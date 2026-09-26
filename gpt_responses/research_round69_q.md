# Research round 69: after the analytic atlas and the finite face completion — what remains for depth?

## Landed since round 68 (laplace `Laplace/Multi/*`, sorry-free, pushed; all NOT mirrored)
Your round-68 route worked verbatim, in five modules:
- **FiniteEntropySupport**: probability vectors ↔ measures on finite `X` (`vecMeasure`, `vecMoment`, `integral_vecMeasure`);
  every measure is `≪` a full-support `ν` with finite `klDiv`; responses of probability vectors = the polytope
  `C = conv S(X)`; **every point of `C` has finite rate**; **maximal support** `r` feasible at `M`, `r{x} > 0 ⇒ q*(M){x} > 0`
  (from Pythagoras `KL(r‖ν) = KL(r‖q*) + 𝓘 < ∞ ⇒ r ≪ q*`); `qStarVec M x = q*(M){x}`.
- **FiniteCompletionContinuity**: `entVec ν p = Σ p log(p/ν)` continuous; bridge `(klDiv (vecMeasure p) ν).toReal = entVec`
  (rnDeriv of `count.withDensity`); `q*` minimises `entVec` over its fibre and is the unique minimiser; **additive recovery**
  `p + a_n − r ∈ Δ` eventually when `supp r ⊆ supp p`; **limits of minimisers are minimisers**; `tendsto_qStarVec`,
  **`continuousOn_qStarVec`** (continuity on `C`), `continuousOn_genRate_toReal`.
- **FiniteMinimalFace**: absorption `q*(M) = ε b + (1−ε) z` for `b` carried by `supp q*(M)`; `support_absorb`;
  `carriedResponses (supp q*(M))` is a face, contained in every face containing `M`, hence **the minimal face**
  (`minimalFace_eq`); **Csiszár: `q*(M) x > 0 ↔ S(x) ∈ minimalFace M`**.
- **FiniteCompletionRetraction**: `completedFamily = q*(C)` compact, **homeomorphic to `C`** (`completedHomeomorph`);
  `retract p = q*(E_p S)` continuous, moment-preserving, idempotent, fixed-point set = completed family;
  **strong deformation retraction** `H_t p = (1−t)p + t·retract p` (continuous, moment-preserving, `retract ∘ H_t = retract`).
- **FiniteCompletionClosure**: essential range = feature set, **moment body = `C`**, on the relative interior `q* = Q_θ`,
  **`closure (interior exponential family) = completedFamily`** (density along atlas rays).
Earlier this session: AnalyticTilt/AnalyticChart (analytic response atlas, grade-ω inversion), PointwiseJets (`p^{(k)} = [∂_s^k q_s]`
for all `k`, Bell tower `B_{k+1} = ∂B_k + ℓB_k`), ThirdJet, QuantitativeJets, CubicRemainder.

## What the whole session has built (for the user's direction "map the space of responses across the data manifold, from the
featureless distribution to the data distribution, with maximum beauty and depth")
Interior: `M ↦ [q_M] ∈ L¹` real-analytic on interior displacements; jets `p^{(k)}(s) = [q_s N_s(B_k)]` with `B_1 = ℓ`, `B_2 = ℓ²+ℓ'`,
`B_3 = ℓ³ − 3ℓr` after projection; explicit `‖p^{(k)}‖₁` bounds and the sharp cubic remainder; smooth global normal form of the
data space `U ≃ Ω × K`; the invisible tower. Boundary (finite `X`): the completed family is continuous on the closed polytope,
Csiszár support, homeomorphic to the polytope, a strong deformation retract of the simplex, the closure of the interior family.

## Questions
1. **Re-rank the remaining candidates** for the direction, with precise statements and seabed routes for the top two:
   (a) the explicit natural-parameter radius (your round-67 rank 3: `q_{a+h} = q_a e^{−⟨h,T⟩}/E e^{−⟨h,T⟩}`, coefficient
       majorant `e^{Lt}/(2 − e^{Lt})`, radius `ρ = log(3/2)/L`, `Σ‖A_n‖ρ^n ≤ 3`, remainder `3(t/ρ)^{N+1}`) — now that the qualitative
       analytic atlas exists, is a *series-free* version reachable (e.g. `‖p^{(k)}(s)‖₁ ≤ C k! ρ^{−k}` from the Bell tower, hence
       an explicit Taylor radius along the atlas)? What is the cleanest explicit statement in Lean terms?
   (b) **general-`X` face completion**: which parts of the finite proof survive for a general probability space with bounded
       features? (Maximal support = absolute continuity `r ≪ q*(M)` holds verbatim. The additive recovery used the finite
       simplex. Is `M ↦ q*(M)` continuous in total variation on the whole moment body for general `ν`? If not in general,
       under which hypothesis — e.g. all faces of positive mass / "polytopal" essential range — and by which route?)
   (c) the reconstruction CLT `√n([q_{M̂_n}] − [q_M]) ⇒ [q_M ℓ_{M,Z}]` in `L¹` (delta method through `Dp_M`; Mathlib has the
       multivariate CLT? we believe only the real CLT `ProbabilityTheory.central_limit`-type statements exist — please advise);
   (d) a **capstone package theorem** "the response atlas of the data manifold": one Lean statement collecting the smooth
       normal form, analyticity, the jets/invisible tower, and (finite `X`) the deformation retraction — is there a single
       beautiful formulation (e.g. a `structure ResponseAtlas` with fields) worth writing, or is that process rather than math?
   (e) something we are missing: the deformation retraction `H_t` vs the natural-gradient flow (`NaturalGradientAtlas`:
       `M(τ) = m₀ + (1 − e^{−τ})(M* − m₀)`); an intrinsic/coordinate-free third jet; a Hessian-of-the-rate = Fisher identity
       on the boundary faces; the "conditional walls" of `ExposedFace` as the face lattice of the completed family; a
       *quantitative* version of face completion (rate of TV-convergence to the boundary along the ray, e.g. from
       `KL(Q_*‖Q_s) = ∫_s^1 (1−u)κ_u du` + Pinsker).
2. For your top candidate, give the lemma chain and flag the single hardest lemma; for the second, the minimal first module.
Answer in ≤ 3000 words.
