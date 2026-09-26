# Round 59: after the entropy-gap topology — what remains for maximum beauty and depth? (germbij / laplace)

Same programme (bounded features `S`, featureless posterior `ν`, family `P_θ`, reconstruction `Π(M) = P_{θ(M)}`,
direction subspace `𝕍`, atlas `M_s`, response scores `ℓ_{M,u}`, `R_M = Dθ(M)`, normal projection `N_M`, regression
`B_M`, third-cumulant operator `T_θ`). User direction unchanged: "map the space of responses across the data manifold,
from the featureless distribution of maximal entropy to the actual data distribution, with maximum beauty and depth."

## Landed since round 58 (all sorry-free on `main`; slop paragraphs pushed)

Your landing order was: (1) named observable Taylor + atlas-curve corollaries, (2) higher moment-normality,
(3) analytic inverse audit / route (a), (4) boundary dual representation + entropy-gap TV stability, (5) empirical TV
consistency + observable stochastic response, (6) matched-velocity dual-curve comparison. Status:

- (1) `ObservableTaylorUniform`: `E_{Π(M+z)}F = E_QF + E_Q[Fℓ_z] + ½E_Q[FN(ℓ_z²)] + o(‖z‖²)B_F` uniformly on
  compact convex interior sets. (Atlas-curve second-order expansion not separately stated; it is the `z = hΔ` case.)
- (4) `EntropyGapStability`: NB the boundary dual representation `𝓘 = sup_θ(−⟨θ,M⟩ − log Z)` is the seabed's
  DEFINITION of `genRate`, and the entropy-minimisation value equals it by `responseProjection_spec`; so 4.1 was free.
  Landed: `lowerSemicontinuous_genRate`; the entropy-gap inequality in the bounded-test form
  `ab(E_{Π(A)}F − E_{Π(B)}F)²/(2L²) + 𝓘(aA+bB) ≤ a𝓘(A) + b𝓘(B)` (from the seabed's mixture compensation identity
  `genRate_mixture_gap` + `pinsker_observable`); the non-radial stability theorem for any filter:
  `M_i → M_*`, `𝓘(M_i) → 𝓘(M_*) < ∞` ⇒ `E_{Π(M_i)}F → E_{Π(M_*)}F` for bounded `F`.
  `SegmentStability`: convexity of `𝓘` between any two finite-rate responses, `𝓘((1−t)A+tB) → 𝓘(B)` as `t ↑ 1`,
  and continuity of the reconstruction along every such segment (boundary endpoints included).
- (5) `EmpiricalTotalVariation`: compact convex interior neighbourhoods; `∫|q_{M̂_n} − q_{M_D}| → 0` a.s.;
  `E_{Π(M̂_n)}φ → E_{Π(M_D)}φ` a.s. The delta method is OUT OF REACH: Mathlib (this pin) has NO central limit theorem.
- (6) `DualCurveComparison`: mixture curve `Π(M+tu)` and exponential curve `P_{θ+tRu}` to second order
  (relative-uniform; `o(t²)` and explicit `O(t³)`), `N(ℓ²) − (ℓ² − Eℓ²) = −B(ℓ²)`, pairing with the velocity
  `= −E_Qℓ³` (`dual_curve_comparison`).
- (2)/(3) NOT done. Mathlib audit: no Banach-space analytic inverse function theorem (only the 1-D
  `analyticAt_localInverse` with `deriv ≠ 0`); `analyticAt_exp_of_mem_ball` exists for Banach algebras; `AnalyticAt.inv`
  exists; the SMOOTH inverse function theorem `ContDiffAt.to_localInverse` exists; `contDiff_succ_iff_fderiv` /
  `contDiff_infty_iff_fderiv` exist; `contDiffAt_ringInverse` exists. The seabed has first derivatives of
  `θ ↦ ∫ φ dP_θ` (`hasFDerivAt_integral_family`, derivative `covCLM`, itself of the same form with `φ` replaced by
  `φ·S_j`), so `C^∞` of the family responses by induction is plausible (~150–300 lines), then `meanMap`,
  `chartDeriv` `C^∞`, `θ = (relintChart)⁻¹` `C^∞` via the smooth IFT (local inverse = global inverse on a
  neighbourhood), then `q_M(x)` `C^∞` in `M` pointwise, and moment-normality at all orders by differentiating
  `∫ q_{M+z} dν = 1`, `∫ S q_{M+z} dν = M + z` — the last step needs exchange of `n`-th derivatives and integrals
  (dominated, bounded features) and is the expensive part.

## Questions

1. Given "no CLT" and "no Banach analytic IFT" in Mathlib, re-rank what is now deepest and reachable. Is the `C^∞`
   route to all-orders moment-normality worth its cost (rough total 800–1500 lines?), or is there a cheaper
   formulation of "every response of order ≥ 2 is moment-normal" — e.g. at the level of the coefficient
   functionals `A_n[u₁,…,u_n] = ∂ⁿ_{u₁…u_n}(q_{M+z}/q_M)|₀` defined via iterated directional derivatives along a
   FIXED line `t ↦ q_{M+tu}` (one-variable `iteratedDeriv`), where `∫ q_{M+tu} = 1` and `∫ S q_{M+tu} = M + tu`
   are polynomial in `t`, so all `t`-derivatives of order ≥ 2 of the integrals vanish — needing only
   `iteratedDeriv` under the integral sign along one line (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   iterated), which the seabed's density derivative formulas support (`q'_t = q_t ℓ_t`, `q''_t = q_t(ℓ² − κ + ⟨w,S−M⟩)`
   along the atlas)? What is the cleanest statement: "for every `n ≥ 2` and direction `u`, the `n`-th
   `t`-derivative of `q_{M+tu}` at `0` is `q_M · A_n(u)` with `E_Q A_n = 0` and `E_Q[S A_n] = 0`", together with the
   recursion `A_{n+1} = A_n' + A_n ℓ`-type formula? Give the precise recursion for the line coefficients in terms of
   `ℓ_t`, `κ_t`, `w_t` (the seabed's atlas objects) and the cost.
2. Are there statements about the GLOBAL structure of the map still missing that you would now rank above
   all-orders? Candidates: (i) the reconstruction as a `C¹` (or `C²`) map between the response body and the
   `L¹`-ball with the explicit derivative and the retraction property stated as a differential identity
   `DΠ_{E_Q S}[u] ∘ (moment map) = projection`; (ii) the "invisible information is monotone under feature refinement"
   tower (`AtlasRefinement` has `𝓘_f − 𝓘_c = KL(P_f‖P_c)`); (iii) the entropy-gap inequality as a modulus of
   continuity for the map `M ↦ Π(M)` on the whole finite-rate domain (`L¹` distance ≤ 2√(2·gap)`) and its
   interpretation as "the reconstruction is continuous on the finite-rate domain for the topology of `(M, 𝓘(M))`" —
   is that the final form of the "map across the data manifold", and should we state it as the theorem of the note?
   (iv) the conditional variational / residual split as the fibre part of the map; (v) anything from the
   Legendre side: `𝓘` is the convex l.s.c. envelope, its subdifferential at boundary points, the recession
   directions (we have `NormalCone`, `BoundaryEscape`).
3. For your top two: precise statements in the seabed's terms, lemma-level sketches, line estimates, pitfalls.
