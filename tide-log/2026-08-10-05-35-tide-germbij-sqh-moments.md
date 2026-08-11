# Tide: germbij class (c) piece (i) — quasi-homogeneous moment ratios

**Direction (user):** "Yes continue with germbij, and do not switch
into another seabed..." (class (c) explicitly ranked less crucial;
this tide follows the archived scoping consult's "best small target"
recommendation after the nondegenerate core completed in both
directions, PRs #93-#111).

**Seabed:** laplace main at 5926dd3. Scoping consult archived as
`tide-log/gpt56_sqh_scoping_v1.md`.

**Started:** 2026-08-10T05:35Z

## Candidates (Claude, following the consult verbatim)

The consult's finding: piece (i) of the semi-quasi-homogeneous debt
(recovery of every M_α from expansion coefficients) needs NO
distribution theory — testing with the monomial observable x^α
itself, anisotropic scaling gives the moment ratio directly, and
exponent collisions never enter a single observable's leading
coefficient.

1. `monomial_integral_scaled_tendsto_moment` (unnormalized, global,
   exact): for positive integer weights a, principal weighted degree
   D, P weighted-homogeneous of degree D with e^{-P} integrable
   against all monomials, the anisotropic substitution
   x_i = h^{a_i} u_i gives EXACTLY
   t^{ℓ(α)} ∫ x^α e^{-tP} = ∫ u^α e^{-P} at t = h^{-D}, with
   ℓ(α) = (Σ a_i(α_i+1))/D — or the h-parametrized integer-power
   form. Build on Laplace.Multi.AnisotropicScaling
   (scalesMeasure_normalized_law) + DiagonalVolume + the even-moment
   specializations in SeparableAffinity/SeparableRecovery.
2. `normalized_monomial_scaled_tendsto_momentRatio`: the normalized
   form t^{weightedDegree a α/D}·⟨x^α⟩_t → M_α/M_0 (exact constant
   for the global model; Tendsto form for uniformity with the local
   statement later). ALL multi-indices including odd — extends the
   existing even-coordinate recovery perimeter.
3. Packaging: `momentRatios_eq_of_normalized_expansions` — two
   quasi-homogeneous models with matching normalized monomial
   families have equal moment ratios M_α/M_0.

Endpoint per the consult: stop short of the analytic-germ theorem;
the one-grade comparison (piece iii) is a separate later tide;
the coarea/Gelfand-Leray layer (piece ii) stays open (Mathlib GMT).

## GPT-5.6 Sol

The scoping consult (archived) IS the deliberation: it answered the
correctness, minimality, and better-candidates questions and
recommended exactly this target ("Best small target").

## Vote

- Claude: candidate chain 1→2→3 (one tide).
- GPT-5.6 Sol: same (the consult's "best small target").

## Numerical check

To execute before writing Lean: P = x⁴ + y⁶ (weights a = (3, 2),
D = 12), α = (2, 2). Check t^{(3·2+2·2+3+2)/12}... precisely:
unnormalized ∫ x²y² e^{-tP} scales as t^{-(3(2+1)+2(2+1))/12}
= t^{-15/12}; normalized ⟨x²y²⟩_t · t^{(3·2+2·2)/12} = t^{10/12}⟨·⟩
→ M_(2,2)/M_0. Verify at t ∈ {10, 100, 1000} by numerical
integration.

## Result

`Laplace/Multi/QhMomentRecovery.lean` (~130 lines), all gates green
on the first substantive build (one unused-binder pass):

- `mvMonomial` + measurability, `rpow_sum_of_pos`,
  `mvMonomial_qhDilation` (homogeneity with weight ⟨q,α⟩).
- `qh_monomial_moment_law` / `qh_monomial_normalized_law` (exact,
  instantiating the abstract ScalesMeasure laws at
  scalesMeasure_qhDilation_volume).
- `qh_momentRatio_recovery`: t^{⟨q,α⟩}·⟨x^α⟩_t = M_α/M_0 exactly at
  every t > 0, every multi-index including odd — piece (i) of the
  semi-quasi-homogeneous debt, distribution-free.
- `momentRatios_eq_of_normalized_moments_eq`: the comparison form at
  a single temperature.

Numerical check (executed before the Lean): P = x⁴+y⁶, weights
(3,2)/12, α = (2,2) — the rescaled normalized moment equals
M_α/M_0 = 0.107624 exactly at t ∈ {10, 100, 1000}.

### Suggested follow-ups

- Piece (iii) one-grade comparison (the consult's "best reusable
  recovery target"): tendsto_normalizedIntegral_difference_div_pow +
  polynomial_eq_zero_of_covariance_monomials +
  weightedGrade_eq_of_moment_rates, restricted to finite polynomial
  corrections. Medium delta; the consult's stage plan is archived.
- The consult's recommended ENDPOINT for class (c): stop after the
  one-grade theorem; the coarea/Gelfand-Leray layer stays open
  (Mathlib GMT) and the full analytic weighted induction is not
  tide-shaped.
