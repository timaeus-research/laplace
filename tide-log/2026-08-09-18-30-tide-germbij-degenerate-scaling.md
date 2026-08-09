# Tide: germbij abstract anisotropic scaling

**Direction (user):** standing auto-mode commission; degenerate
roadmap item 5, the genuinely non-separable step.
**Seabed:** laplace, main at 31dd5a6 (post-affinity).
**Started:** 2026-08-09T18:30 local

## Candidates + consult

Shape consult fired before the tide opened; archived verbatim in
`tide-log/gpt56_scaling_shape_v1.md`. Its rulings, all adopted:

1. Statement shape (ii)+: take the geometric input as a PUSHFORWARD
   hypothesis `ScalesMeasure delta Q mu` (map (delta s) mu =
   ofReal (s^(-Q)) • mu for s > 0), NOT an integral identity and NOT
   the concrete determinant computation — "the main theorem is then
   independent of pi types, determinants, and Lebesgue measure".
2. No Integrable hypotheses anywhere: integral_map respects the
   junk-value convention (an invertible substitution preserves
   non-integrability, both sides are 0). Measurability hypotheses
   only.
3. Normalized law needs no positivity (field division is total; the
   0 case degenerates coherently); positivity enters only the
   recovery consumer, as M_i(1) > 0 hypotheses (quasi-homogeneity
   alone cannot supply it).
4. Recovery consumer: exact law M_i(t) = M_i(1) t^(-2 q_i) +
   eventual_power_eq per coordinate; recovers ONLY the weights (the
   honest scope: mixed potentials share weights).
5. The concrete pi-volume diagonal pushforward
   (map_linearMap_volume_pi + Matrix.det_diagonal, "the most
   brittle piece of Mathlib determinant plumbing") is deferred to a
   separate infrastructure tide.

## Vote

- Claude: as staged (abstract layer this tide, concrete instance
  next). - GPT-5.6 Sol: same (the consult IS the staging). Agreed.

## Numerical check

The abstract law instantiated on P = x^4 + x^2 y^2 + y^4
(q = (1/4, 1/4), non-separable): to run before the Result — check
M_{2e1}(t) = t^(-1/2) M_{2e1}(1) at t = 30 by 2D quadrature.

## Numerical check (executed)

Non-separable P = x^4 + x^2 y^2 + y^4 (weights q = (1/4, 1/4)), 2D
quadrature:

    M(1)  = 0.3035226138
    M(30) = 0.0554153941
    t^(-1/2) M(1) at t=30 = 0.0554153941
    ratio M(30)/(30^-0.5 M(1)) = 1.0000000000

The exact law M(t) = t^(-2 q_1) M(1) holds to ten digits on a
potential whose integrals do not factor.

## Result

Committed on tide/germbij-degenerate-scaling:
`Laplace/Multi/AnisotropicScaling.lean` (~230 lines). Theorems:
`ScalesMeasure` (the one-parameter pushforward interface),
`scalesMeasure_moment_law` (exact unnormalized law t^(-(Q+r)), no
integrability hypotheses — integral_map + the junk-value convention,
per the consult), `scalesMeasure_normalized_law` (t^(-r), no
positivity — field division degenerates coherently), `qhDilation` +
measurability + coordinate-square homogeneity, and
`weights_eq_of_coordSq_moments_eq`: two quasi-homogeneous potentials
(arbitrary mixed terms) with scaling dilations, matched coordinate
second moments on a ray, and one side's moment positivity have equal
anisotropic weights. Zero sorries, zero warnings.

Surprises: the linter forced statement hygiene — hq positivity,
the second potential's moment positivity, and 0 < T all turned out
UNUSED (exponent equality needs only one positive coefficient and
eventual_power_eq's internal max), so the merged statement is
strictly stronger than the consult's draft. Real.rpow_neg_one does
not exist for real base (only NNReal/ENNReal) — hit twice before;
now catalogued. The deferred piece: the concrete pi-volume diagonal
pushforward instance (determinant plumbing), next tide.
