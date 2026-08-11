# Tide: germbij-leading-corollary

**Direction (user):** continue the germbij arc (auto mode): the multivariate
composed corollary, assembling `leading_part_scaled_set` with
`pencil_difference_lower_bound_multi`, constants first then all t >= T0,
per-t integrability premises. The d-dimensional analogue of the 1D analytic
corollary; makes the two chains structurally parallel.

**Seabed:** laplace, chained off tide/germbij-leading-part (PR #29 pending).
**Started:** 2026-08-09T05:05Z
**Worktree/branch:** laplace-tide-germbij-leading-corollary /
tide/germbij-leading-corollary (base 7088d6b, verified)

## Deliberation (carried over)

The composition mirrors the 1D analytic corollary tide, whose deliberation
("B should be a short subsequent composition once A is stable") covers the
pattern; the multivariate ingredients were each deliberated in their own
tides. New bookkeeping is limited to the scale threshold: T0 :=
max (4/R^2) (u0^{-2}) makes both the window condition 4 <= R^2 t and the
leading-part scale condition (sqrt t)^{-1} <= u0 hold for t >= T0. The
packaged constant is kappa := vol(S).toReal * c^2 * exp(-(4 C0)), positive
by ENNReal.toReal_pos. No fresh consult.

## Numerical check

Not feasible (existential constants); underlying inequality checked in the
identifiability-multi tide (margin ~8e6). Shape check: with L2 - L1 = P =
(w1 w2)^2 exactly (C = 0 remainder), m = 4, the instantiation gives some
ball S around (3/2, 3/2) and the corollary's exponent t^{1 - 4 - 1}
matches the earlier composite check.

## Result

`Laplace/Multi/LeadingIdentifiability.lean`, registered in `Laplace.lean`.
Declaration, sorry-free, zero warnings:
- `Laplace.leading_part_pencil_difference_lower_bound`: from Taylor
  structure of the difference (continuous homogeneous P of degree m,
  nonzero at norm 3/2, remainder O(||x||^{m+1})), nonnegativity, and
  quadratic domination on the ball of radius R, there are kappa > 0 and
  T0 = max(4/R^2, u0^{-2}) such that for all t >= T0 (per-t integrability
  premises), kappa * t * t^(-(m:R) - d/2) <= Delta_t((L2 - L1) psi).

One compile iteration: `inv_le_inv_of_le` no longer exists; the stable
route is `inv_le_comm₀` (a <-> flip inequality with inverses), plus
`Real.sqrt_sq` / `Real.sqrt_le_sqrt` for the scale threshold. Full
`lake build` passes on rebased main (8bfec0e, containing PR #29);
`scripts/sorries` 0/0/0/0.

The 1D and multivariate germbij chains are now structurally parallel:
analyticity / Taylor structure -> growth bound on a window / scaled set ->
sector bound -> composite -> composed corollary.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-09-05-05-tide-germbij-leading-corollary.tex
