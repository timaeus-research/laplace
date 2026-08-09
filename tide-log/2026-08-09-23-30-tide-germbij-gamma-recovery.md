# Tide: germbij-gamma-recovery (stage 6, the gamma-rung finale)

**Direction (user):** gamma-rung programme stage 6: the recovery
corollary. Eventual agreement of the mean-susceptibility,
covariance-susceptibility, and fourth-cumulant data streams for two
anharmonic triples forces lambda, alpha, AND gamma equal — the complete
jet recovery of germbij Theorem 3.1's anharmonic instance.

**Seabed:** laplace, chained on tide/germbij-gamma-kappa4 (stages 4-5,
PR #48 in flight). Consumes anharmonic_susceptibility_recovery (the
lambda-alpha rungs, merged as tide 21) and kappa4_anharmonic_asymptotic.
**Worktree/branch:** laplace-tide-germbij-gamma-recovery /
tide/germbij-gamma-recovery
**Started:** 2026-08-09T23:30Z

## Deliberation (programme-inherited)

The scoping consult's endpoint: gamma = -lam^4 L + 3 alpha^2/lam where
L is the observed kappa4 limit. Lean shape: compose the merged two-rung
recovery with tendsto_nhds_unique on the kappa4 limits (the thread's
most-practiced pattern, used four times). Extraction:
3a^2/l^5 - g1/l^4 = 3a^2/l^5 - g2/l^4 forces g1 = g2 by field algebra
with l^4 != 0.

## Numerical check

Tautological given the pinned kappa4 limit (recovery = uniqueness of
limits); the programme target's numerics are archived in the stage-1
log.

## Result

- Branch tide/germbij-gamma-recovery,
  Laplace/OneD/RecoveryAnharmonicFull.lean: kappa4Data (the observed
  fourth-cumulant combination) and anharmonic_jet_recovery — eventual
  agreement of the three data streams forces lambda, alpha, gamma all
  equal.
- FIRST-ATTEMPT CLEAN BUILD: the composition of the merged two-rung
  recovery with tendsto_nhds_unique on the kappa4 limits compiled
  without a single iteration. The uniqueness-of-limits pattern's fifth
  use; the programme's six stages close with its cheapest tide.

## Vote

Programme-inherited (the scoping consult's stated endpoint).
