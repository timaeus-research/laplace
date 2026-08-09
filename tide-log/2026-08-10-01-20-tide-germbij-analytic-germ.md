# Tide: germbij analytic germ corollary (nondegenerate core, item C)

**Direction (user):** the nondegenerate core; audit consult item C
(deliberation of record in the expansion-bridge tide log).
**Seabed:** laplace, stacked on tide/germbij-location (PR #94,
unmerged at start).
**Started:** 2026-08-10T01:20 local

## Candidates

Mathlib has no derivative-based identity theorem directly (the
Uniqueness file works from eventual equality); the route is the
diagonal reconstruction:

1. `hasFPowerSeries_diag_eq`: for a function with a power series on
   a ball at 0, the diagonal of p_n is (n!)^-1 times the diagonal of
   the n-th iterated derivative (iteratedFDeriv_eq_sum_of_completeSpace
   with the constant vector: all permutations act trivially on a
   diagonal, so the sum is n! copies).
2. `analytic_germ_eq_of_jet_eq`: two functions analytic at 0 with
   equal iterated derivatives at all positive orders agree modulo
   the constant near 0 (HasSum difference: the termwise difference
   vanishes for n >= 1 and is f0 - g0 at n = 0; hasSum_single +
   uniqueness).
3. **Corollary 3.2 composed**: superPoly-matched monomial moment
   families + analyticity at 0 give equal germs modulo the constant
   (compose 2 with smooth_jet_recovery_of_superPoly_moments).

## Vote

- Claude: 1-3 as one tide. - GPT-5.6 Sol: item C per the archived
  audit consult ("completes the analytic corollary once inverse jet
  recovery is available"). Agreed on record.

## Numerical check

Not feasible: structural (power-series manipulation).
