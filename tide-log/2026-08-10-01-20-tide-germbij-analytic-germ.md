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

## Result

Committed on tide/germbij-analytic-germ:
`Laplace/Multi/AnalyticGermRecovery.lean` (~125 lines). Theorems:
`hasFPowerSeries_diag_eq` (power-series diagonals from iterated
derivatives: the permutation sum collapses to n! copies on a
constant vector — iteratedFDeriv_eq_sum_of_completeSpace +
Fintype.card_perm), `analytic_germ_eq_of_jet_eq` (equal positive-
order jets + analyticity give equal germs modulo the constant, by
the HasSum-difference argument: termwise difference vanishes above
order zero, hasSum_single, uniqueness of sums), and the composition
`analytic_germ_recovery_of_superPoly_moments` — germbij Corollary
3.2's inverse direction in the note's own data language. Zero
sorries, zero warnings. WITH THIS, THE INVERSE HALF OF THEOREM 3.1
IS COMPLETE (audit items B + D + C): superpolynomially-equal
localized moment families determine the location, the full
positive-order jet, and (for analytic losses) the germ modulo the
additive constant. The remaining substantive half is programme A
(the forward direction).

Iterations: two — the beta-reduced permutation sum needed the
reduced statement form, and Fintype.card_perm leaves
Fintype.card (Fin n) needing card_fin.
