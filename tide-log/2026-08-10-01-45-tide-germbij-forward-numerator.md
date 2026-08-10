# Tide: germbij forward programme stage 5c-ii (numerator expansion)

**Direction (user):** "Yes continue with germbij, and do not switch into
another seabed... the main core concern being the recovery of all
coefficients in the nondegenerate case and the main theorem in the
nondegenerate case."

**Seabed:** laplace, branch tide/germbij-forward-majorant at 087e769
(stacked; stage 5c-i in PR #103). Architecture consult archived as
`tide-log/gpt56_stage5_shape_v1.md`; this tide is its items 7-9.

**Started:** 2026-08-10T01:45Z

## Candidate

`numerator_hasExpansion`: for continuous observables of polynomial
growth, the rescaled numerator `∫ z, D.integrand P q z` is an order-N
asymptotic polynomial at 0⁺ with coefficients
`a_j = ∫ z, P z · e^{-T₂(z)} · P_j(z)`.

Pieces:
1. `boltzmann_factor_eq` (extraction of the majorant tide's factoring
   as a standalone lemma).
2. `numeratorCoeff` + `integrable_coeff_integrand` (domination by
   `(1+‖z‖)^{n+j+2N} e^{-(λ/2)‖z‖²}`).
3. `tendsto_integral_window_remainder`: the filter-indexed DCT with
   the window indicator folded in; dominator = the 5c-i majorant ×
   observable growth; pointwise limit from exp_graded_expansion +
   tendsto_scaledRem + eventually_mem_mesoscopicSet.
4. The two outer tails: the true integrand via
   integrand_meso_tail_isLittleO; the coefficient polynomial via
   gaussian_meso_tail_isLittleO (binomial split of (1+‖z‖)-powers).
5. The decomposition identity (eventually in q) and the o-sum
   assembly into `Laplace.IsAsymptoticExpansionTo`.

## Numerical check

The full expansion was checked numerically in the stage-4 tide at the
scalar level; the integrated statement's coefficients are integrals
of the checked coefficients against the Gaussian, and no closed form
is pinned here (existence-form statement per the programme's API).

## Scope adjustment

Cut at the window convergence: items 1-3 of the candidate list ship in
this tide (renamed 5c-ii-a); the two outer tails, the decomposition
identity, and numerator_hasExpansion move to the follow-up tide
(5c-ii-b). The tails are another full tide of set-integral
comparisons; a clean cut beats a half-done state.

## Result

`Laplace/Multi/NumeratorExpansion.lean` (~250 lines), all gates green:

- `boltzmann_factor_eq` (the exponent-split factoring, standalone).
- `numeratorCoeff` (the expansion's coefficient integrals) +
  `integrable_coeff_integrand` (domination by
  (1+‖z‖)^{n+j+2N} e^{-(λ/2)‖z‖²}).
- `tendsto_integral_window_remainder`: the filter-indexed DCT with
  the window indicator folded into the integrand
  (MeasureTheory.tendsto_integral_filter_of_dominated_convergence),
  5c-i's majorant × observable growth as dominator, pointwise limit
  from exp_graded_expansion + tendsto_scaledRem +
  eventually_mem_mesoscopicSet via boltzmann_factor_eq.

Surprises: `rw` of `0 = ∫ 0` rewrote the zero inside `𝓝[>] (0:ℝ)`
too (state the DCT conclusion with `∫ 0` and `simpa` instead of
rewriting the target); positivity cannot see `0 < D.lambda / 4`
(opaque field — `by linarith [D.lambda_pos]`).

### Suggested follow-ups

- Stage 5c-ii-b (next): the two outer tails
  (observable-weighted integrand_meso_tail via binomial split;
  coefficient-polynomial tail via gaussian_meso_tail), the eventual
  decomposition identity, and numerator_hasExpansion.
