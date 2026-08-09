# Tide: germbij degenerate affinity

**Direction (user):** standing auto-mode commission; consult roadmap
item 4 of the degenerate-separable programme.
**Seabed:** laplace, stacked on tide/germbij-degenerate-separable
(PR #86, unmerged at start).
**Started:** 2026-08-09T17:30 local

## Candidates

Proceeding on the deliberation of record (the degenerate scoping
consult, archived in the previous tide's log, staged this tide
explicitly): the even multi-index layer.

1. **`evenMonomial`** (j : iota -> N) w = prod_i (w i)^(2 j i), with
   the general factorization of its unnormalized separable moment
   into 1D even moments (subsumes the one-hot case).
2. **Normalized product form**: gibbsExpectation of evenMonomial =
   product over i of the 1D normalized moments (spectator
   cancellation at every coordinate simultaneously,
   prod_div_distrib per the consult).
3. **Exact exponent affinity**: gibbsExpectation (evenMonomial j) t
   = C(k,a,j) * t^(-sum_i j_i/k_i) with C > 0 — the note's
   normalized affinity l(alpha) = sum_i alpha_i q_i (linear, zero
   intercept), exact for the separable class. Consult's staging
   advice honored: keep the closed form as a product of 1D forms
   first; the single-rpow exponent statement is a separate theorem
   so downstream users are not forced through rpow normalization.

## Numerical check

The j = (1,0)/(0,1) instances were checked numerically in the
previous tide (ten digits); the general-j closed form is the same
1D formula per factor. Additional check to run before the Result:
a mixed multi-index (j = (2,1)) against 2D quadrature.

## Vote

- Claude: 1-3 as one tide. - GPT-5.6 Sol: staged exactly so in the
  archived scoping consult (roadmap item 4, with the
  product-of-closed-forms-first advice). Agreed on record.

## Numerical check (executed)

Mixed multi-index j = (2,1) against L = 1.3 x^4/4! + 0.6 y^6/6! at
t = 40 (scipy quad):

    product of 1D moments = 0.1141638843
    closed power law      = 0.1141638843
    exponent sum j_i/k_i  = 1.333333 (= 2/2 + 1/3)

## Result

Committed on tide/germbij-degenerate-affinity:
`Laplace/Multi/SeparableAffinity.lean` (~190 lines). Theorems: 1D
`evenMoment_smul_kthPotential` (general-j exact power law) and
`evenMoment_coeff_pos`; multivariate `evenMonomial`,
`evenMonomial_integral_separableMonomial` (multi-index
factorization, no DecidableEq needed — the observable is already a
product, unlike the one-hot case),
`gibbsExpectation_evenMonomial_separableMonomial` (normalized
product form via prod_div_distrib, pure field algebra),
`gibbsExpectation_evenMonomial_powerLaw` (the exact exponent
affinity: exponent -sum_i j_i/k_i = -sum_i (2 j_i) q_i, linear in
the multi-index with zero intercept, weights q_i = 1/(2k_i)), and
`evenMonomial_powerLaw_coeff_pos`. Zero sorries, zero warnings.

One compile iteration (a neg_div orientation); otherwise first
build. The consult's advice held: keeping the closed form as a
product of 1D forms and collecting the t-exponent separately
(Real.rpow_sum_of_pos) confined the rpow friction to six lines.
