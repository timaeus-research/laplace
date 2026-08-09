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
