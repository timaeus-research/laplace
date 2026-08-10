# Tide: germbij class (c) piece (iii) stage B (one-grade difference limit)

**Direction (user):** "Yes continue with germbij, and do not switch
into another seabed..." (class (c) less crucial; following the
archived scoping consult `tide-log/gpt56_sqh_scoping_v1.md`, this is
its "best reusable recovery target", stage B).

**Seabed:** laplace, branch tide/germbij-sqh-moments at 60f6f4c
(stacked; the moments tide in PR #113).

**Started:** 2026-08-10T06:10Z

## Candidate

`Laplace/Multi/GradeComparison.lean`: the pairwise one-grade
difference limit for perturbed Gibbs families with a COMMON reference
density e^{-P} (general positive P, no Gaussian structure):

1. Pointwise engine: for W → 0 with W/h^ρ → Q,
   (e^{-W} - 1)/h^ρ → -Q, via the second-order bound
   |e^{-W} - 1 + W| ≤ W²e^{|W|} (squeeze; no division by W, so the
   W = 0 fibers are painless), then e^{-V₁}·(...) with V₁ → 0.
2. `tendsto_integral_exp_difference_div_pow` (unnormalized): with an
   explicit eventual integrable majorant hypothesis for the
   normalized difference quotient, DCT gives
   (∫A e^{-(P+V₂ h)} - ∫A e^{-(P+V₁ h)})/h^ρ → -∫ A·Q·e^{-P}.
3. `covarianceUnder P A Q := E_P[AQ] - E_P[A]E_P[Q]` (normalized
   expectations under e^{-P}).
4. `tendsto_normalized_difference_div_pow`: via the quotient-rate
   identity (mirror of NormalizedRate's div_sub_div_rate), the
   normalized moments satisfy
   (M₂(h) - M₁(h))/h^ρ → -Cov_P(A, Q), assuming Z_P > 0 and the
   two majorant hypotheses (observable and constant-1 instances).

Stages C (covariance injectivity for polynomial corrections) and D
(weightedGrade_eq_of_moment_rates + finite induction) are the
FOLLOW-UP tide; per the consult they are the endpoint of class (c).

## GPT-5.6 Sol

The archived scoping consult is the deliberation (its stage B
signatures are followed with the majorant abstraction made an
explicit hypothesis rather than a new predicate).

## Vote

- Claude: the four-piece stage B file.
- GPT-5.6 Sol: same (consult section 1, stage B).

## Numerical check

Feasible; execute before Lean: P = x⁴ (1D), V_i h = h^ρ·c_i·x⁶ with
ρ = 2, c₁ = 0.3, c₂ = 1.0 (so Q = 0.7 x⁶), A = x². Check
(⟨A⟩_{P+V₂} - ⟨A⟩_{P+V₁})/h² → -0.7·Cov_P(x², x⁶) as h → 0.

## Result

`Laplace/Multi/GradeComparison.lean` (~290 lines), all gates green
(three small fix rounds):

- `expectationUnder` / `covarianceUnder` (the non-Gaussian covariance
  API against an arbitrary reference density).
- `tendsto_exp_neg_sub_one_div_pow` (the pointwise engine: the
  second-order bound |e^{-W}-1+W| ≤ W² squeezes without dividing by
  W, so W = 0 fibers are painless).
- `tendsto_pointwise_difference_div_pow` (the factored integrand
  limit), `tendsto_integral_exp_difference_div_pow` (the unnormalized
  DCT), and `tendsto_normalized_difference_div_pow`:
  (M₂(h) - M₁(h))/h^ρ → -Cov_P(A, Q) with explicit majorant /
  integrability / base-convergence hypotheses, assembled through the
  quotient-rate identity (field_simp + ring under three eventual
  nonvanishing facts).

Surprises: two exp_add rewrites suffice (the second rewrites both
identical instances at once); integral_div wanted the FORWARD
direction (the ← pattern (∫f)/r is not present when the target has a
difference of integrals over the division).

### Suggested follow-ups

- Stage C+D (the consult's endpoint for class (c)): covariance
  injectivity for polynomial corrections against a positive
  full-support density (polynomial_eq_zero_of_covariance_monomials)
  and weightedGrade_eq_of_moment_rates + the finite induction,
  consuming this tide's normalized limit.
