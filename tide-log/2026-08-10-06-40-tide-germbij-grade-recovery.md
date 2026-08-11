# Tide: germbij class (c) stages C+D (grade recovery — the endpoint)

**Direction (user):** "Yes continue with germbij, and do not switch
into another seabed..." (class (c) less crucial; this tide reaches
the archived scoping consult's designated ENDPOINT for the class).

**Seabed:** laplace, branch tide/germbij-grade-compare at ea2e764
(stacked; stage B in PR #114). Consult archived as
`tide-log/gpt56_sqh_scoping_v1.md` (in the sqh-moments tide, merged).

**Started:** 2026-08-10T06:40Z

## Candidates

`Laplace/Multi/GradeRecovery.lean`:

1. `mvMonomial_continuous`; expectation/covariance bilinearity over
   finite monomial combinations (per-term integrability hypotheses;
   the derived integrabilities of the combo come from per-PAIR
   integrability, avoiding double sums by factoring through
   m_α·Q_c·e).
2. Stage C, `eq_zero_of_covariance_self_zero`: for continuous Q with
   Cov_P(Q,Q) = 0 and Q(0) = 0, Q ≡ 0 — the L² argument
   (∫(Q-m)²e^{-P} = Z·Cov = 0, integral_eq_zero_iff_of_nonneg,
   a.e.-to-everywhere via Continuous.ae_eq_iff_eq on the
   open-positive volume, constant killed at 0), and
   `monomialCombo_eq_zero_of_covariance_monomials_zero` (nonzero
   multi-indices give Q(0) = 0).
3. Stage D, `grade_eq_of_normalized_rates`: if for every monomial in
   the support the normalized difference quotients tend BOTH to
   -Cov_P(m_α, Q_c) (stage B's conclusion, discharged by callers
   under its hypothesis package) and to 0 (the matching-rates
   assumption), then by uniqueness of limits every covariance
   vanishes and the grade difference Q_c is identically zero.

Per the consult, this is the sensible endpoint for class (c): the
principal-model moment ratios are recoverable (PR #113), and
conditional on a common principal part each finite weighted
correction grade is recoverable from normalized moment rates. The
coarea/Gelfand-Leray layer stays open (Mathlib GMT); the full
weighted-analytic induction is a programme, not a tide.

## GPT-5.6 Sol

The archived scoping consult is the deliberation (stages C and D
followed with the noted hypothesis-placement adjustment: stage B's
conclusion is taken as the interface hypothesis in D).

## Vote

- Claude: the three-piece file above.
- GPT-5.6 Sol: same (consult stages C, D).

## Numerical check

Structural statements (injectivity, uniqueness-of-limits
composition); the analytic content was checked numerically in the
stage B tide. Not feasible beyond that: no closed form is pinned.

## Result

`Laplace/Multi/GradeRecovery.lean` (~280 lines), all gates green
(two small fix rounds). **THE CONSULT'S CLASS (c) ENDPOINT IS
REACHED.**

- `mvMonomial_continuous`, `mvMonomial_zero_eq_zero`.
- `expectationUnder_combo_mul` / `covarianceUnder_combo_left`
  (bilinearity over finite monomial combinations).
- `eq_zero_of_covariance_self_zero` (stage C core: the L² variance
  argument, a.e.-to-everywhere via Continuous.ae_eq_iff_eq on the
  open-positive volume, constant killed at the origin) and
  `monomialCombo_eq_zero_of_covariance_monomials_zero`.
- `grade_eq_of_normalized_rates` (stage D: uniqueness of limits
  against stage B's difference limit forces every covariance to zero
  and the grade difference to vanish).

Together with PR #113 (exact moment-ratio recovery for the principal
quasi-homogeneous model) and PR #114 (the one-grade difference
limit), this realizes the consult's endpoint: "principal-model moment
ratios are recoverable, and — conditional on a common recovered
principal part — each finite weighted correction grade is recoverable
from normalized moment rates." Remaining class (c) items stay open by
design: the coarea/Gelfand-Leray layer (Mathlib GMT) and the full
weighted-analytic induction (a programme, not a tide).

Surprises: Finset.sum_div wanted the numerator-sum orientation
(convert per-term with mul_div_assoc after pushing the sum through
the division); the catalogued Pi.sub single-lambda trap fired on
integral_add (type-ascribed witness); push_neg is deprecated for
`push Not` on this toolchain.
