# Tide: germbij-gamma-remainder

**Direction (user):** the gamma-rung programme (auto mode, standing
delegation): complete the anharmonic jet recovery (lambda, alpha, GAMMA)
of the germbij note's Theorem 3.1 by proving t^3 kappa4 ->
-gamma/lam^4 + 3 alpha^2/lam^5 and the recovery corollary. This tide is
stage 1 of the 6-stage plan.

**Seabed:** laplace, main at a659dbb.
**Worktree/branch:** laplace-tide-germbij-gamma-remainder /
tide/germbij-gamma-remainder
**Started:** 2026-08-09T18:00Z

## Programme plan (scoping consult, verbatim in
tide-log/gpt56_gamma_rung_scoping_v1.md)

Target NUMERICALLY PINNED before scoping (mpmath, breakpoint quadrature;
t = 100..6400 converges to -0.1858371 at (lam, alpha, gamma) =
(1.3, 0.4, 0.9)): t^3 kappa4 -> -gamma/lam^4 + 3 alpha^2/lam^5.
GPT-5.6 Sol verified the full symbolic route: A = alpha/(6 lam^{3/2}),
B = gamma/(24 lam^2); J_n = m_n - A m_{n+3} t^{-1/2} +
(A^2/2 m_{n+6} - B m_{n+4}) t^{-1} + O(t^{-3/2}); the kappa4 t^{-3}
table sums to 108 A^2 - 24 B = 3 alpha^2/lam^5 - gamma/lam^4 (after the
lam^{-2} factor), and the t^{-2} Gaussian terms cancel. Risk assessment:
the coercivity risk is discharged by the standing discriminant
hypothesis alpha^2 < 3 lam gamma; the remaining risk is the domination
infra exposing the two-branch bound e^{-u^2/2} max(1, e^{-s_t(u)}) —
which the seabed's first-order ScalarBound layer already does.

Stages: (1) two-sided scalar Taylor remainder [THIS TIDE];
(2) second-order J_n asymptotics; (3) ratio/moment coefficient lemmas;
(4) kappa4 definition + algebraic assembly; (5) the analytic kappa4
limit; (6) gamma recovery corollary.

## Candidate (this tide)

`abs_expRemainder_le_max`: for all real s and all n,
|expRemainder n s| <= |s|^n / n! * max 1 (exp (-s)).
Proof: s >= 0 branch reuses the merged abs_expRemainder_le (max >= 1);
s <= 0 branch by the same FTC induction with the sharper inductive form
|E_n(s)| <= |s|^n/n! * exp(-s) on s <= 0 (at u in [s,0]:
e^{-u} <= e^{-s}; the polynomial integral via integral_comp_neg +
integral_pow).

## Numerical check

The bound is elementary and two-sided-sharp at s -> 0±; the programme
target was pinned numerically at scoping (above). Not separately
scripted for this stage.

## Vote

- Claude: stage 1 as deliberated in the programme scoping (single tide,
  two theorems in Laplace/OneD/ExpRemainderSigned.lean).
- GPT-5.6 Sol: the endpoint-maximum form and the FTC route were
  specified in the scoping consult's section 2 and tide staging.
  Agreed (inherited deliberation).

## Result

- Branch tide/germbij-gamma-remainder,
  Laplace/OneD/ExpRemainderSigned.lean: abs_expRemainder_le_of_nonpos
  (sharp e^{-s} form on s ≤ 0), abs_expRemainder_le_max (the two-sided
  endpoint-maximum bound for all real s).
- Three build iterations: integral_symm orientation +
  abs_neg (write |∫_0^s| = |∫_s^0| as its own have); positivity cannot
  see (-u)^n ≥ 0 from u ≤ 0 (explicit div_nonneg/pow_nonneg);
  field_simp closed leaving ring dangling; le_or_lt no longer exists
  (le_total).
- Surprise: the negative branch's inductive form (with e^{-s}, not the
  max) makes the induction go through verbatim; the max only appears in
  the final packaging.
