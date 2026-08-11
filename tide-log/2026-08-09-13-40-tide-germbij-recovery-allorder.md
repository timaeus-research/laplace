# Tide: germbij-recovery-allorder

**Direction (user):** continue the germbij recovery thread (auto mode):
the all-order dimension-one expansion, completing the Section 7.4 ladder
for the quartic-perturbed Gaussian: every coefficient explicit, elementary
remainder at every order.

**Seabed:** laplace, chained on tide/germbij-recovery-expansion (81625e2,
PR #38 in flight); consumes the scale-t Gaussian moments and the monomial
integrability family.
**Worktree/branch:** laplace-tide-germbij-recovery-allorder /
tide/germbij-recovery-allorder
**Started:** 2026-08-09T13:40Z

## Candidates v1 (Claude)

**A (exponential Taylor remainder, all orders):** E_n(s) := e^{-s} -
Σ_{j<n} (-s)^j/j!; for s ≥ 0, |E_n(s)| ≤ s^n/n!. Route options: FTC
induction (E_{n+1}' = -E_n, E_{n+1}(0) = 0), Mathlib's
taylor_mean_remainder_lagrange (|d^{n+1}e^{-x}| ≤ 1 on [0,s]), or an
alternating-series bound.

**B (all-order quartic expansion):** for b ≥ 0, t > 0, n:
|Z_b(t) - √(2π) Σ_{j≤n} (-b)^j (4j-1)‼/j! · t^{-(j+1/2)}|
≤ √(2π) b^{n+1} (4(n+1)-1)‼/(n+1)! · t^{-(n+3/2)}.
n = 1 reproduces the previous tide with the sharp constant 105/2.

**C (coefficient limits, Tendsto packaging):** each coefficient as the
limit of the rescaled remainder.

## GPT-5.6 Sol v1

Saved verbatim in `tide-log/gpt56_germbij_recovery_allorder_v1.md`.
Summary: A by direct FTC induction with the E_n indexing (base |E_0| =
e^{-s} ≤ 1; step E_{n+1}(s) = -∫_0^s E_n), NOT the Taylor API (polynomial
normalization, derivative towers, endpoint friction) and NOT alternating
series (terms not decreasing for s > 1; the true reason is the bounded
derivative, not the alternating criterion); B's bookkeeping verified
term by term including the j = 0 natural-subtraction convention
(4·0-1 = 0 truncated, 0‼ = 1 = (-1)‼); recommended isolating the rpow
algebra ((-tb)^j · t^{-(2j+1/2)} = (-b)^j t^{-(j+1/2)}) in helper lemmas
outside the integration proof; C deferred to a follow-up (a separate
layer of Tendsto/rpow work not needed for the expansion itself).

## Vote

- Claude: A + B (C deferred), Laplace/OneD/RecoveryAllOrder.lean.
- GPT-5.6 Sol: A + B now, C deferred. Agreed.

## Numerical check

The n = 1 case was verified numerically in the previous tide (rescaled
correction -> -3b√(2π); error constant with factor-two slack). For n = 2
(scipy quad, b = 0.1, run now): see appended output below.
```
t=10: |Z - main_n2| = 9.523e-04  vs bound 1.373e-03  ok=True
t=100: |Z - main_n2| = 4.144e-07  vs bound 4.343e-07  ok=True
t=1000: |Z - main_n2| = 1.367e-10  vs bound 1.373e-10  ok=True
```

## Result

- Branch tide/germbij-recovery-allorder,
  Laplace/OneD/RecoveryAllOrder.lean: expRemainder (def),
  expRemainder_continuous, expRemainder_succ_zero,
  hasDerivAt_expRemainder, abs_expRemainder_le (the all-order FTC
  induction), rpow_shift, quartic_partition_expansion_allOrder.
- Six build iterations. Fixes: dead ring after field_simp; the
  HasDerivAt.sub/sum Pi-form vs single-lambda mismatch (converted via a
  funext bridge, the derivative-side sibling of the documented Pi.add
  gotcha); explicit (μ := volume) on
  intervalIntegral.norm_integral_le_integral_norm; ‼ notation needs
  open scoped Nat; the final exponent-form mismatch (-(a+1/2) vs
  -a-1/2) resolved by placing the equality calc under le_of_eq.
- Surprise: the FTC induction went through on the first attempt at the
  mathematical level; every iteration was elaboration-level. The n = 1
  case subsumes the previous tide's bound with the sharp constant
  105/2.
