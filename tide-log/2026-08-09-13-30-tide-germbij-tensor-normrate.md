# Tide: germbij tensor J5e (normalized moment difference)

**Direction (user):** standing auto-mode commission; the final J5
sub-stage per the shape consult.
**Seabed:** laplace, branch tide/germbij-tensor-pairwise at 519e5fe
(stacked on unmerged J5d, PR #79).
**Started:** 2026-08-09T13:30 local

## Candidates

Consult J5e (its quotient identity and assembly), plus one gap the
staging exposed: H4's generic limit `tendsto_integral_rescaled` is
restricted to QUADRATIC-growth observables (built for moments 0/1/2),
but the N₂/D₂ factor of the quotient identity needs it for arbitrary
polynomial growth (degree-k tests, k ≥ 3). So:

1. `tendsto_integral_rescaled_poly`: H4's dominated-convergence
   theorem re-proven at polynomial growth — same structure, dominator
   C(1+‖x‖^n)e^{-c‖x‖²} integrable by the J5a general-rate layer.
2. `rescaledMoment A P q := (∫ A.integrand P q)/(∫ A.integrand 1 q)`
   (the consult's rescaled formulation, "preferable internally").
3. The scalar quotient lemma (consult's div_sub_div_rearranged,
   rate-divided form) proven on opaque scalars — NOT via field_simp
   on integral-bearing goals (the J5d catalogue entry).
4. **`tendsto_pairwise_normalized_moment_difference`**:
   (M₁(P,q) − M₂(P,q))/q^{k−2} → −gaussianCovariance H P Q, from
   J5d at P and at 1, the generalized H4 limits, eventual denominator
   positivity, and the limit-value algebra with integral atoms
   folded.

## Numerical check

Ratios of already-verified integrals; the covariance target equals
the H2a-verified quantities combination. Structural.

## Vote

- Claude: as staged.
- GPT-5.6 Sol: same (archived consult, section J5e).

Agreed.

## Result

One file (`Laplace/Multi/NormalizedRate.lean`, ~230 lines, sorry-free,
two-repair pass — dead rewrites after set-folding did its job):

- `tendsto_integral_rescaled_poly`: H4's generic dominated
  convergence at POLYNOMIAL growth (the gap the staging exposed —
  H4's original was quadratic-growth only), dominator via the J5a
  general-rate layer.
- `rescaledMoment` (the consult's internally-preferred formulation).
- The scalar quotient identity as a private lemma on opaque reals
  (per the J5d catalogue rule: never field_simp an integral-bearing
  quotient).
- **`tendsto_pairwise_normalized_moment_difference`**: the J5 arc's
  final form — (M₁(P,q) − M₂(P,q))/q^{k−2} → −Cov_γ(P, Q) — from
  J5d at P and at 1, the polynomial-growth ordinary limits, eventual
  denominator positivity, and the limit-value algebra with all four
  Gaussian integrals folded to atoms.

THE J5 ARC (a-e) IS COMPLETE: five sub-stages in four tides, exactly
as the shape consult staged them, with its two predicted hard points
(the rate-divided domination and the tail split) landing via the
secant bound and the q^{-r} ≤ ρ^{-r}‖x‖^r trade respectively.
