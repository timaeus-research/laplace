# Tide: germbij forward programme, stage 1 (asymptotic polynomials)

**Direction (user):** the nondegenerate core, forward direction
(programme A of the audit consult).
**Seabed:** laplace, main at 8a308ef (inverse half complete).
**Started:** 2026-08-10T02:30 local

## Design consult

The programme-A shape consult is archived verbatim in
`tide-log/gpt56_forwardA_shape_v1.md`. Its rulings, all adopted:

- Public API = EXISTENCE of coefficients + a comparison/uniqueness
  theorem (jet-dependence in comparison form); internal proof object
  = recursive coefficient collection P_j (each P_j visibly uses only
  V_1..V_j, hence derivatives through j+2) — never expose a
  multinomial formula.
- ForwardExpansionDomain N = a ONE-FIELD Peano-remainder mixin over
  HigherLaplaceDomain (N+2) (the O(||y||^{N+2}) bound identifies no
  coefficient; the little-o is the genuinely missing input).
- Do NOT apply the exponential-remainder estimate globally (the
  e^{|R|} majorant is not integrable for higher-degree potentials):
  localize first at the MESOSCOPIC radius ||z|| <= q^{-1/2}, where
  q^s ||z||^{s+2} <= ||z||^2 q^{s/2} makes the correction small
  relative to the quadratic for every finite order.
- Do NOT recurse the whole Laplace theorem order-by-order; confine
  recursion to the algebraic coefficient object.
- Implementation order: (1) AsymptoticPolynomial (predicate +
  uniqueness), (2) GaussianMeso (cutoff + tails + coercivity
  transfer), (3) ForwardExpansionDomain (Peano + exact exponent
  split), (4) ExpGraded (recursive P_j + scalar expansion),
  (5) NumeratorExpansion, (6) AsymptoticDivision,
  (7) ForwardCoefficients (public existence + jet comparison).

## Candidate (this tide = stage 1)

`IsMomentExpansion`-shaped predicate in generic form
(`IsAsymptoticExpansionTo f c N`: f minus the degree-N polynomial
with coefficients c is o(q^N) at 0+), and the uniqueness theorem
`asymptoticPolynomial_coeff_eq`: two coefficient systems expanding
the same function agree through order N (least-index/strong-
induction argument: divide by q^j, the polynomial part tends to the
j-th coefficient gap, the little-o part tends to zero, limits are
unique). Laplace-independent; also canonicalizes any later
Classical.choose coefficient function.

## Vote

- Claude: stage 1 as staged. - GPT-5.6 Sol: its own implementation
  order. Agreed.

## Numerical check

Not feasible: pure asymptotic algebra.
