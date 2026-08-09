# Tide: grammar bounded-prior quartic even moments

**Direction (tide-pick candidate 1):** bounded-prior quartic even
moments = full-line Gamma closed form minus exponentially-bounded
tail (mirroring quartic_partition_bounded_prior, the j = 0 case);
normalized bounded-prior moment converges to the full-line moment.
**Seabed:** laplace, main at b3b2d69.
**Started:** 2026-08-09T22:10 local

## Candidates v1 (Claude)

Seabed: quartic_tail_Ioi (Gaussian-comparison tail at j = 0),
quartic_partition_split (even split), quartic_partition_bounded_prior
(j = 0 headline), quartic_moment_even (full-line closed forms), and
today's SuperPoly vocabulary (Laplace.Anchoring).

1. **Moment tail bound via rate-halving**: for w >= a, split
   e^{-tw^4/24} = e^{-tw^4/48} e^{-tw^4/48} <= e^{-ta^4/48} e^{-tw^4/48},
   so int_{Ioi a} x^{2j} e^{-tx^4/24} <=
   M_j(t/2) e^{-ta^4/48} with M_j the full-line closed form —
   avoiding polynomial-times-Gaussian tail machinery entirely
   (the j = 0 seabed's Gaussian-comparison route does not extend
   cheaply past monomial factors).
2. **Bounded-prior moment approximation**: the even split at x^{2j}
   (mirror of quartic_partition_split) plus 1 gives
   |int_{Icc(-a,a)} x^{2j} e^{-tx^4/24} - M_j(t)| <=
   2 M_j(t/2) e^{-ta^4/48}: the j = 0 headline generalized.
3. **Normalized superpolynomial agreement**: the bounded-prior
   normalized moment (moment / partition on Icc) differs from the
   full-line normalized moment by a superpolynomially small function
   of t — SuperPoly (Laplace.Anchoring vocabulary) via the
   quotient-difference algebra with the exponential bounds from 1-2
   and the polynomial lower bound on the partition function.

Rationale: 1+2 are the mechanical extension; 3 is the grammar-facing
payoff (bounded priors are asymptotically invisible in normalized
observables) and the first consumer of SuperPoly outside its
birthplace.
