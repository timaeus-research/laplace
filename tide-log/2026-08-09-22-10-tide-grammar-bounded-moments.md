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

## GPT-5.6 Sol v1

Archived verbatim in `tide-log/gpt56_grammar_moments_v1.md`. All
three candidates correct (with "grows like" corrected to "decays
like" for the tail prefactor — 2 M_j(t/2) = (48/t)^alpha Gamma,
decaying in t). Rulings: extract the generic even-split lemma
(second use; Integrable + evenness + 0 <= a, real-valued, no
continuity); land candidate 2 as the headline with 1 as its helper;
candidate 3 is the better semantic endpoint but NOT the minimal
addition — and when it comes, state it as an eventual exponential
inequality / IsBigO against exp(-(a^4/48) t) (the relative-error
argument preserves the rate; coarse polynomial denominator bounds
would lose it), with SuperPoly as a corollary; the grammar-facing
rescaled form t^{j/2} Q_j -> explicit Gamma constant is the
recommended follow-up statement. Z_n[phi]-specific analytics
deferred until the grammar-side object stabilizes: "the moment
approximation is the reusable analytic kernel."

## Vote

- Claude: candidate 2 (+1 as helper, + generic even split), per the
  consult's staging; candidate 3 deferred to the next tide in the
  rescaled exponential form.
- GPT-5.6 Sol: same. Agreed.

## Numerical check (executed before this text)

j = 1, t = 50, a = 1 (scipy quad):

    tail = 1.372129e-02  <=  bound 2.096849e-01  : True
    |Icc - M_j| = 2.744257e-02  <=  bound 4.193698e-01  : True
    full-line numeric = 0.3533334288, closed form = 0.3533334288

Normalized difference decay (candidate 3 preview): |Q - N| =
9.3e-2 / 1.5e-2 / 1.2e-3 at t = 20/50/100, well inside the
e^{-t/48} envelope.
