# Tide: germbij tensor J5a+J5b (rate calculus openers)

**Direction (user):** standing auto-mode commission on the germbij
note; the first two of the five J5 sub-stages ruled by the shape
consult (archived verbatim: `tide-log/gpt56_j5_shape_v1.md`).
**Seabed:** laplace main post-#76 (J2-J4 merged).
**Started:** 2026-08-09T11:30 local

## Candidates

The J5 consult's rulings (all adopted): generic k from the start
(cubic-first would duplicate the proof); NO sqrt-q split (the fixed
ball ‖qx‖ < ρ plus the trade q^{-r} ≤ ρ^{-r}‖x‖^r on the tail
support gives a q-uniform Gaussian dominator); unequal domains
handled by two retreating tails; the quotient identity
N₁/D₁ − N₂/D₂ = (N₁−N₂)/D₁ − (N₂/D₂)((D₁−D₂)/D₁) with only D₁ in
the outer division; the exponential difference via the INTEGRAL
secant identity e^{-a} − e^{-b} = −(a−b)∫₀¹ e^{-((1−t)b+ta)}dt (no
chosen mean-value point — measurability); HigherLaplaceDomain with a
direct Taylor-remainder field (smaller proof surface than deriving
it from ContDiffAt). Staging J5a-J5e; this tide delivers:

1. **J5a**: `exp_neg_sub_exp_neg_eq` (the FTC secant identity),
   `abs_exp_neg_sub_exp_neg_le` (the two-sided secant bound —
   mirroring the seabed's 1D JetDifference bound), and
   `tendsto_exp_neg_sub_div` (the scalar limit
   (e^{-a₁}−e^{-a₂})/s → −e^{-u}·v from a_j → u, (a₁−a₂)/s → v),
   with the secant's limit by dominated convergence on [0,1]
   (eventual [u−1,u+1] confinement, constant dominator).
2. **J5b**: `tendsto_integral_retreating_tail_div_pow` — the
   rate-r-divided integral of a polynomial-growth function times a
   Gaussian over the retreating region ρ ≤ q‖x‖ tends to zero, by
   the q^{-r} ≤ ρ^{-r}‖x‖^r trade and the filter DCT.

## Numerical check

Executed after this section header was written; output quoted
verbatim below (secant identity at (a,b) = (0.7, -0.3), and the
retreating tail at r = 1 for a 1D Gaussian).
    e^-a - e^-b   = -0.8532735038
    -(a-b)*secant = -0.8532735038
    q=0.5: tail/q = 9.814e-02
    q=0.1: tail/q = 2.152e-45
    q=0.02: tail/q = 0.000e+00

## Vote

- Claude: J5a+J5b as one tide (both consult-staged small checkpoints).
- GPT-5.6 Sol: same staging (archived shape consult, section 4).

Agreed.

## Result

One file (`Laplace/Multi/RateCalculus.lean`, ~370 lines, sorry-free):

- `hasPolynomialGrowth_norm_pow`,
  `integrable_pow_mul_exp_neg_mul_sq` (general rate c > 0, the
  H2a series-term trick with (2/c)^m·m!), and
  `integrable_mul_exp_neg_mul_sq_of_polynomialGrowth` — the
  general-rate Gaussian integrability layer J5c-J5e will consume.
- J5a: `exp_neg_sub_exp_neg_eq` (the FTC secant identity, stated
  with the b + t(a-b) exponent shape), `abs_exp_neg_sub_exp_neg_le`
  (two-sided secant bound via norm_integral_le_of_norm_le_const and
  the convex-combination min bound), and `tendsto_exp_neg_sub_div`
  (the scalar rate limit; secant limit by the filter DCT on
  volume.restrict (Ioc 0 1) with eventual [u-1,∞) confinement and a
  constant dominator — required adding [l.IsCountablyGenerated]).
- J5b: `tendsto_integral_retreating_tail_div_pow` — the q^{-r} ≤
  ρ^{-r}‖x‖^r trade on the support ρ ≤ q‖x‖, filter DCT, pointwise
  vanishing because the region retreats past every fixed x.

Error classes: the ae-restricted bound obligation (of_forall
over-quantifies for restrict-measure DCT — use
ae_restrict_mem measurableSet_Ioc); the cascading-rewrite trap
avoided by never stating 0 = ∫ 0 as a rewritable equation (it
rewrites the filter's 0 too — restructure with a typed `have hmain`
instead); AESM has `.mul_const` but NOT `.div_const` (division is
defeq mul-inverse, exact accepts the mul_const form); this pin's
`integrableOn_const` takes autoParam finiteness arguments (the
`finiteness` tactic doesn't know Real.volume_Ioc — discharge with
ofReal_ne_top explicitly); beta-unreduced FTC endpoints (rewrite the
exponent identities b + 1·(a−b) = a instead of lambda applications).
