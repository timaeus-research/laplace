# Tide: germbij forward programme stage 5c-ii-b (numerator packaging)

**Direction (user):** "Yes continue with germbij, and do not switch into
another seabed... the main core concern being the recovery of all
coefficients in the nondegenerate case and the main theorem in the
nondegenerate case."

**Seabed:** laplace, branch tide/germbij-forward-numerator at 6804103
(stacked; stage 5c-ii-a in PR #104). Consult items 8-9.

**Started:** 2026-08-10T02:20Z

## Candidate

Completes the numerator stage. `Laplace/Multi/NumeratorTails.lean`:

1. `abs_integrand_eq`: |integrand P q z| = |P z|·|integrand 1 q z|.
2. `observable_integrand_tail_isLittleO`: the outer tail of the true
   integrand, ∫_{mesoᶜ}|integrand P| = o(q^M) for every M — via the
   two-term bound |P| ≤ CP(‖z‖⁰ + ‖z‖ⁿ) (no binomial needed for this
   one) and stage 2's integrand_meso_tail_isLittleO.
3. `coeff_polynomial_tail_isLittleO`: the outer tail of the
   coefficient polynomial, via the collapsed bound
   CW(1+‖z‖)^{n+3N}e^{-(λ/2)‖z‖²} and gaussian_meso_tail_isLittleO
   after a binomial split.
4. `numerator_hasExpansion`: the eventual decomposition (window +
   true tail - coefficient tail, using integral_add_compl and the
   eventual U-indicator collapse on the window through
   smul_mem_ball_of_mesoscopic at delta), the window piece as o(q^N)
   via isLittleO_iff_tendsto' + the 5c-ii-a DCT, and the o-sum
   assembly into Laplace.IsAsymptoticExpansionTo with coefficients
   numeratorCoeff.

## Numerical check

Covered at the scalar level in stage 4 (the integrated coefficients
are Gaussian integrals of the checked scalar coefficients; the
statement is existence-form per the programme's API).
