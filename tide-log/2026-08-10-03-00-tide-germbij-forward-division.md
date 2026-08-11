# Tide: germbij forward programme stage 6 (asymptotic division)

**Direction (user):** "Yes continue with germbij... the main core
concern being the recovery of all coefficients in the nondegenerate
case and the main theorem in the nondegenerate case."

**Seabed:** laplace, branch tide/germbij-forward-package at 6070a92
(stacked; stage 5c-ii-b in PR #106). Design consult
(gpt56_forwardA_shape_v1.md): "a generic finite-division lemma for
asymptotic polynomials whose constant denominator coefficient is
nonzero."

**Started:** 2026-08-10T03:00Z

## Candidate

`Laplace/AsymptoticDivision.lean` (Laplace-independent, next to
AsymptoticPolynomial):

1. `divisionCoeff a b : ℕ → ℝ` by strong recursion:
   c_0 = a_0/b_0, c_j = (a_j - Σ_{i=1}^{j} b_i·c_{j-i})/b_0.
2. The convolution identity: for b_0 ≠ 0 and all j,
   Σ_{i∈range(j+1)} c_i·b_{j-i} = a_j.
3. `IsAsymptoticExpansionTo.div`: if f, g admit order-N expansions
   with coefficients a, b and b_0 ≠ 0, then f/g admits the order-N
   expansion with coefficients divisionCoeff a b. Proof:
   f/g - Σc q^j = (f - g·Σc)/g; the numerator telescopes into
   (f - Σa) + (Σa - Σb·Σc) - (g - Σb)·Σc; the middle polynomial
   difference has zero coefficients through q^N by the convolution
   identity (so is O(q^{N+1}) on (0,1]); each o(q^N) piece divides by
   g which is eventually bounded below by |b_0|/2.

## Numerical check

Feasible; executed before writing Lean (see Result): a = stage-4 test
coefficients, b = (2, 0.5, -0.1, 0.3), N = 3; check the convolution
identity and that (f/g - Σc q^j)/q^3 → 0 for synthetic
f = Σa q^j + q^4, g = Σb q^j + q^4.

## Result

`Laplace/Multi/AsymptoticDivision.lean` (~330 lines), all gates green:

- `divisionCoeff` (strong recursion via Finset.attach +
  termination_by), `divisionCoeff_eq` (unattached form via
  Finset.sum_attach), `divisionCoeff_conv` (the convolution identity).
- `coeffPoly` + eval/coeff/degree lemmas, `coeffPoly_mul_coeff`
  (Cauchy product through degree N via
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk).
- `poly_vanishing_tail_bound`, and the main
  `isAsymptoticExpansionTo_div`: quotients of order-N expansions with
  nonzero constant denominator coefficient expand with the division
  coefficients.

Numerical check passed before writing (convolution identity + the
o(q^N) decay of the quotient error at the stage-4 test coefficients).

Surprises: two rounds only. `div_eq_iff` wants the division on the
LEFT (use `eq_div_iff` when it is on the right); an untyped
`have := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds` cannot
synthesize the within-set (give the have its full type — the exact
same term elaborates fine against an explicit target).

### Suggested follow-ups

- Stage 7 (final): a_0(1) = ∫ e^{-T₂} > 0 (partition positivity via
  correctionCoeffFn_zero + Gaussian integral positivity); the moment
  expansion moment_hasExpansion := numerator / partition via this
  tide's division; the public existence + jet-comparison statements.
