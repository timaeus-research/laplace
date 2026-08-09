# Tide: germbij forward programme stage 5a (coefficient functions)

**Direction (user):** "Yes continue with germbij, and do not switch into
another seabed. Consult with 5.6 Sol to make sure there aren't higher
value targets for autoformalisation remaining, the main core concern
being the recovery of all coefficients in the nondegenerate case and
the main theorem in the nondegenerate case."

**Seabed:** laplace, branch tide/germbij-forward-expgraded at a27cde0
(stacked; stage A4 in PR #99). Design consult archived as
`tide-log/gpt56_forwardA_shape_v1.md` (stage-1 tide); a stage-5
architecture consult is in flight in parallel (will be archived when
it returns).

**Started:** 2026-08-09T23:45Z

## Candidates

Stage 5a: the consult-independent half of the numerator stage. The
integrated expansion's coefficients are
`a_j = ∫ z^α e^{-T₂(z)} P_j(z) dz` with
`P_j(z) = expCorrectionCoeff (fun s ↦ exponentTerm s L z) N j`; for
those integrals to exist and for DCT domination, `z ↦ P_j(z)` needs:

1. `exponentPoly_coeff`: the coefficient of `exponentPoly a N` at `u`
   is `if u ∈ Icc 1 N then a u else 0`.
2. `continuous_taylorHomogeneousTerm`: `z ↦ T_m(z)` is continuous
   (multilinear map on the diagonal).
3. Induction through `Polynomial.coeff_mul` on the power `i`:
   continuity and polynomial growth `|((exponentPoly (V z) N)^i).coeff k|
   ≤ D · (1 + ‖z‖)^(k + 2i)` of the coefficient functions of powers.
4. `correctionCoeffFn` (the `P_j` above), its continuity, and the
   growth bound `|P_j(z)| ≤ C · (1 + ‖z‖)^(j + 2(N+1))`-shape.

## Numerical check

Not feasible in the usual closed-form sense: the statements are
structural (continuity, existence of growth constants). The
coefficient values themselves were checked numerically in the stage-4
tide.

## GPT-5.6 Sol stage-5 architecture consult

Fired in parallel with this tide; archived verbatim as
`tide-log/gpt56_stage5_shape_v1.md`. Highlights affecting the plan:

- The unrestricted-x exponential remainder route is CONFIRMED as
  cheaper than a q^(-1/4) sub-window (which would need a second
  varying set, new tail theorems, annulus estimates, and still could
  not bound the Peano remainder absolutely at N = 0).
- 5a must cover arbitrary j (tail coefficients up to degree N² are
  consumed by the polynomial tail bound) — this tide already does.
- Recommended implementation order for the rest of stage 5:
  (1) T₂/H bridge + named Gaussian lower bound; (2) arbitrary-small
  Peano control on the window (eventually_abs_scaledRem_le);
  (3) absolute-correction absorption into a weakened Gaussian;
  (4) [this tide]; (5) unrestricted exp/perturbation inequalities;
  (6) the normalized q-uniform Gaussian majorant (the single DCT
  interface); (7) filter-indexed DCT with the indicator folded in
  (MeasureTheory.tendsto_integral_filter_of_dominated_convergence);
  (8) two outer-tail removals via stage 2; (9) numerator_hasExpansion.
- Sum-of-absolute-values form for the correction bound (avoids
  cancellation issues in exp(|A| + |δ|)).
- Watch: continuity/measurability of scaledRem (q ≠ 0 available
  eventually); integrable_one_add_norm_pow_mul_gaussian as a
  reusable helper.

## Vote

- Claude: proceed with the consult's order; 5a as built (arbitrary j).
- GPT-5.6 Sol: same decomposition with the two adjustments noted
  (arbitrary j — already satisfied; majorant packaged at the 5b/5c
  boundary).

## Result

`Laplace/Multi/CoeffFn.lean` (~230 lines), all gates green:

- `exponentPoly_coeff` (if-then-else description),
  `gradedExpPoly_coeff` (finite sum over coefficients of powers).
- `correctionCoeffFn` + `correctionCoeffFn_zero = 1`.
- `continuous_exponentPoly_coeff` / `continuous_exponentPoly_pow_coeff`
  (induction through Polynomial.coeff_mul) /
  `continuous_correctionCoeffFn`.
- `abs_exponentPoly_coeff_le` / `abs_exponentPoly_pow_coeff_le`
  (growth (1+‖z‖)^(k+2i), antidiagonal exponent matching) /
  `abs_correctionCoeffFn_le` (growth (1+‖z‖)^(j+2N)).

Surprises: none mathematical. Iteration errors: positivity cannot see
nonnegativity of opaque chosen constants (pass mul_nonneg explicitly);
`← pow_add` needs `mul_mul_mul_comm` first to make the pow factors
adjacent; a gcongr bullet order mismatch fixed by explicit mono lemmas.
