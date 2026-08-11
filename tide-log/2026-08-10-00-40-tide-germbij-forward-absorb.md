# Tide: germbij forward programme stage 5c-pre (Gaussian absorption)

**Direction (user):** "Yes continue with germbij, and do not switch into
another seabed... the main core concern being the recovery of all
coefficients in the nondegenerate case and the main theorem in the
nondegenerate case."

**Seabed:** laplace, branch tide/germbij-forward-scalarbounds at
005296b (stacked; stage 5b in PR #101). Architecture consult archived
as `tide-log/gpt56_stage5_shape_v1.md`; this tide is its items 1-3.

**Started:** 2026-08-10T00:40Z

## Candidates (consult section 4 + implementation order 1-3)

1. **The T₂/qform bridge by ray coefficient uniqueness.** The domain
   ties H to L only through `quadratic_peano`; the bridge composes
   both Peano statements along the ray `t ↦ t•z` and applies stage
   A1's `isAsymptoticExpansionTo_coeff_eq` at order 2. Byproducts, at
   j = 1 and j = 2 respectively: `taylorHomogeneousTerm_one_eq_zero`
   (the domain's critical-point condition, discharging
   `exponent_split`'s hypothesis for free) and
   `taylorHomogeneousTerm_two_eq_qform`. Then the named lower bound
   `t2_lower : λ/2·‖z‖² ≤ T₂(z)` from `qform_lower`.
2. **Arbitrary-small Peano control on the window**:
   `eventually_abs_scaledRem_le` (|ρ_q(z)| ≤ ε‖z‖^(N+2) eventually,
   from taylorPeano + smul_mem_ball_of_mesoscopic) and its quadratic
   form `eventually_abs_scaledPerturbation_le_quadratic`
   (|q^N ρ_q(z)| ≤ ε‖z‖², using (q‖z‖)^N ≤ 1 on the window).
3. **The homogeneous correction bound**
   `eventually_exponentCorrection_le_quadratic`
   (∑_s q^s|V_s(z)| ≤ ε‖z‖², sum-of-absolute-values form per the
   consult) and the combined **Gaussian absorption**
   `gaussian_absorb`: e^{-T₂}·e^{∑|..|+|q^Nρ|} ≤ e^{-(λ/4)‖z‖²}
   eventually on the window.
4. The reusable integrability helper
   `integrable_one_add_norm_pow_mul_gaussian` (binomial expansion +
   the seabed's polynomial-Gaussian integrability).

## Numerical check

Not feasible in closed form: the statements are eventual bounds with
existential constants. The scale arithmetic (q^s‖z‖^(s+2) =
‖z‖²(q‖z‖)^s ≤ ‖z‖²q^(s/2) on the window) was verified symbolically
in the consult.

## Result

`Laplace/Multi/GaussAbsorb.lean` (~330 lines), all gates green:

- `isBigO_pow_pow_nhdsGT` (t^n = O(t^m) at 0⁺ for m ≤ n).
- `rayExpansion_taylor` / `rayExpansion_quad` (the loss along a ray
  as an order-2 asymptotic polynomial, two ways).
- `taylorHomogeneousTerm_one_eq_zero` (the critical-point condition,
  free from coefficient uniqueness at j = 1: discharges
  exponent_split's hgrad hypothesis for every domain) and
  `taylorHomogeneousTerm_two_eq_qform` (the bridge, at j = 2).
- `t2_lower` (λ/2·‖z‖² ≤ T₂), `eventually_abs_scaledRem_le`,
  `eventually_abs_scaledPerturbation_le_quadratic`,
  `eventually_exponentCorrection_le_quadratic`, `gaussian_absorb`
  (e^{-T₂}·e^{corrections} ≤ e^{-(λ/4)‖z‖²} on the window).
- `integrable_one_add_norm_pow_mul_gaussian` (binomial +
  integrable_pow_mul_exp_neg_mul_sq).

The T₂/qform bridge consumed stage A1's coefficient uniqueness — the
programme's own first stage closed its central identification.

Surprises: `Real.sqrt_le_one` is an iff (use .mpr); λ cannot appear
inside an identifier (hλ fails to parse — it is the fun-notation
token); an unused domain binder in the correction lemma tripped the
zero-warnings gate (renamed _D, dot-notation callers unaffected).

### Suggested follow-ups

- Stage 5c (next): rescaledNumerator definition, the normalized
  q-uniform Gaussian majorant on the window (consuming this tide's
  gaussian_absorb + 5b's scalar bounds + 5a's coefficient growth),
  filter-indexed DCT with the indicator folded in, the two outer-tail
  removals (stage 2), and numerator_hasExpansion.
