# Tide: grammar §4 fluctuation property (iv) S_1(a)

**Direction (user):** continue on auto to autoformalise grammar. Unit 4 of §4.
**Seabed:** laplace, branch tide/grammar-fluctuation-one off tide/grammar-fluctuation-recurrence.
**Started:** 2026-09-06

## Target (lem:fluctuation_properties (iv))

`fluctuation_one`: S_1(a) = (a/2) S_{1/2}(a) + 1/β  — the λ=0 boundary case.

## Proof plan

Mirror of unit 3's recurrence FTC, with g = e^{phase} (no t^λ factor). ∫₀^∞ d/dt[e^{phase}] =
g(∞) − g(0⁺) = 0 − 1 = −1 (boundary value 1, not 0). g'(t) = e^{phase}(−β + (βa/2)t^{-1/2}) =
−β·(t^{1-1} e) + (βa/2)·(t^{1/2-1} e), so ∫ g' = −β S_1 + (βa/2) S_{1/2} = −1 ⟹ (iv). Two derivative
terms (the λ t^{λ-1} term vanishes at λ=0). Reuses integral_Ioi_of_hasDerivAt_of_tendsto,
fluctuation_integrableOn at 1 and 1/2. No new GPT consult (mirror of unit 3).

## Result

Committed on `tide/grammar-fluctuation-one`. Theorem: `fluctuation_one`. `lake build` green (2751
jobs), `scripts/sorries` clean. Clean mirror of unit 3's FTC (g = e^{phase}, boundary value 1,
two derivative terms). No GPT consult needed. This CLOSES lem:fluctuation_properties (i)-(iv) +
eq:fluctuation_recurrence — all of §4.1. Deviation vs unit 3: hII has no t^λ factor (exponent is
-1/2 directly), so drop the `← rpow_add` step; atTop majorant reuses the s=0 case of
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` (t^0·exp = exp).
