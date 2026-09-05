# Tide: grammar §4 fluctuation recurrence + ODE + S_1

**Direction (user):** continue on auto to autoformalise grammar. Unit 3 of §4.
**Seabed:** laplace, branch tide/grammar-fluctuation-recurrence off tide/grammar-fluctuation-deriv.
**Started:** 2026-09-05

## Targets (lem:fluctuation_properties (iii),(iv) + eq:fluctuation_recurrence)

- `fluctuation_recurrence`: S_{λ+1}(a) = (a/2)S_{λ+1/2}(a) + (λ/β)S_λ(a)  [IBP, λ>0].
- `fluctuation_ode` (iii): β²S_{λ+1} = (aβ/2)(βS_{λ+1/2}) + λβ S_λ  [= β²·recurrence, algebra].
- `fluctuation_one` (iv): S_1(a) = (a/2)S_{1/2}(a) + 1/β  [λ=0 boundary FTC].

## Proof plan

Both recurrence and (iv) use ∫_{(0,∞)} d/dt[t^λ e^{-βt+βa√t}] dt = [t^λ e^phase]₀^∞ (FTC on Ioi,
vanishing boundary). Integrand deriv = (λ t^{λ-1} − β t^λ + (βa/2) t^{λ-1/2}) e^phase. For λ>0 both
boundary limits are 0 ⇒ λ S_λ − β S_{λ+1} + (βa/2) S_{λ+1/2} = 0 ⇒ recurrence. For λ=0, boundary =
0 − 1 = −1 ⇒ −β S_1 + (βa/2) S_{1/2} = −1 ⇒ (iv). (iii) = β²·recurrence (field_simp/ring).

Consult GPT-6 Astra on the Mathlib FTC-on-Ioi lemma (integral_Ioi_of_hasDerivAt_of_tendsto or
similar) + the boundary-limit / integrability plumbing.

## GPT-6 Astra v1

`tide-log/gpt6_fluctuation_recurrence_v1.md`. Astra confirmed the math and the FTC-on-Ioi route;
key steers: the improper-FTC lemma needs continuity at the endpoint (not differentiability) — g is
continuous at 0 (g 0 = 0 for λ>0) but not differentiable; define the derivative D with the exact
shifted exponents so the integral decomposition identifies with `fluctuation` values definitionally;
the monotone-`a` domination reuse from unit 2 wasn't needed here — instead the atTop decay via
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` + AM–GM squeeze.

## Result

Scope: recurrence + (iii); property (iv) [λ=0 boundary] deferred to a short unit 4 (reuses the FTC
machinery). Committed on `tide/grammar-fluctuation-recurrence`. Theorems: `fluctuation_recurrence`,
`fluctuation_ode`. `lake build Laplace.Grammar.Fluctuation` green (2751 jobs), `scripts/sorries` clean.
Exact v4.33 lemma: `integral_Ioi_of_hasDerivAt_of_tendsto` (`ContinuousWithinAt f (Ici 0) 0`,
derivatives on `Ioi 0`, `f'` integrable, `atTop`-limit → `∫ f' = m − f 0`). Deviations: `continuousAt_rpow_const`
(top-level, not `Real.`-namespaced); the derivative reconciliation via `hval ▸ hg` (t^λ·(√t)⁻¹ = t^{λ-1/2}
by `rpow_neg`+`rpow_add`); integral linearity needed type-ascribed single-lambda `IntegrableOn`
witnesses + `hDe : D = … := rfl` to unfold the `let` (the CLAUDE.md Pi.add/let gotcha).
