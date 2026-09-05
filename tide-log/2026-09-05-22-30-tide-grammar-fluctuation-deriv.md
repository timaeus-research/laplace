# Tide: grammar §4 fluctuation properties (i),(ii) — derivative ladder

**Direction (user):** continue on auto to autoformalise grammar. Unit 2 of the §4 campaign.
**Seabed:** laplace, branch tide/grammar-fluctuation-deriv off tide/grammar-fluctuation-defn (unit 1, PR #140).
**Started:** 2026-09-05

## Target (lem:fluctuation_properties (i),(ii))

- (i) `S'_λ(a) = β·S_{λ+1/2}(a)` — differentiate under the integral (∂_a of the phase = β√t).
- (ii) `S''_λ(a) = β²·S_{λ+1}(a)` — apply (i) twice (corollary).

Lean:
- `hasDerivAt_fluctuation : HasDerivAt (fluctuation β lam) (β * fluctuation β (lam+1/2) a) a`
- `deriv_fluctuation` (deriv form)
- `hasDerivAt_deriv_fluctuation : HasDerivAt (fun a => β * fluctuation β (lam+1/2) a) (β^2 * fluctuation β (lam+1) a) a`

## Proof plan

(i): `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. F(a,t)=t^{λ-1}e^{-βt+βa√t},
F'(a,t)=β t^{λ-1/2}e^{...}. hF_int = unit-1 `fluctuation_integrableOn`. Uniform bound over a'∈ball(a,ε):
β e^{β(|a|+ε)²/2} t^{λ-1/2}e^{-(β/2)t} (Gamma p=1, exp λ-1/2>-1). ∫F'(a,·)=β·S_{λ+1/2} via rpow arith
t^{λ-1}·√t = t^{(λ+1/2)-1}. (ii): (i).const_mul β at λ+1/2, reconcile (λ+1/2)+1/2=λ+1, β·β=β².

Consult GPT-6 Astra on the exact v4.33 lemma name + dominating-hypothesis shape.

## GPT-6 Astra v1

`tide-log/gpt6_fluctuation_deriv_v1.md`. Astra was fast (no timeout) and supplied the key
simplification: the derivative integrand is **monotone in the parameter b**, so on `ball a 1` it is
dominated by itself at `a+1` — integrable directly via unit-1 `fluctuation_integrableOn` at
`(λ+1/2, a+1)`. No AM–GM, no second integrability lemma. Also gave the normalised `F'` (= shifted
integrand `D = β·G`) so the final integral is one `integral_const_mul`.

## Result

Committed on `tide/grammar-fluctuation-deriv` (chained off unit 1). Theorems:
`hasDerivAt_fluctuation` (i), `deriv_fluctuation`, `hasDerivAt_deriv_fluctuation` (ii).
`lake build Laplace.Grammar.Fluctuation` green (2751 jobs), `scripts/sorries` clean.
Deviations from Astra's skeleton: the v4.33 `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
takes `(hs : s ∈ 𝓝 x₀)` for a neighbourhood *set* `s` (I passed `s := Metric.ball a 1`,
`Metric.ball_mem_nhds a one_pos`), not `0 < ε`; `add_le_add_left` has swapped orientation on this
pin (used `linarith`); `show`→`change` for the style linter.
