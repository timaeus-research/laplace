# Tide: localised-mean-coeff

**Direction (user):** auto mode ("Continue with what you think best"); chosen direction: the localised anharmonic mean to second order — `t⟨x⟩_loc = c + c'/t + O(t⁻²)` with `c'` in closed form (eq:mean's `O(S²)` coefficient on the exact localised measure), via the sixth-order expansion of the localised weight, the second-order moments of tides 70–71 and the ratio bookkeeping; then E2.
**Seabed:** laplace, commit d995017 (branch `tide/localised-mean-coeff` off `main`)
**Started:** 2026-09-22T15:09Z

## Candidates v1 (Claude)

Setting as in tides 65–71: `ℓ = λx²/2 + αx³/6 + γx⁴/24`, localiser strength `g ≥ 0`, anchor `x₀`, `a = g x₀`, `b = g/2`, weight
`φ = e^{y}`, `y = ax − bx²`, `⟨x⟩_loc = ⟨xφ⟩/⟨φ⟩`. Available: `|t⟨x⟩_loc − c| ≤ K/t` with `c = −α/(2λ²) + a/λ` (tide 67); the moments to
second order `t⟨x⟩ = a₁ + B₁/t`, `t⟨x²⟩ = 1/λ + B₂/t`, `t²⟨x³⟩ = c₃ + B₃/t`, `t²⟨x⁴⟩ = 3/λ² + C₄'/t` (all with `K/t²` remainders, tides
70–71), the leading rates for `t³⟨x⁵⟩`, `t³⟨x⁶⟩` and the even-moment bounds `⟨x^{2k}⟩ ≤ C/tᵏ` for every `k`; `Real.exp_bound`.

- **A (the localised mean to second order, 1D).** `|t⟨x⟩_loc − c − c'/t| ≤ K/t²` with
  `c' = B₁ + aα²/λ⁴ − aγ/(2λ³) + αg/λ³ − αa²/(2λ³) − ag/λ²` — eq:mean's `O(S²)` coefficient on the exact localised anharmonic measure
  (tide 67's deferred C). Route: `|e^y − Σ_{m<6} y^m/m!| ≤ (e^M + 3)y⁶` for `y ≤ M` (`Real.exp_bound` at `n = 6` on `|y| ≤ 1`, crude
  beyond); `xφ = Σ_{k≤5} p_k x^k + Σ_{k=6}^{11} p_k x^k + xR₆` with `p₁ = 1, p₂ = a, p₃ = a²/2 − b, p₄ = a³/6 − ab, p₅ = a⁴/24 − a²b/2 +
  b²/2` (exact, signed) and an even-power bound on the tail (odd `|x|^k`, `k ≥ 7`, by `(x^{k−1} + x^{k+1})/2`; `y⁶ ≤ 32(a⁶x⁶ + b⁶x¹²)`),
  so `⟨xφ⟩ = m₁ + a m₂ + p₃ m₃ + p₄ m₄ + p₅ m₅ + O(t⁻³)` and `t⟨xφ⟩ = n₀ + n₁/t + O(t⁻²)`; `⟨φ⟩ = 1 + a m₁ + p₃ m₂ + O(t⁻²)` from the
  `y⁴` expansion (`|R₄| ≤ (e^M + 3)y⁴ ≤ 8(e^M+3)(a⁴x⁴ + b⁴x⁸)`, the `x³…x⁶` terms are `O(t⁻²)`), so `⟨φ⟩ = 1 + d₁/t + O(t⁻²)` with
  `d₁ = a·a₁ + (a²/2 − b)/λ`; then `tN/D = n₀ + (n₁ − n₀d₁)/t + O(t⁻²)`, `c' = n₁ − c d₁`.
- **B (E2, `d` dimensions).** `|(⟨w⟩_loc − c − meanShiftLoc − g S(w₀ − c))ⱼ − (Q(c'ᵢ − c'_{S,i})ᵢ)ⱼ/t²| ≤ K/t³`, where `c'_{S,i}` is the
  `1/t` coefficient of the displayed formula `P_t` (`P_t = c/t + c'_S/t² + O(t⁻³)`, `c'_S = αg/λ³ − ag/λ²`… to be computed); i.e.
  eq:mean's `O(S²)` term identified on E2's exact localised measure. Optional; A is the content.
- **C (the E3 localised LLC's first correction).** With A and tide 68/69's machinery the `1/t` coefficient of `t⟨ℓ⟩_loc` (GPT's
  `[a²/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)]`) would need `t⟨x²⟩_loc` to second order — the same expansion for `x²φ` plus
  `Var_loc` bookkeeping. Deferred.

Rationale: identifies the `O(S²)` term that tides 67–68 only bounded; closes the localised arc with a coefficient statement.
Cost: mechanical but long (degree-11 polynomial bookkeeping) — GPT's judgement on the truncation orders is the main risk.

## Numerical check

`numcheck_localised_mean_coeff.py` (sympy Wick expansion with the localiser inside the perturbation, `ε = 1/√t`): `c = (−α/2 +
gλx₀)/λ²` and `c'` exactly equal to the formula above (difference simplifies to `0`); `c' = 0.07515` at `λ = 1.3, α = 0.7, γ = 1.1,
g = 0.8, x₀ = 0.6`, matching tide 67's quadrature `t(t⟨x⟩_loc − c) = 0.0464, 0.0668, 0.0730, 0.0746, 0.0750` at `t = 10, …, 2560`.

## GPT-6 Astra v1

Verbatim in `gpt_localised_mean_coeff_v1.md` (prompt `gpt_localised_mean_coeff_prompt_v1.md`). Summary: A correct, but use the
*fifth*-order remainder (`e^y = P₄(y) + R₅`, `|R₅| ≤ (e^M+3)|y|⁵`), not sixth: `|xR₅| ≤ 16C(|a|⁵x⁶ + |b|⁵|x|¹¹)`, `|x|¹¹ ≤ (x¹⁰ + x¹²)/2`,
even moments through degree 12; the exact identity is degree 9, `xP₄(y) = x + ax² + p₃x³ + p₄x⁴ + p₅x⁵ + q₆x⁶ + … + q₉x⁹` with
`p₃ = a²/2 − b`, `p₄ = a³/6 − ab`, `p₅ = a⁴/24 − a²b/2 + b²/2`, `q₆ = ab²/2 − a³b/6`, `q₇ = a²b²/4 − b³/6`, `q₈ = −ab³/6`, `q₉ = b⁴/24`;
the `p₅m₅` term is `O(t⁻³)` by the *signed* fifth-moment bound (do not replace `|m₅|` by `⟨|x|⁵⟩`). Moment inputs: second order only
for `m₁, m₂`; leading with `O(t⁻³)` error for `m₃, m₄`; `|m₅| ≤ C/t³`; no `B₃`, no sixth-moment coefficient. Denominator: `P₃` with
`|R₄| ≤ C|y|⁴ ≤ 8C(a⁴x⁴ + b⁴x⁸)`, `D = 1 + am₁ + p₃m₂ + O(t⁻²) = 1 + d₁/t + O(t⁻²)`, `d₁ = −aα/(2λ²) + (a² − g)/(2λ)`. Independent
recomputation: `n₁ = B₁ + aB₂ + p₃c₃ + 3p₄/λ²`, `c' = n₁ − c d₁` = the stated formula ✓. Ratio: cross-multiply,
`U − qD = ε_N − cε_D − c'd₁/t² − (c'/t)ε_D` with `n₁ = c' + cd₁`, then divide by `D ≥ ½`. The localised Stein route is valid
(`L₂ = B₂ − 2aα/λ³ + (a² − g)/λ²`, `L₃ = −5α/(2λ³) + 3a/λ²`) but needs a weighted IBP theorem — not worth it here. B: for the displayed
`P_t = a/(tλ + g) − tα/(2(tλ + g)²)`, `P_t = c/t + c'_S/t² + O(t⁻³)` with `c'_S = αg/λ³ − ag/λ²`; the residual coefficient
`r = c' − c'_S = B₁ + aα²/λ⁴ − aγ/(2λ³) − αa²/(2λ³)` (at `g = 0` it is `B₁`); E2: `R_loc = Q(rᵢ)`, `|(⟨w⟩_loc − c − meanShiftLoc − gS(w₀−c)
− R_loc/t²)ⱼ| ≤ K/t³`. Wording: "identifies the `t⁻²` coefficient of the exact localised mean, and hence the second-order residual of
the displayed E2 approximation". Vote: strong yes on A (P₄ route, cross-multiplied ratio), B optional after checking `P_t`, C deferred.

## Vote
- Claude: A (+ B if it fits)
- GPT-6 Astra: A ("strong yes", `P₄` route); B optional; C deferred
