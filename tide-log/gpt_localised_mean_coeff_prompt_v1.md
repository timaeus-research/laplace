# Tide 72 consult: the localised anharmonic mean to second order (eq:mean's O(S²) coefficient)

One-round consult on a Lean 4 / Mathlib formalisation step in the `laplace` seabed. Real names: tide 65 `locWeight` (`φ = e^{g x₀ x −
(g/2)x²}`), `locWeight_le` (`φ ≤ e^{g x₀²/2}`), `localisedMean_eq_ratio` (`⟨x⟩_loc = ⟨xφ⟩/⟨φ⟩`), `locDenominator_rate` (`|⟨φ⟩ − 1| ≤ K/t`);
tide 67 `abs_exp_sub_taylor2_le` (`|e^y − 1 − y − y²/2| ≤ (e^M+3)|y|³`, `y ≤ M`, from `Real.exp_bound`), `localisedMean_anharmonic_rate_sharp`
(`|t⟨x⟩_loc − c| ≤ K/t`); tide 70 `mean_anharmonic_order2_rate` (`|t⟨x⟩ + α/(2λ²) − B₁/t| ≤ K/t²`), `ibp_anharmonic`; tide 71
`thirdMoment_order2_rate` (`B₃`), `fourthMoment_order2_rate`, `fifthMoment_bound`, `sixthMoment_lead`, `secondMoment_anharmonic_order3_rate`
(`B₂`, `K/t²`); `evenMoment_bound k` (`⟨x^{2k}⟩ ≤ C/tᵏ`); `gibbs_lin3`, `gibbs_sub_sub`, `abs_gibbsExpectation_le'`, `gibbsExpectation_mono'`.

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

## Questions

1. Is A correct and are the truncation orders right? Specifically: (i) is the sixth-order expansion of `φ` (remainder `y⁶`, even)
   the minimal one that makes the remainder of `⟨xφ⟩` `O(t⁻³)` — the `y⁴`-remainder route fails because `x·y⁴ ∋ a⁴x⁵` would be bounded
   through `|x|⁵`, losing to `O(t⁻²)`, unless the `x⁵` coefficient is kept exactly (which is what keeping `Σ_{k≤5} p_k x^k` exact does — so
   is a `y⁴`/`y⁵` truncation with exact `x⁵` coefficient and even tail enough after all?); (ii) which moments need second-order input
   (`m₁, m₂, m₃, m₄` — is `m₅` needed beyond its leading rate?); (iii) `⟨φ⟩` to `O(t⁻²)` from the `y⁴` expansion; (iv) the ratio step.
   Please recompute `c'` independently and give `n₁`, `d₁` explicitly.
2. Is there a shortcut via the Stein identity for the *localised* measure (`ℓ_loc' = ℓ' + (g/t)(x − x₀)`, so `⟨ℓ'⟩_loc = −(g/t)⟨x − x₀⟩_loc`,
   i.e. `λ⟨x⟩_loc + (α/2)⟨x²⟩_loc + (γ/6)⟨x³⟩_loc = −(g/t)(⟨x⟩_loc − x₀)`), giving `⟨x⟩_loc` from `⟨x²⟩_loc`, `⟨x³⟩_loc` — would that
   reduce the order needed (`⟨x²⟩_loc` to `t⁻²`, `⟨x³⟩_loc` to `t⁻²`) and avoid the degree-11 polynomial? Which route is cheaper in Lean?
3. For B: the displayed `P_t`'s own `1/t²` coefficient and the resulting vector `meanShift₂,loc`; wording; pitfalls; vote.
