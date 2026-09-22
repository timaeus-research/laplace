# Tide: localised-covK-order2

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); tide 77's follow-up: the second-order localised eq:covK through the Stein–covariance reduction.
**Seabed:** laplace, commit acda0e3 (worktree `laplace-tide-localised-covK-order2`, branch
`tide/localised-covK-order2` off `tide/localised-derivative` — a linear chain, for `stein_loc_cov_reduction`)
**Started:** 2026-09-22T18:00Z

## Candidates v1 (Claude)

Setting as in tides 65–77 (1D anharmonic oscillator `ℓ`, isotropic localiser `g ≥ 0`, anchor `x₀`, `a = g x₀`, `φ = e^{ax − (g/2)x²}`,
`⟨·⟩_loc`, `m_j = ⟨x^j⟩_loc`, `C_{r,n} = Cov_loc[x^r, xⁿ]`). Tide 77 proved the exact localised Stein–covariance reduction
`t²Cov_loc[ℓ, xⁿ] = (n/2)t m_n − (α/12)t²C_{3,n} − (γ/24)t²C_{4,n} − (g/2)tC_{2,n} + (a/2)tC_{1,n}` (`stein_loc_cov_reduction`), and the
localised moments known so far are: `t m₁ = c + c'/t + O(t⁻²)` (tide 72, `c = −α/(2λ²) + a/λ`, `c' = meanLocCoeff2`),
`t m₂ = 1/λ + c₂'/t + O(t⁻²)` (tide 73, `c₂' = locSecondCoeff2`), `t²m₃ → c₃' = −5α/(2λ³) + 3a/λ²` and `t²m₄ → 3/λ²` at `K/t` (tide 73),
`|t³m₅| ≤ K`, `|t³m₆| ≤ K` (tide 76). The seabed's unlocalised inputs: `fourthMoment_order2_rate`
(`t²⟨x⁴⟩ = 3/λ² + C₄/t + O(t⁻²)`, `C₄ = 25α²/(2λ⁵) − 4γ/λ⁴`), `fifthMoment_lead` (`t³⟨x⁵⟩ → c₅ = −35α/(2λ⁴)`, `K/t`),
`evenMoment_anharmonic_rate 3` (`t³⟨x⁶⟩ → 15/λ³`, `K/t`), `oddMoment_anharmonic_rate 3` (`|t⁴⟨x⁷⟩ + 105α/(6λ⁵)| ≤ K/t`, so `t⁴⟨x⁷⟩` bounded),
`evenMoment_bound k`, tide 72's `locDenominator_rate2` (`⟨φ⟩ = 1 + d₁/t + O(t⁻²)`) and `ratio_key`, tide 73's shared expansion
`locSquare_pointwise` (`|x²φ − (x² + ax³ + p₃x⁴ + p₄x⁵)| ≤ H₆x⁶ + H₈x⁸ + H₁₀x¹⁰`) and tide 76's `locFifth_expansion`
(`|⟨x⁵φ⟩ − (⟨x⁵⟩ + a⟨x⁶⟩)| ≤ N₆⟨x⁶⟩ + … + N₁₄⟨x¹⁴⟩`), tide 75's `prod_rate`.

### A. The localised fourth moment to second order

`|t²m₄ − 3/λ² − c₄'/t| ≤ K/t²` with **`c₄' = n₄ − 3d₁/λ²`, `n₄ = C₄ + a c₅ + 15p₃/λ³`**, i.e.
`c₄' = (25α² − 32aαλ + 12a²λ² − 12gλ² − 8γλ)/(2λ⁵)` (sympy). Route: `x⁴φ = x⁴ + ax⁵ + p₃x⁶ + p₄x⁷ + x²R` with `|x²R| ≤ H₆x⁸ + H₈x¹⁰ + H₁₀x¹²`
(the shared expansion times `x²`, keeping the degree-6 and -7 monomials exact — tide 73's `locQuartic_pointwise2` put them in the envelope);
`t²⟨x⁴φ⟩ = t²⟨x⁴⟩ + a(t³⟨x⁵⟩)/t + p₃(t³⟨x⁶⟩)/t + p₄(t⁴⟨x⁷⟩)/t² + t²⟨x²R⟩` gives `|t²⟨x⁴φ⟩ − 3/λ² − n₄/t| ≤ K/t²`, then `ratio_key`
with `c = 3/λ²`, `d₁ = locD1` (this is tide 72's numerator pattern one degree up).

### B. The localised fifth and sixth moments at leading order with rates

`|t³m₅ − (c₅ + 15a/λ³)| ≤ K/t` (from `locFifth_expansion`: `t³⟨x⁵φ⟩ = t³⟨x⁵⟩ + a t³⟨x⁶⟩ + O(1/t)`, then the leading-order division
`loc_ratio_lead`-style with `D = 1 + O(1/t)`) and `|t³m₆ − 15/λ³| ≤ K/t` (`x⁶φ = x⁶ + ax⁷ − (g/2)x⁸ + x⁶R₂`, `|x⁶R₂| ≤ C(x⁸ + x¹⁰)`, the
signed `x⁷` by `oddMoment_anharmonic_rate 3`). Sympy: `t³m₅ → 5(−7α + 6aλ)/(2λ⁴)`, `t³m₆ → 15/λ³`.

### C. eq:covK on the localised measure to second order — the derivative reading at second order

`|t²Cov_loc[ℓ, x] − c − 2c'/t| ≤ K/t²` and `|t²Cov_loc[ℓ, x²] − 1/λ − 2c₂'/t| ≤ K/t²` (`localisedCovK_lin_order2_rate`, `localisedCovK_sq_order2_rate`),
from the reduction with the inputs A, B and tides 72/73: for `n = 1`, `t²C_{3,1} = t²m₄ − (t²m₃)(tm₁)/t`, `t²C_{4,1} = (t³m₅)/t − (t²m₄)(tm₁)/t`,
`tC_{2,1} = (t²m₃)/t − (tm₂)(tm₁)/t`, `tC_{1,1} = tm₂ − (tm₁)²/t`; for `n = 2`, `t²C_{3,2} = (t³m₅)/t − (t²m₃)(tm₂)/t`, `t²C_{4,2} = (t³m₆)/t − (t²m₄)(tm₂)`,
`tC_{2,2} = (t²m₄)/t − (tm₂)²/t`, `tC_{1,2} = (t²m₃)/t − (tm₁)(tm₂)/t`. The coefficient identities (`covKLocCoeff2Lin_eq : … = 2·meanLocCoeff2`,
`covKLocCoeff2Sq_eq : … = 2·locSecondCoeff2`) are pure algebra, verified by sympy: **the `1/t` coefficients are exactly `2c'`, `2c₂'`** — the
derivative reading `Cov_loc = −∂ₜ⟨·⟩_loc` (tide 77, exact) holds coefficientwise at second order, as `C' = 2B` did unlocalised (tide 71),
with the localiser's `−g/2`, `+a/2` reduction terms and the anchor all accounted for. Probe form for `(B/2)x² + bx`.

### D. E2 (optional): the rotated localised eq:covK to second order

With tide 76's frame pair identity `Cov_loc[L∘A, uᵢuⱼ] = ⟨uⱼ⟩_loc Cov_loc,i[ℓᵢ, x] + ⟨uᵢ⟩_loc Cov_loc,j[ℓⱼ, x]` and tide 75's `prod_rate`:
`|t²Cov_loc[L∘A, uᵢuⱼ] − 2cᵢcⱼ/t| ≤ K/t²` (`i ≠ j`, `cᵢ` the localised leading means), the diagonal terms from C, and the quadratic-probe
assembly as in tide 75: `t²Cov_loc[L∘A, ψ] = C_loc + C'_loc/t + O(t⁻²)` with `C'_loc = ∑ᵢ (B̃ᵢᵢ·2c₂',ᵢ/2 + b̃ᵢ·2c'ᵢ) + ∑_{i≠j} B̃ᵢⱼ cᵢcⱼ`.
Include if A–C land within the tide; otherwise the next tide.

Proposed bundle: A + B + C (+ D if cheap). Line estimate ~800 (A ~300, B ~200, C ~300).

Numerical check (`numcheck_localised_covK_order2.py`, sympy Wick expansion with the localiser inside the perturbation, `ε = 1/√t`, moments to
`ε⁶`): the reduction's `1/t` coefficients equal `2c'` (n = 1) and `2c₂'` (n = 2) identically in `λ, α, γ, g, x₀`; `t²m₄`'s `1/t` coefficient is
`(25α² − 32aαλ + 12a²λ² − 12gλ² − 8γλ)/(2λ⁵)` = `n₄ − 3d₁/λ²`; `t³m₅ → −35α/(2λ⁴) + 15a/λ³`, `t³m₆ → 15/λ³`. Quadrature (tide 76's check):
`t(t²Cov_loc[ℓ, x] − c) → 0.1487` vs `2c' = 0.150301`, `t(t²Cov_loc[ℓ, x²] − 1/λ) → −1.3544` vs `2c₂' = −1.357602` at `t = 640`.

## Numerical check

`numcheck_localised_covK_order2.py`: sympy (moments to `ε⁶`) — the reduction's `1/t` coefficients equal `2c'`, `2c₂'` identically;
`c₄'`, the leading `t³m₅`, `t³m₆` as stated; tide 76's quadrature (`t = 640`): `0.1487` vs `2c' = 0.150301`, `−1.3544` vs `2c₂' = −1.357602`.

## GPT-6 Astra v1

Verbatim in `gpt_localised_covK_order2_v1.md` (prompt: `gpt_localised_covK_order2_prompt_v1.md`). Summary: the coefficients of A–C are
right — `c₄'` re-derived, the bookkeeping for `n = 1` (`K₁ = c'/2 − (α/12)(q₄ − sc) − (γ/24)(v − qc) − (g/2)(s − bc) + (a/2)(c₂' − c²) = 2c'`)
and `n = 2` (`K₂ = c₂' − (α/12)(v − sb) − (γ/24)(w − qb) − (g/2)(q − b²) + (a/2)(s − cb) = 2c₂'`) written out and confirmed
(`b = 1/λ`, `q = 3/λ²`, `s = c₃'`, `v`, `w` the fifth/sixth leading coefficients). **Two proof corrections**: (i) the candidates' `t²C_{4,2}`
lost a `1/t` (correct: `t²C_{4,2} = (t³m₆)/t − (t²m₄)(tm₂)/t`) — a typo in the text, not in the plan; (ii) **B's fifth moment cannot use
tide 76's `locFifth_expansion`**: its envelope starts at `N₆⟨x⁶⟩ = O(t⁻³)`, so `t³·` gives `O(1)`, not `O(1/t)` — keep `p₃x⁷ + p₄x⁸` exact
(`x⁵φ = x⁵ + ax⁶ + p₃x⁷ + p₄x⁸ + x³R`, `|x³R| ≤ H₆|x|⁹ + H₈|x|¹¹ + H₁₀|x|¹³`, all `O(t⁻⁴)`) with the signed seventh moment bounded. Input table:
`n = 1` needs `M₁, M₂, M₄` to second order and `M₃, M₅` at leading rate; `n = 2` needs `M₂` to second order only, and `M₃, M₄, M₅, M₆`
at leading rate — so A is needed for the linear result, not the square one. Cautions: A uses the *unlocalised* `t⁴⟨x⁷⟩` (from
`oddMoment_anharmonic_rate 3`; its leading coefficient is `−(α/6)·9‼/λ⁵ = −945α/(6λ⁵)`, the candidates' `105` was a typo — only
boundedness is used); products need `prod_rate`'s `O(1/t)` error, not mere boundedness. Wording: "for the fixed isotropic localiser,
the localised covK expansions for linear and quadratic *raw* probes agree through the `t⁻³` covariance term with the coefficientwise
negative `t`-derivatives of their expectation expansions; the scaled `1/t` coefficients are `2c'`, `2c₂'`"; the localiser already enters
the leading linear coefficient through `c`; for the *variance* the coefficient is `2(c₂' − c²)` (`−∂ₜVar = Cov[ℓ, x²] − 2m₁Cov[ℓ, x]`).
D correct (`t²Cov_loc[L∘A, uᵢuⱼ] = 2cᵢcⱼ/t + O(t⁻²)`, `C'_loc = ∑ᵢ(B̃ᵢᵢc₂',ᵢ + 2b̃ᵢc'ᵢ) + ∑_{i≠j} B̃ᵢⱼcᵢcⱼ`, ordered pairs), "bundle only if
genuinely cheap".

## Vote
- Claude: A + B + C with GPT's fifth-moment repair (exact to degree eight); D if it fits
- GPT-6 Astra: "approve A–C with the two proof corrections and the seventh-moment coefficient audit; bundle D only if the existing
  assembly makes it genuinely cheap"

## Result

Commit `91ab805` on `tide/localised-covK-order2`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/LocalisedCovKOrder2.lean` (    1288 lines).
A + B + C as voted (D, the rotated E2 pairs `2cᵢcⱼ`, left as the next step).
Theorems: `locQuartic_pointwise4`, `locU₈`…`locU₁₄`, `locFifth_pointwise4`, `locS₈`/`locS₁₀`, `locSixth_pointwise`,
`locQuartic_expansion4`, `locFifth_expansion4`, `locSixth_expansion`, `locN4`, `locFourthCoeff2` (+`_eq`), `locFifthCoeff`,
`locQuartic4_assembly`, `locFifth_lead_assembly`, `locSixth_lead_assembly`, `ratio_key2`, `ratio_lead3_key`, `seventhMoment_bound`,
`eighthMoment_bound`, `locQuartic_rate4`, `locFifth_rate`, `locSixth_rate`, `loc_ratio_lead3_rate`, `locFourthMoment_loc_rate4` (A),
`locFifthMoment_loc_rate`, `locSixthMoment_loc_rate` (B), `covKLocCoeff2Lin` (+`_eq` `= 2·meanLocCoeff2`), `covKLocCoeff2Sq`
(+`_eq` `= 2·locSecondCoeff2`), `covK_loc_lin_order2_assembly`, `covK_loc_sq_order2_assembly`, `stein_loc_cov_reduction_lin/_sq`,
`locMean_loc_order2`, `localisedCovK_lin_order2_rate`, `localisedCovK_sq_order2_rate` (C).

Surprises: GPT caught that tide 76's fifth-moment envelope (from `x⁶`) is `O(1)` after `t³`, so the degree-eight exact expansion was
needed; a hand-computed sixth-moment envelope constant was off by the `2²` of `abs_locExponent_pow_le` (the `ring` residual showed it);
`unfold` needs outer definitions listed before inner ones. The two coefficient identities `K₁ = 2c'`, `K₂ = 2c₂'` closed by
`field_simp; ring` once all definitions were unfolded.
