You are GPT-6 Astra consulting on a Lean 4 + Mathlib formalisation tide ("laplace" seabed: Laplace asymptotics of Gibbs expectations for
the quartic anharmonic oscillator with the isotropic Gaussian localiser of a research note's E3). In the previous consult you proposed
the exact localised Stein–covariance reduction (now formalised) and listed the moment inputs for the second-order localised eq:covK.
Below are the candidates for the tide that carries it out. Please answer:

1. Are A, B, C correct? Check independently `c₄' = n₄ − 3d₁/λ²` with `n₄ = C₄ + ac₅ + 15p₃/λ³` (`C₄ = 25α²/(2λ⁵) − 4γ/λ⁴`,
   `c₅ = −35α/(2λ⁴)`, `p₃ = (a² − g)/2`, `d₁ = −aα/(2λ²) + p₃/λ`), the leading `t³m₅ → c₅ + 15a/λ³`, `t³m₆ → 15/λ³`, and — the main point — that
   the reduction with these inputs gives exactly `2c'` and `2c₂'` as the `1/t` coefficients (`c'`, `c₂'` the second-order coefficients of
   `t m₁`, `t m₂`; write out the bookkeeping for `n = 1` and `n = 2` and confirm the identity, or find the mistake).
2. Remainder bookkeeping: each pair covariance `t^k C_{r,n}` is a difference of products of scaled moments divided by powers of `t`; list
   for `n = 1, 2` which factors need second order and which only leading order with rate, so we allocate the right lemmas. Is `t⁴m₇`
   bounded (needed for `p₄x⁷` in A) available from `oddMoment_anharmonic_rate 3`? Pitfalls?
3. Wording against the note (E3/Setup): "on the exact localised measure eq:covK is `−∂ₜ` of eq:mean/eq:cov coefficientwise through
   second order, the localiser entering the `1/t` coefficient through `2c'`, `2c₂'`" — fair? Anything the note could claim from this?
4. Is D (the rotated E2 second order with pair terms `2cᵢcⱼ`) right, and worth bundling? Vote.

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
