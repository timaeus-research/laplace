You are GPT-6 Astra consulting on a Lean 4 + Mathlib formalisation tide ("laplace" seabed: Laplace asymptotics of Gibbs expectations
for the quartic anharmonic oscillator with the isotropic Gaussian localiser of a research note's E3; eq:mean and eq:cov are the note's
displayed formulas `⟨w⟩ − w* = −½S(tT:S) + γS(w₀ − w*) + O(S²)` and `Cov = S + O(S²)` with `S = (tH + γI)⁻¹`). Below are the candidates
for the next tide with the seabed's available lemmas. Please answer:

1. Are A, B, C, D correct as stated? Check independently (not just trusting our sympy): `v' = c₂' − c² = α²/λ⁴ − aα/λ³ − g/λ² − γ/(2λ³)`
   (with `c₂' = n₂ − d₁/λ`, `n₂ = B₂ + ac₃ + 3p₃/λ²`, `d₁ = −aα/(2λ²) + p₃/λ`, `p₃ = (a² − g)/2`, `c₃ = −5α/(2λ³)`,
   `B₂ = 5α²/(4λ⁴) − γ/(2λ³)`, `c = −α/(2λ²) + a/λ`), `v' + g/λ² = α²/λ⁴ − γ/(2λ³) − aα/λ³`, the `t⁻²` coefficient `c'_S = αg/λ³ − ag/λ²`
   of `P_t = −αt/(2(tλ + g)²) + a/(tλ + g)`, and `r = c' − c'_S = B₁ + aα²/λ⁴ − aγ/(2λ³) − αa²/(2λ³)` with `B₁ = −5α³/(8λ⁵) + 2αγ/(3λ⁴)`.
   Check the remainder bookkeeping: from `|t⟨x⟩_loc − c − c'/t| ≤ K/t²` and `|t⟨x²⟩_loc − 1/λ − c₂'/t| ≤ K/t²` (both eventually, `t ≥ T ≥ 1`),
   is `|t Var_loc − 1/λ − v'/t| ≤ K/t²` immediate, and are the unscaled `K/t³` statements right?
2. Is D's reading fair: "with the anchor at the minimiser the displayed eq:mean and eq:cov with `S = (tH + γI)⁻¹` absorb the localiser
   exactly through second order — their `O(S²)` terms are the unlocalised second-order coefficients, independent of `γ`"? Is there a
   structural reason (e.g. the localiser at the minimiser being a pure quadratic added to `tℓ`, so it only shifts `tλ → tλ + g` in the
   Gaussian part) that makes this obvious, or a hidden `g`-dependence at the next order? Any pitfalls in wording against the note?
3. Is there a better or additional candidate close to this seabed (e.g. the E2 rotated eq:covK second order with the off-diagonal pair
   terms `2∑_{i<j} B̃ᵢⱼaᵢaⱼ`, left from an earlier tide; or eq:covK under localisation)? Which single bundle do you back?
4. Vote.

## Candidates v1 (Claude)

Setting as in tides 65–73 (1D anharmonic oscillator `ℓ = (λ/2)x² + (α/6)x³ + (γ/24)x⁴`, `λ, γ > 0`, `α² < 3λγ`; isotropic localiser
`g ≥ 0`, anchor `x₀`, `a = g x₀`, `φ = e^{ax − (g/2)x²}`, `⟨·⟩_loc = ⟨·φ⟩/⟨φ⟩`; E2's rotated separable oscillator `w = c + Qu`,
frame anchor `u₀ = Qᵀ(w₀ − c)`, `S = (tH + gI)⁻¹`, `H = Q diag(λ) Qᵀ`).

Seabed state. Second-order localised results now available in 1D: the mean `|t⟨x⟩_loc − c − c'/t| ≤ K/t²`
(`localisedMean_order2_rate`, tide 72; `c = −α/(2λ²) + a/λ`, `c' = meanLocCoeff2 = B₁ + aα²/λ⁴ − aγ/(2λ³) + αg/λ³ − αa²/(2λ³) − ag/λ²`),
the second moment `|t⟨x²⟩_loc − 1/λ − c₂'/t| ≤ K/t²` (`locSecondMoment_loc_rate2`, tide 73; `c₂' = locSecondCoeff2 = n₂ − d₁/λ`,
`n₂ = B₂ + ac₃ + 3p₃/λ²`), `⟨x²⟩_loc = Var_loc + ⟨x⟩_loc²` (`locSecondMoment_eq`), `Var_loc` as a ratio (`localisedVar_eq`). The E2
transports: `⟨wⱼ⟩_loc = cⱼ + ∑ᵢ Qⱼᵢ ⟨uᵢ⟩_loc,i` (`localisedRotatedAnharmonic_ambient_coord`), the displayed right-hand side of eq:mean in
frame form `meanShiftLoc + gS(w₀ − c) = Q (P_t,i)ᵢ` with `P_t = locLeading = −αt/(2(tλ + g)²) + a/(tλ + g)` (`displayed_mean_rot`),
`Cov_loc[wⱼ, wₖ] = ∑ᵢ QⱼᵢQₖᵢ Var_loc,i` (`localisedRotatedAnharmonic_cov_coord`), `Sⱼₖ = ∑ᵢ QⱼᵢQₖᵢ/(tλᵢ + g)` (`locS_rot_apply`), and the
finite-sum transport lemmas `sum_rate_div`, `sum_rate_div_sq`. Tides 67 (§72) and 68 (§73) certified eq:mean's and eq:cov's `O(S²)`
remainders on E2's exact localised measure (`K/t²` per entry) without their coefficients; tide 72 (§77) gave the mean's second-order
coefficient in 1D only. The unlocalised variance's second-order coefficient is `α²/λ⁴ − γ/(2λ³)` (`var_anharmonic_order2_rate`), the
mean's is `B₁ = meanCoeff2`.

### A. The localised variance to second order (1D)

`|t·Var_loc − 1/λ − v'/t| ≤ K/t²` with `v' = c₂' − c² = α²/λ⁴ − aα/λ³ − g/λ² − γ/(2λ³)`, from `t Var_loc = t⟨x²⟩_loc − (t⟨x⟩_loc)²/t`
and the two second-order inputs (`(c + c'/t + O(t⁻²))² = c² + O(1/t)`). Against the displayed `S = 1/(tλ + g)`:
`|Var_loc − 1/(tλ + g) − (v' + g/λ²)/t²| ≤ K/t³` since `1/(λt) − 1/(tλ + g) = g/(λ²t²) − g²/(λ²t²(tλ + g))`, and
**`v' + g/λ² = (α²/λ⁴ − γ/(2λ³)) − aα/λ³`**: eq:cov's `O(S²)` term under localisation is the unlocalised second-order variance
coefficient minus `aα/λ³`.

### B. eq:mean's `O(S²)` coefficient on E2

1D: `|⟨x⟩_loc − P_t − r/t²| ≤ K/t³` with `r = c' − c'_S`, `c'_S = αg/λ³ − ag/λ²` the `t⁻²` coefficient of `P_t`
(`P_t = c/t + c'_S/t² + O(t⁻³)`, algebra as in `locLeading_sub_le`), so
**`r = B₁ + aα²/λ⁴ − aγ/(2λ³) − αa²/(2λ³)`**. E2: `|(⟨w⟩_loc − c − meanShiftLoc − gS(w₀ − c))ⱼ − (∑ᵢ Qⱼᵢ rᵢ)/t²| ≤ K/t³` by
`ambient_coord`, `displayed_mean_rot` and a `sum_rate_div_cube` (copy of `sum_rate_div_sq`). This identifies the `O(S²)` of eq:mean
whose existence §72 certified.

### C. eq:cov's `O(S²)` coefficient on E2

`|Cov_loc[wⱼ, wₖ] − Sⱼₖ − (∑ᵢ QⱼᵢQₖᵢ (v'ᵢ + g/λᵢ²))/t²| ≤ K/t³` by `cov_coord`, `locS_rot_apply`, A and `sum_rate_div_cube`.

### D. Corollary: the anchor at the minimiser

With `w₀ = c` (so `u₀ = 0`, every `aᵢ = 0`): `rᵢ = B₁,ᵢ` and `v'ᵢ + g/λᵢ² = αᵢ²/λᵢ⁴ − γᵢ/(2λᵢ³)` — the `O(S²)` coefficients of eq:mean and
eq:cov on the localised measure are the *unlocalised* second-order coefficients, independent of `g`: **the displayed formulas with
`S = (tH + γI)⁻¹` absorb the localiser exactly through second order** (pure algebra on A–C's coefficients; `affineFrame Q c c = 0`).
For `a ≠ 0` the `g`-dependence enters only through `a = g u₀`: `−aα/λ³` in the variance, `aα²/λ⁴ − aγ/(2λ³) − αa²/(2λ³)` in the mean.

Proposed bundle: A + B + C + D. Line estimate ~500–600 (no new expansions; ratio and transport bookkeeping).

Numerical check (`numcheck_localised_order2_multi.py`, sympy Wick expansion with the localiser inside the perturbation, `ε = 1/√t`; quadrature at
`λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`): `t Var_loc = 1/λ + 0·ε + v'ε² + …` with `v'` exactly `c₂' − c²`;
`P_t`'s `t⁻²` coefficient is exactly `c'_S`; quadrature `t(t Var_loc − 1/λ) = −0.6424, −0.6888, −0.7010, −0.7041, −0.7048` vs
`v' = −0.70509`, `t²(Var_loc − S) → −0.23157` vs `v' + g/λ² = −0.23171`, `t²(⟨x⟩_loc − P_t) → 0.04738` vs `r = 0.047476`
(`t = 10, …, 2560`).
