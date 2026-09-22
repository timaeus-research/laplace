# Tide: localised-covK-order2-multi

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); tide 78's follow-up D: the rotated E2 localised eq:covK to second order and the expectation side.
**Seabed:** laplace, commit 1046e0f (worktree `laplace-tide-localised-covK-order2-multi`, branch
`tide/localised-covK-order2-multi` off `main`)
**Started:** 2026-09-22T18:24Z

## Candidates v1 (Claude)

Setting: E2's rotated separable oscillator with E3's isotropic localiser (`u = Qᵀ(w − c)`, frame anchor `u₀ = Qᵀ(w₀ − c)`, `aᵢ = g u₀ᵢ`,
`cᵢ = −αᵢ/(2λᵢ²) + aᵢ/λᵢ` the localised leading means, `c'ᵢ = meanLocCoeff2`, `c₂',ᵢ = locSecondCoeff2` the 1D second-order coefficients
of tides 72/73), centred quadratic probe `ψ = ½(w − c)ᵀB(w − c) + bᵀ(w − c)`, `B̃ = QᵀBQ`, `b̃ = Qᵀb`; `⟨·⟩_loc`, `Cov_loc` on the
localised rotated measure, `L∘A` the unlocalised energy.

Seabed state. Tide 76: `localisedRotatedAnharmonic_covK_rate` (leading order, `C_loc = ∑ᵢ(B̃ᵢᵢ/(2λᵢ) + b̃ᵢcᵢ)`), the exact frame identities
`localisedCovK_frame_coord` (`Cov_loc[L∘A, uᵢ^m] = Cov_loc,i[ℓᵢ, x^m]`) and `localisedCovK_frame_pair`
(`Cov_loc[L∘A, uᵢuⱼ] = ⟨x⟩_j,loc Cov_loc,i[ℓᵢ, x] + ⟨x⟩_i,loc Cov_loc,j[ℓⱼ, x]`, `i ≠ j`), the split `localisedCovK_quadratic_split`, and
`locMean_loc_leading`. Tide 78: `localisedCovK_lin_order2_rate` (`t²Cov_loc[ℓ, x] = c + 2c'/t + O(t⁻²)`), `localisedCovK_sq_order2_rate`
(`t²Cov_loc[ℓ, x²] = 1/λ + 2c₂'/t + O(t⁻²)`). Tides 72/73/74: the localised mean and second moment to second order, `sum_rate_div_sq`,
`prod_rate`, `sum_rate_div_cube`; the generic `gibbsExpectation_two_coord_separable` (`⟨f(uᵢ)g(uⱼ)⟩ = ⟨f⟩ᵢ⟨g⟩ⱼ` on a separable measure) and
tide 76's `locFamily` bridge (`localisedRotated_gibbsCov_eq`, `separablePotential_locFamily`).

### A. The pair covariances on the localised measure to second order

For `i ≠ j`: `|t²Cov_loc[L∘A, uᵢuⱼ] − 2cᵢcⱼ/t| ≤ K/t²` (`localisedCovK_frame_offdiag_order2_rate`), from the exact pair identity and
`prod_rate` (`(t⟨x⟩_j)(t²Cov_i) → cⱼcᵢ` at rate `1/t`); diagonal: `|t²Cov_loc[L∘A, uᵢ²] − 1/λᵢ − 2c₂',ᵢ/t| ≤ K/t²`,
`|t²Cov_loc[L∘A, uᵢ] − cᵢ − 2c'ᵢ/t| ≤ K/t²` (tide 78 through `frame_coord`); unified `localisedCovK_frame_pair_order2_rate` with
`locCovKPairCoeff2 i j = if i = j then 2c₂',ᵢ else 2cᵢcⱼ`.

### B. eq:covK on E2's exact localised measure to second order

`|t²Cov_loc[L∘A, ψ] − C_loc − C'_loc/t| ≤ K/t²` (`localisedRotatedAnharmonic_covK_order2_rate`) with
**`C'_loc = ∑ᵢ (B̃ᵢᵢ c₂',ᵢ + 2b̃ᵢ c'ᵢ) + ∑_{i≠j} B̃ᵢⱼ cᵢcⱼ`** (`locCovKCoeff2Sep`; closed form of the off-diagonal part `cᵀB̃c − ∑ᵢ B̃ᵢᵢcᵢ²`),
via the split, `sum_rate_div_sq` over `Fin d × Fin d` and `Fin d`, and `probe_affineFrame` — tide 75's assembly on tide 76's frame objects.
The localised analogue of §80: the off-diagonal probe components contribute at second order through products of the leading localised
means `cᵢ` (which carry the anchor).

### C. The derivative reading coefficientwise on E2

`|t⟨ψ⟩_loc − C_loc − (C'_loc/2)/t| ≤ K/t²` (`localisedRotatedAnharmonic_probe_order2_rate`): `⟨ψ⟩_loc = ∑ᵢⱼ(B̃ᵢⱼ/2)⟨uᵢuⱼ⟩_loc + ∑ᵢ b̃ᵢ⟨uᵢ⟩_loc`
with `⟨uᵢ⟩_loc = cᵢ/t + c'ᵢ/t² + O(t⁻³)` (tide 72), `⟨uᵢ²⟩_loc = 1/(λᵢt) + c₂',ᵢ/t² + O(t⁻³)` (tide 73), `⟨uᵢuⱼ⟩_loc = ⟨uᵢ⟩_loc⟨uⱼ⟩_loc = cᵢcⱼ/t² + O(t⁻³)`
(`i ≠ j`, product measure via `gibbsExpectation_two_coord_separable` on the `locFamily` measure). Together with B: on E2 the exact
localised eq:covK is coefficientwise `−∂ₜ` of the exact localised expectation through second order (`C'_loc = 2 × (C'_loc/2)`), the
E2 form of tides 77/78 — the localiser and the anchor enter both sides consistently.

Proposed bundle: A + B + C. Line estimate ~600.

Numerical check (`numcheck_localised_covK_order2_multi.py`, 2D, `λ = (1.3, 0.9)`, `α = (0.7, −0.4)`, `γ = (1.1, 1.5)`, `g = 0.8`, `u₀ = (0.6, −0.3)`,
`B̃ = [[1, ½],[½, 2]]`, `b̃ = (0.3, −0.2)`; 1D quadratures via separability): `C_loc = 1.548316`, `C'_loc = −4.228837` (pair term `2B̃₁₂c₁c₂ = −0.003203`);
`t(t²Cov_loc − C_loc) = −3.261, −3.940, −4.154, −4.210` at `t = 10, 40, 160, 640`; the pair `t·t²Cov_loc[L, u₁u₂] → −0.0068` vs `2c₁c₂ = −0.0064`;
`t(t⟨ψ⟩_loc − C_loc) → −2.108` vs `C'_loc/2 = −2.114`.

## Numerical check

`numcheck_localised_covK_order2_multi.py`: see the candidates' last paragraph — `t(t²Cov_loc − C_loc) → −4.210` vs `C'_loc = −4.2288`, the pair
`→ −0.0068` vs `2c₁c₂ = −0.0064`, the expectation side `→ −2.108` vs `C'_loc/2 = −2.1144` (`t = 640`).

## GPT-6 Astra v1

Verbatim in `gpt_localised_covK_order2_multi_v1.md` (prompt: `gpt_localised_covK_order2_multi_prompt_v1.md`). Summary: A, B, C correct
for fixed `g, w₀, Q`, probe: the pair coefficient `2cᵢcⱼ` (no further localiser correction — it sits in the means and the 1D
covariances); `C'_loc` over **ordered** pairs (`2∑_{i<j}` only for symmetric `B̃`); `⟨uᵢuⱼ⟩_loc = ⟨uᵢ⟩_loc⟨uⱼ⟩_loc` exactly, since
`|w − w₀|² = ∑ᵢ(uᵢ − u₀ᵢ)²` keeps the product structure in the frame; the expectation side's second coefficient is `C'_loc/2`.
Pitfalls: A needs `O(1/t)` *rates* of the scaled factors (mere limits give `o(1/t)`); constants depend on `g, u₀, d, Q, B, b`; the probe
is centred (`ψ(c) = 0`). Derivative reading: fair as "independently established expansions whose coefficients agree through second
order" — not by differentiating C's `O(t⁻³)` remainder. **Centred correction worth adding**: with `vᵢ = c₂',ᵢ − cᵢ²`,
`Var_loc(uᵢ) = 1/(λᵢt) + vᵢ/t² + O(t⁻³)`, `Cov_loc(uᵢ, uⱼ) = 0` exactly off the diagonal, and the exact identity
`−∂ₜVar_loc(uᵢ) = Cov_loc[L, uᵢ²] − 2⟨uᵢ⟩_loc Cov_loc[L, uᵢ]` gives `t²(−∂ₜCov_loc(uᵢ, uⱼ)) = δᵢⱼ(1/λᵢ + 2(c₂',ᵢ − cᵢ²)/t) + O(t⁻²)` — the raw
off-diagonal `2cᵢcⱼ` cancels on centring, the diagonal `2c₂'` becomes `2(c₂' − c²)` (= `2·varLocCoeff2`, tide 74). Open after A–C: the
centred covariance tensor rotated to physical coordinates (highest priority for the note's eq:cov), uniformity in `g`/anchor,
nonseparable `d`-dimensional potentials ("product factorisation is doing substantial work"), third order (next off-diagonal expectation
coefficient `c'ᵢcⱼ + cᵢc'ⱼ`, covariance `3(c'ᵢcⱼ + cᵢc'ⱼ)`).

## Vote
- Claude: A + B + C (ordered-pair bookkeeping as written); the centred variance derivative as the next tide
- GPT-6 Astra: "YES to A+B+C, with explicit ordered-pair bookkeeping and no differentiation of bare remainder bounds; prioritise the
  centred E2 covariance tensor next"
