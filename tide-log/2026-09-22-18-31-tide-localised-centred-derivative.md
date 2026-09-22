# Tide: localised-centred-derivative

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); GPT's top pick after tide 79: the centred covariance derivative on E2's exact localised measure.
**Seabed:** laplace, commit 320e06d (worktree `laplace-tide-localised-centred-derivative`, branch `tide/localised-centred-derivative`
off `main`; main was repaired mid-tide — see the Result)
**Started:** 2026-09-22T18:34Z

## Candidates v1 (Claude)

Setting as in tides 65–79: E2's rotated separable oscillator with E3's isotropic localiser (`u = Qᵀ(w − c)`, `u₀ = Qᵀ(w₀ − c)`,
`cᵢ = −αᵢ/(2λᵢ²) + g u₀ᵢ/λᵢ`), `⟨·⟩_loc`, `Cov_loc` on the localised rotated measure at `s`, `L∘A` the unlocalised energy, `μᵢ(s) = ⟨uᵢ⟩_loc(s)`.
The note's eq:cov is the *centred* covariance `Cov_loc(wⱼ, wₖ)`; tides 68/74 gave it to second order on the exact localised measure
(`Cov_loc(uᵢ, uⱼ) = δᵢⱼ Var_loc(uᵢ)` exactly, `t·Var_loc(uᵢ) = 1/λᵢ + vᵢ/t + O(t⁻²)`, `vᵢ = varLocCoeff2 = c₂',ᵢ − cᵢ²`). Tide 77 gave the exact
derivative identity for expectations of fixed probes; tides 78/79 the second-order eq:covK for *raw* probes, where the off-diagonal
pairs contribute `2cᵢcⱼ/t`. GPT (tide 79) pointed out that for the centred covariance those terms cancel and asked for this tide.

### A. The exact derivative identity for the centred covariance

For each frame coordinate, `−d/ds Var_loc(uᵢ)(s) = Cov_loc[L∘A, uᵢ²] − 2μᵢ Cov_loc[L∘A, uᵢ]` at `s = t > 0` (`hasDerivAt_localised_frame_var`,
`localisedVar_frame_eq_neg_deriv`): from tide 77's frame derivative lemma for `ψ = uᵢ^m` (`m = 1, 2`; integrability of `L uᵢ^m e^{−(t/2)L}` from
`integrable_energy_coord_pow_separableAnharmonic`), the rotation lemmas, and the product rule on `Var = ⟨uᵢ²⟩ − ⟨uᵢ⟩²`. Off the diagonal
`Cov_loc(uᵢ, uⱼ) = 0` for all `s` (tide 68), so its derivative vanishes, and consistently the exact pair identity (tide 76) gives
`Cov_loc[L∘A, uᵢuⱼ] − μⱼ Cov_loc[L∘A, uᵢ] − μᵢ Cov_loc[L∘A, uⱼ] = 0` (`centred_pair_offdiag_zero`): the raw pair covariance `2cᵢcⱼ/t` is
exactly the mean-product term. In physical coordinates `Cov_loc(wⱼ, wₖ) = ∑ᵢ QⱼᵢQₖᵢ Var_loc(uᵢ)` (tide 68) gives
`−d/ds Cov_loc(wⱼ, wₖ) = ∑ᵢ QⱼᵢQₖᵢ (Cov_loc[L∘A, uᵢ²] − 2μᵢ Cov_loc[L∘A, uᵢ])` (`hasDerivAt_localised_cov_coord`).

### B. The centred covariance derivative to second order

`|t²(Cov_loc[L∘A, uᵢ²] − 2μᵢ Cov_loc[L∘A, uᵢ]) − 1/λᵢ − 2vᵢ/t| ≤ K/t²` (`localisedVar_neg_deriv_order2_rate`): from tide 79's
`|t²Cov_loc[L∘A, uᵢ²] − 1/λᵢ − 2c₂',ᵢ/t| ≤ K/t²`, `t μᵢ → cᵢ` and `t²Cov_loc[L∘A, uᵢ] → cᵢ` at rate `1/t`, `prod_rate`, and `2c₂' − 2c² = 2v`.
Hence **`t²(−∂ₜ Cov_loc(wⱼ, wₖ)) = (H⁻¹)ⱼₖ + 2(∑ᵢ QⱼᵢQₖᵢ vᵢ)/t + O(t⁻²)`** (`localisedCov_neg_deriv_order2_rate`; `(H⁻¹)ⱼₖ = ∑ᵢ QⱼᵢQₖᵢ/λᵢ`,
`conj_diagonal_inv_apply`) — twice the second-order coefficient of tide 74's `Cov_loc(wⱼ, wₖ) = Sⱼₖ + (∑ᵢ QⱼᵢQₖᵢ(vᵢ + g/λᵢ²))/t² + O(t⁻³)`
modulo the displayed `S`'s own expansion: the derivative reading holds for the note's *centred* eq:cov coefficientwise through
second order, with the off-diagonal raw terms gone.

### C. Reading

The centred covariance tensor's negative time derivative is, to second order and in physical coordinates, `H⁻¹/t² + 2Q diag(vᵢ)Qᵀ/t³`;
the raw eq:covK's off-diagonal `∑_{i≠j} B̃ᵢⱼcᵢcⱼ` (§84) is the mean-product term `μᵀBμ`'s derivative and cancels on centring; the diagonal
`2c₂'` becomes `2(c₂' − c²)`. (Remark; the theorems are A and B.)

Proposed bundle: A + B. Line estimate ~450.

Numerical check (`numcheck_localised_centred_derivative.py`, 1D quadrature, `λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`): central differences
of `Var_loc(t)` vs `Cov[ℓ, x²] − 2m₁Cov[ℓ, x]` agree to `10⁻⁹`–`10⁻¹²`; `t(t²(−∂ₜVar_loc) − 1/λ) = −1.226, −1.362, −1.398, −1.407` at
`t = 10, 40, 160, 640` vs `2v' = −1.410175`.

## Numerical check

`numcheck_localised_centred_derivative.py`: central differences of `Var_loc(t)` vs the exact `Cov[ℓ, x²] − 2m₁Cov[ℓ, x]` agree to
`5·10⁻⁹`–`2·10⁻¹²`; `t(t²(−∂ₜVar_loc) − 1/λ) → −1.407` vs `2v' = −1.410175` (`t = 640`).

## GPT-6 Astra v1

Verbatim in `gpt_localised_centred_derivative_v1.md` (prompt: `gpt_localised_centred_derivative_prompt_v1.md`). Summary: A and B correct
(fixed `g, w₀, Q`): `−∂ₜVar_loc(uᵢ) = Cov_loc(L, uᵢ²) − 2μᵢCov_loc(L, uᵢ)`, and more generally
`−∂ₜCov_loc(uᵢ, uⱼ) = Cov_loc(L, uᵢuⱼ) − μⱼCov_loc(L, uᵢ) − μᵢCov_loc(L, uⱼ)`, which vanishes *exactly* off the diagonal by the pair identity;
the product estimate `|aᵢbᵢ − cᵢ²| ≤ |cᵢ|(A + B)/t + AB/t²`; the rotated tensor statement. Wording corrections: `2cᵢcⱼ/t` is the leading
off-diagonal term of the `t²`-*scaled* raw covariance (unscaled `2cᵢcⱼ/t³`); the exact equality is with the two mean–covariance products,
not their leading coefficients; the mean-product contribution is `−∂ₜ(μᵀB̃μ)`; "off-diagonal terms vanish" refers to the separable
`u`-frame (physical-coordinate off-diagonal entries generally remain after rotation). **Normalisation check**: with `V = Q diag(vᵢ)Qᵀ`,
`D = V + gH⁻²`, tide 74's `C(t) = S(t) + D/t² + O(t⁻³)` and `S = H⁻¹/t − gH⁻²/t² + O(t⁻³)` give the *total* `t⁻²` coefficient `V`, and
`−∂ₜC(t) = SHS + 2D/t³ + O(t⁻⁴) = H⁻¹/t² + 2V/t³ + O(t⁻⁴)` — matches B (sign positive since `−∂ₜ(t⁻²) = 2t⁻³`); "twice the coefficient"
refers to the total covariance coefficient, not the displayed correction `D` alone. Do not justify B by differentiating tide 74's
remainder. Suggested note wording recorded in the file. **Next target**: the invariant centred quadratic-probe theorem
`−∂ₜ tr(B C(t)) = tr(BH⁻¹)/t² + 2tr(BV)/t³ + O(t⁻⁴)` with the exact bridge `−∂ₜ tr(BC(t)) = Cov_loc(L, (w − m(t))ᵀB(w − m(t)))` (the probe
depends on `t`: prove by expanding the centred quadratic, not by the fixed-probe lemma).

## Vote
- Claude: A + B, C as remark in GPT's wording
- GPT-6 Astra: "accept A + B; retain C as an explanatory remark after correcting the scaling, derivative sign wording, and frame
  qualification"
