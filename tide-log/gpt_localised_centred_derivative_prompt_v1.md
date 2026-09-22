You are GPT-6 Astra consulting on a Lean 4 + Mathlib formalisation tide ("laplace" seabed: Laplace asymptotics of Gibbs expectations for
the quartic anharmonic oscillator with the isotropic Gaussian localiser of a research note's E3). In the previous consult you asked for
the centred covariance derivative on E2 as the highest-priority next target. Below are the candidates. Please answer:

1. Are A and B correct? Check the exact identity `−∂ₜVar_loc(uᵢ) = Cov_loc[L, uᵢ²] − 2μᵢCov_loc[L, uᵢ]` (product rule on `⟨uᵢ²⟩ − ⟨uᵢ⟩²` with
   `∂ₜ⟨ψ⟩_loc = −Cov_loc[L, ψ]` for fixed `ψ`), the vanishing of the off-diagonal expression via the exact pair identity, the second-order
   coefficient `2vᵢ = 2(c₂',ᵢ − cᵢ²)`, and the rotated tensor statement. Remainder bookkeeping pitfalls (products `(tμᵢ)(t²Cov_loc[L, uᵢ])`)?
2. Is C's reading right, and how should the note's eq:cov paragraph be worded (the derivative of the *centred* covariance vs the raw
   second moment; the claim "for the centred covariance the off-diagonal second-order terms vanish")? Is the sign/normalisation of
   "twice tide 74's coefficient" right — tide 74 gives `Cov_loc(wⱼ, wₖ) = Sⱼₖ + (∑ᵢ QⱼᵢQₖᵢ(vᵢ + g/λᵢ²))/t² + O(t⁻³)` with `S = (tH + gI)⁻¹`,
   whose own `t⁻²` coefficient is `−g(H⁻²)ⱼₖ`; please write `−∂ₜCov_loc(wⱼ, wₖ)` through `t⁻³` from that expansion and confirm it matches B.
3. What is the best next target after this in the E3 arc, in your view?
4. Vote.

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
