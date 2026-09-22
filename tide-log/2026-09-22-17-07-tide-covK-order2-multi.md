# Tide: covK-order2-multi

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); tide 71's follow-up C: E2's rotated eq:covK to second order with the off-diagonal pair terms.
**Seabed:** laplace, commit b866486 (worktree `laplace-tide-covK-order2-multi`, branch `tide/covK-order2-multi` off `main`)
**Started:** 2026-09-22T17:09Z

## Candidates v1 (Claude)

Setting: E2's rotated separable anharmonic oscillator, `L∘A` with `A w = u = Qᵀ(w − c)`, `L(u) = ∑ᵢ ℓᵢ(uᵢ)`,
`ℓᵢ = (λᵢ/2)x² + (αᵢ/6)x³ + (γᵢ/24)x⁴` (`λᵢ, γᵢ > 0`, `αᵢ² < 3λᵢγᵢ`), no localiser. Probe `ψ = ½(w − c)ᵀB(w − c) + bᵀ(w − c)`, frame form
`ψ = ∑ᵢⱼ (B̃ᵢⱼ/2)uᵢuⱼ + ∑ᵢ b̃ᵢuᵢ` with `B̃ = QᵀBQ`, `b̃ = Qᵀb`. Write `aᵢ = −αᵢ/(2λᵢ²)` (the leading `t⟨uᵢ⟩`), `C'_sq,i = 2B₂,ᵢ`,
`C'_lin,i = 2B₁,ᵢ` (tide 71's `covKCoeff2Sq/Lin`).

Seabed state. eq:covK for E2 at leading order with rate: `covK_separable_quadratic_rate`
(`|t²Cov[L, ψ̃] − ∑ᵢ(B̃ᵢᵢ/(2λᵢ) − b̃ᵢαᵢ/(2λᵢ²))| ≤ K/t`), built from `gibbsCov_energy_quadratic_split`
(`Cov[L, ψ̃] = ∑_{p : ι×ι} (B̃_p/2) Cov[L, u_{p.1}u_{p.2}] + ∑ᵢ b̃ᵢ Cov[L, uᵢ]`), `covK_separable_pair_rate`
(`|t²Cov[L, uᵢuⱼ] − (if i = j then 1/λᵢ else 0)| ≤ K/t`), `covK_separable_lin_rate`, the exact reductions
`gibbsCov_energy_coord_pow_separableAnharmonic` (`Cov[L, uᵢ^m] = Cov_i[ℓᵢ, x^m]`) and
`gibbsCov_energy_pair_separableAnharmonic` (`i ≠ j`: `Cov[L, uᵢuⱼ] = ⟨xⱼ⟩ Cov_i[ℓᵢ, x] + ⟨xᵢ⟩ Cov_j[ℓⱼ, x]`), and the ambient transport
`covKFormula_rot_rate` (`|Cov[L∘A, ψ] − covKFormula t H T B b| ≤ K/t³`, using `covKFormula = C/t²` in the frame,
`covKFormula_rot`) and its relative form `covKFormula_rot_ratio_rate`. In 1D, tide 71 (§76) gave the second order:
`covK_sq_order2_rate` (`|t²Cov[ℓ, x²] − 1/λ − C'_sq/t| ≤ K/t²`), `covK_lin_order2_rate` (`|t²Cov[ℓ, x] + α/(2λ²) − C'_lin/t| ≤ K/t²`),
with `C'_sq = 2B₂`, `C'_lin = 2B₁`. Leading rates: `mean_anharmonic_O2_rate` (`|t⟨x⟩ − a| ≤ K/t`), `covK_lin_rate` (`|t²Cov[ℓ, x] − a| ≤ K/t`).
GPT (tide 71) computed the missing off-diagonal contribution: for `i ≠ j`, `t²Cov[L, uᵢuⱼ] = 2aᵢaⱼ/t + O(t⁻²)`, so the rotated
second-order coefficient acquires `2∑_{i<j} B̃ᵢⱼaᵢaⱼ`.

### A. The pair covariances to second order (frame)

For `i ≠ j`: `|t²Cov[L, uᵢuⱼ] − 2aᵢaⱼ/t| ≤ K/t²` (`covK_separable_offdiag_order2_rate`), from the exact pair identity:
`t²⟨xⱼ⟩Cov_i[ℓᵢ, x] = (t⟨xⱼ⟩)(t²Cov_i[ℓᵢ, x])/t` and `(aⱼ + O(1/t))(aᵢ + O(1/t)) = aᵢaⱼ + O(1/t)` (an abstract product lemma:
`|XY − ab| ≤ (K_X(|b| + K_Y) + |a|K_Y)/t`). Diagonal: `|t²Cov[L, uᵢ²] − 1/λᵢ − C'_sq,i/t| ≤ K/t²`, `|t²Cov[L, uᵢ] − aᵢ − C'_lin,i/t| ≤ K/t²`
(tide 71 through `coord_pow`). Unified: `covK_separable_pair_order2_rate`:
`|t²Cov[L, uᵢuⱼ] − (if i = j then 1/λᵢ else 0) − (if i = j then C'_sq,i else 2aᵢaⱼ)/t| ≤ K/t²`.

### B. eq:covK to second order for the general quadratic probe (frame)

`|t²Cov[L, ψ̃] − C − C'/t| ≤ K/t²` with `C = ∑ᵢ(B̃ᵢᵢ/(2λᵢ) − b̃ᵢαᵢ/(2λᵢ²))` and
`C' = ∑_{p} (B̃_p/2)(if p.1 = p.2 then C'_sq,p.1 else 2a_{p.1}a_{p.2}) + ∑ᵢ b̃ᵢ C'_lin,i`
`  = ∑ᵢ (B̃ᵢᵢ C'_sq,i/2 + b̃ᵢ C'_lin,i) + ∑_{i≠j} B̃ᵢⱼ aᵢaⱼ` (`covKCoeff2Sep`), via `gibbsCov_energy_quadratic_split` and finite sums of
`K/t²` rates over `ι × ι` and `ι` (`sum_rate_div_sq`). Also the closed form of the off-diagonal part: `∑_{i≠j} B̃ᵢⱼaᵢaⱼ = aᵀB̃a − ∑ᵢ B̃ᵢᵢaᵢ²`
(`covKCoeff2Sep_offdiag_eq`), i.e. the quadratic form of `B̃` on the leading mean-shift vector minus its diagonal.

### C. The ambient (E2) form and the relative error

`|Cov[L∘A, ψ] − covKFormula t H T B b − C'(B̃, b̃)/t³| ≤ K/t⁴` (`covKFormula_rot_order2_rate`), by the transport of
`covKFormula_rot_rate` (`covKFormula = C/t²` in the frame) — the unscaled covariance has terms at `t⁻²` and `t⁻³` with an `O(t⁻⁴)` remainder.
Relative form (`covKFormula_rot_ratio_order2_rate`): when `C ≠ 0`, `|Cov[L∘A, ψ]/covKFormula − 1 − (C'/C)/t| ≤ K/t²` — E2's
"relative error proportional to `1/t`" with its coefficient, in the rotated frame (§76 gave it per eigendirection).

### D. Corollary: the coefficient is not the diagonal one

For `B̃` with off-diagonal entries and `aᵢaⱼ ≠ 0` the coefficient `C'` differs from the eigenframe-diagonal `∑ᵢ(B̃ᵢᵢC'_sq,i/2 + b̃ᵢC'_lin,i)`
by `∑_{i≠j} B̃ᵢⱼaᵢaⱼ`: unlike the leading order (`covK_separable_quadratic`: "only the eigenframe-diagonal part of `B` survives"), at
second order the off-diagonal part of the probe contributes, through the product of the leading mean shifts. (Pure algebra;
formalised as B's closed form, with a remark.)

Proposed bundle: A + B + C (D is B's closed form). Line estimate ~500.

Numerical check (`numcheck_covK_order2_multi.py`, 2D, `λ = (1.3, 0.9)`, `α = (0.7, −0.4)`, `γ = (1.1, 1.5)`, `B̃ = [[1, ½],[½, 2]]`,
`b̃ = (0.3, −0.2)`; the covariances by 1D quadratures via separability): `C = 1.384214`, `C' = −1.245008` (diagonal part `−1.193872`,
off-diagonal `2B̃₁₂a₁a₂ = −0.051136`); `t(t²Cov − C) = −1.1472, −1.2332, −1.2439, −1.2449` at `t = 10, 40, 160, 640` (at `t = 2560` the
quadrature loses the cancellation in `Cov[ℓ, x²]`; excluded); the pair term `t·t²Cov[L, u₁u₂] = −0.0713, −0.0925, −0.0997, −0.1016, −0.1021`
vs `2a₁a₂ = −0.10227`.

## Numerical check

`numcheck_covK_order2_multi.py`: see the last paragraph of the candidates — `t(t²Cov[L, ψ̃] − C) → −1.2449` vs `C' = −1.24501` and the pair
term `→ −0.1021` vs `2a₁a₂ = −0.10227` (quadrature reliable up to `t = 640`).

## GPT-6 Astra v1

Verbatim in `gpt_covK_order2_multi_v1.md` (prompt: `gpt_covK_order2_multi_prompt_v1.md`). Summary: A, B, C correct for all
sufficiently large `t`; the off-diagonal coefficient `2aᵢaⱼ` re-derived (`mⱼvᵢ + mᵢvⱼ` with `mᵢ = aᵢ/t + O(t⁻²)`, `vᵢ = aᵢ/t² + O(t⁻³)`);
the ordered-pair form `∑_{i≠j} B̃ᵢⱼaᵢaⱼ` needs no symmetry (the skew part contributes zero; `2∑_{i<j}` assumes symmetric `B̃`); remainder
orders `K/t²` (scaled), `K/t⁴` (unscaled), `K/t²` (relative, constant `K/|C|`) all right. Keep the closed form
`∑_{i≠j} B̃ᵢⱼaᵢaⱼ = aᵀB̃a − ∑ᵢ B̃ᵢᵢaᵢ²` for Lean (no order on `ι`); for exposition `C' = mᵀBm + tr(BS₂) + bᵀr` with `m = Qa` (the
time-independent mean-shift coefficient), `S₂ = Q diag(C'_sq,i/2 − aᵢ²)Qᵀ` (the second-order coefficient of the centred covariance),
`r = Q(C'_lin,i)`. Pitfalls: `t ≥ 1` and nonnegative constants in the product lemma (`|XY − ab| ≤ (|b|K_X + |a|K_Y + K_XK_Y)/t`),
common thresholds, absolute probe coefficients in the constants, handle the `if` by cases, separate the algebraic extraction from the
analytic assembly, unscale after recording `t > 0`. **Correction to D**: "nonzero off-diagonal entries and nonzero `aᵢaⱼ`" is not
sufficient — the sum can cancel; say "off-diagonal probe components *can* contribute at second order, through products of leading mean
shifts; the coefficients differ precisely when `∑_{i≠j} B̃ᵢⱼaᵢaⱼ ≠ 0`", and at leading order "only the eigenframe-diagonal part of the
*quadratic component* survives" (the linear probe contributes there too). E2 wording: relative error `(C'/C)/t + O(t⁻²)` for `C ≠ 0`;
"proportional to `1/t`" is an asymptotic equivalence only when `C' ≠ 0` (if `C' = 0` the relative error improves to `O(t⁻²)`).
Nearby: the derivative reading predicts `⟨ψ⟩_t = C/t + C'/(2t²) + O(t⁻³)` but must not be obtained by differentiating the remainder;
cheap corollaries `lim t(Cov/covK − 1) = C'/C` and, for `C = 0 ≠ C'`, `Cov = C'/t³ + O(t⁻⁴)`; do not bundle the localised eq:covK.

## Vote
- Claude: A + B + C, with D as B's closed-form corollary in GPT's wording (`covKCoeff2Sep_eq`, `covKCoeff2Sep_offdiag_eq`)
- GPT-6 Astra: "A + B + C, with D as the corrected closed-form corollary; defer derivative and localized extensions"

## Result

Commit `0f780fa` on `tide/covK-order2-multi`; `lake build` clean, `scripts/sorries` 0/0/0/0. A + B + C as voted, D as B's closed-form
corollary in GPT's wording.
`Laplace/Multi/CovKOrder2Multi.lean` (     358 lines): `prod_rate`, `covK_separable_sq_order2_rate`, `covK_separable_lin_order2_rate`,
`covK_separable_offdiag_order2_rate` (A), `covKPairCoeff2`, `covK_separable_pair_order2_rate`, `covKCoeff2Sep`,
`covKCoeff2Sep_eq`, `covKCoeff2Sep_offdiag_eq` (D), `covK_separable_quadratic_order2_rate` (B), `covKFormula_rot_order2_rate`,
`covKFormula_rot_ratio_order2_rate` (C).

Surprises: none — the exact pair identity of `CovKSeparable` plus tide 71's coefficients made this a bookkeeping tide; the only
new analytic content is the product-of-rates lemma. GPT's correction to D (non-cancellation, not nonzero entries) went into the
docstring; its `C' = mᵀBm + tr(BS₂) + bᵀr` presentation is recorded in the log as exposition, not formalised.
