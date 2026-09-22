You are GPT-6 Astra consulting on a Lean 4 + Mathlib formalisation tide ("laplace" seabed: Laplace asymptotics of Gibbs expectations
for the quartic anharmonic oscillator; eq:covK is a research note's Hessian-route formula for `Cov_t[L, ψ]` between the loss and a
quadratic probe, `covKFormula`, exact-to-leading-order `C/t²` for the separable oscillator). In an earlier consult you computed that
for the rotated oscillator the second-order coefficient acquires off-diagonal pair terms `2∑_{i<j} B̃ᵢⱼaᵢaⱼ`. Below are the candidates
for the tide that formalises this. Please answer:

1. Are A, B, C correct as stated? Check the pair coefficient `2aᵢaⱼ` independently from the exact identity
   `Cov[L, uᵢuⱼ] = ⟨xⱼ⟩Cov_i[ℓᵢ, x] + ⟨xᵢ⟩Cov_j[ℓⱼ, x]` (`i ≠ j`), the assembled `C'`, and the ambient/relative forms (orders of the remainders:
   `K/t²` scaled, `K/t⁴` unscaled, `K/t²` relative). Is the off-diagonal closed form `∑_{i≠j} B̃ᵢⱼaᵢaⱼ = aᵀB̃a − ∑ᵢ B̃ᵢᵢaᵢ²` the best way to
   present it, or is there a nicer invariant form (e.g. in terms of the leading mean shift `μ = Qa/t` and the ambient `B`: `t²μᵀBμ − …`)?
2. Any pitfalls in the remainder bookkeeping (products of two `K/t`-rates, finite sums over `ι × ι`, the `if i = j` unification)?
3. Wording against the note's E2 ("relative error proportional to `1/t`"): with `C'` now in the rotated frame, how should the result be
   stated? Is D's remark ("unlike leading order, the off-diagonal part of the probe contributes at second order, through the product of the
   leading mean shifts") fair? Is there a nearby stronger target (e.g. the derivative reading `Cov_t[L, ψ] = −∂ₜ⟨ψ⟩_t` at second order in E2,
   or the localised eq:covK) worth bundling?
4. Vote: which single bundle do you back?

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
