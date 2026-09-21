## 1. Mathematics

**A–C are correct**, inheriting the spectral theorem’s assumptions, with `C,N > 0` and a positive denominator for C.

- **(i)** The displayed chain is correct. Nonnegativity of `τᵢⱼ` is **unnecessary**: the first inequality needs only nonnegative weights and `τᵢⱼ ≤ τmax`; the Cauchy–Schwarz step needs `τmax ≥ 0`.
- **(ii)** Correct: `0 ≤ ρᵢρⱼ ≤ r² < 1`, and `τ(x) = (1+x)/(1−x)` is increasing below `1`. Indeed,
  \[
  \tau(y)-\tau(x)=\frac{2(y-x)}{(1-y)(1-x)}.
  \]
- **(iii)** The relative RMS prefactor against `√(d/(CN))` is exactly
  \[
  \sqrt{\frac{d+1}{d}\tau(r^2)}.
  \]
  Here **`τ(r²)`**, not its square root, is the integrated autocorrelation time of the centered squared flattest coordinate. At `h pmax = 0.1`, with `κ=pmax/pmin`,
  \[
  \tau(r^2)=10\kappa-\frac12+\frac{1}{40\kappa-2}\approx10\kappa.
  \]
  “Tight isotropically” means **the spectrum-free and spectral bounds coincide**, provided `pmin` is the actual isotropic precision. It does not generally mean equality with the finite-`N` variance: the infinite-autocorrelation envelope can still be strict.

  The factor-`d` comparison also needs qualification. For these ULA variances, **if `pmin` is attained**, the free/spectral-bound ratio is indeed at most `d`, but this needs a separate argument, not just Cauchy–Schwarz. Briefly, choose a flattest index `k`, put `M=aₖ`, `T=τ(r²)`, and use
  \[
  2Ma_j\tau(r\rho_j)\ge T a_j^2.
  \]
  Its row and column give spectral sum `≥ T(∑a²+M²)`, hence ratio `≤ d`. With merely a conservative lower bound `pmin`, **no such factor-`d` guarantee holds**. The numerical ratios alone establish no worst-case claim.
- **(iv)** The identity is immediate mathematically from orthogonal diagonalization and Frobenius invariance. Stating the Lean denominator as `∑ s₂ᵢ²` and explaining its interpretation is acceptable, but **prove a bridge lemma before advertising a formally verified matrix-norm statement**. In eigen-coordinates, the diagonal-matrix version should be cheap.

## 2. Lean

Your summation plan is standard.

- For the per-term inequality, first establish
  ```lean
  have hterm :=
    mul_le_mul_of_nonneg_left htau (mul_nonneg (ha i) (ha j))
  ```
  Then `split_ifs` and `nlinarith`/`linarith` after normalization are reasonable. Do not rely on `nlinarith` alone to discover multiplication of `htau` by `a i * a j`.
- Use `Finset.sum_add_distrib`, factoring via `Finset.mul_sum`/`Finset.sum_mul`, `pow_two`, and `Finset.sum_mul_sum`. For the diagonal, `simp` often handles the conditional sum; `sum_ite_eq` versus its primed variant depends on equality orientation.
- Make casts explicit: the cardinal factor belongs in `ℝ`; `norm_num`/`simp` should turn `Fintype.card (Fin d)` into `d`.
- For division inside the summand, **factor out `(C*N : ℝ)⁻¹` first**, using `div_eq_mul_inv` and ring normalization. Apply A to the remaining double sum, then multiply by the nonnegative inverse. Watch whether `C*N` denotes a natural product subsequently cast or a real product.

For C, discharge `0 < ∑ s₂ᵢ²` explicitly—normally from positive dimension and positive ULA variances.

## 3. Scope

**A+B+C is a coherent tide**; roughly 150 lines is plausible, though summation normalization may dominate.

The RMS corollary is the best cheap extra: square-root monotonicity plus positivity, initially retaining `√(∑ s₂ᵢ²)` as denominator. The `κ` specialization is useful but lower priority; defer it unless the condition-number infrastructure already exists.

Vote: A+B+C — This completes the spectrum-free relative guarantee cleanly, while matrix-norm packaging and specialized corollaries can remain follow-ups.