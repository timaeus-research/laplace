### 1. Correctness

**(a) Yes**, assuming `C,N > 0`, `0 ≤ ρ < 1`, `v > 0`. Writing `σ² = v/(1−ρ²)`, the exact shortfall is
\[
\sigma^2-\mathrm{pooled}
=\sigma^2\left(\frac{R_2}{N}+\frac{T_N-R_1^2}{CN^2}\right).
\]
- \(R_2=\rho^{2(b+1)}\sum_{i<N}(\rho^2)^i\le \rho^{2(b+1)}/(1-\rho^2)\).
- \(T_N\le N+2N\rho/(1-\rho)=N(1+\rho)/(1-\rho)\).
- `norm_sum_window_sq` gives \(\sigma^2(T_N-R_1^2)=\|\sum x\|^2\ge0\). Since `C > 0`, use `X ⟨0, hC⟩` as the witness chain. Thus `pooled ≤ σ²`.

\((1+\rho)/(1-\rho)\) is exactly the **stationary integrated autocorrelation time**, with convention \(1+2\sum_{k\ge1}\rho^k\).

**“Tight up to dropped \(R_1^2\)” needs qualification:** both geometric truncation and the replacement of Toeplitz weights by `N` introduce additional slack. Indeed,
\[
N\tau-T_N=\frac{2\rho(1-\rho^N)}{(1-\rho)^2}.
\]
The bound is leading-order sharp as `N → ∞` for fixed `ρ,b,C`, but can be loose when `N(1−ρ)` is small.

For ULA, \(\tau=(2-hp)/(hp)\le2/(hp)\), as proposed.

**(b) Yes.** Symmetry makes the entrywise contraction a trace, giving
\[
\sum_{i,j}(tH)_{ij}((tH+\gamma I)^{-1})_{ij}
=\sum_i\frac{t\lambda_i}{t\lambda_i+\gamma}.
\]
For **any** eigenvector, without unit normalisation,
\[
u^\top(tH+\gamma I)^{-1}u
=\frac{\|u\|^2}{t\lambda+\gamma}
=\frac{\|u\|^2/(t\lambda)}{1+\gamma/(t\lambda)}.
\]
For nonunit `u`, this is the variance of the linear observable \(u^\top w\); normalised directional variance divides by \(\|u\|^2\). The note’s `γ_rel` uses `λ_min`; the per-direction version uses `λᵢ`.

### 2. Lean route

**(a) Prefer the already-working `geom_sum_eq`.** For `0 ≤ q < 1`, first establish
```lean
∑ i ∈ range N, q ^ i = (1 - q ^ N) / (1 - q)
```
from `geom_sum_eq (ne_of_lt hq)`, by field algebra. Then:
```lean
apply (div_le_iff₀ (sub_pos.mpr hq)).2
-- RHS simplifies to 1; use pow_nonneg hq0 N.
```
Apply with `q = ρ²`, and separately `q = ρ`.

Useful names:
- `Finset.sum_le_sum`
- `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`
- `Finset.mul_sum`, `Finset.sum_mul`
- `pow_add`, `pow_mul`, `pow_succ`
- `pow_nonneg`, `sub_pos.mpr`, `div_le_iff₀`

For the weighted sum, use termwise
\[
(N-(m+1))\rho^{m+1}\le N\rho^{m+1},
\]
then factor `ρ` out of the power sum. Keep the weights as **real subtraction**, matching the existing theorem. No specialised `Ico` lemma is needed; I would not rely on the suggested specialised name without checking the pin.

**(b) Your inverse route is sound.** Most robust: define
```lean
D := diagonal (fun i => t * λ i + γ)
E := diagonal (fun i => 1 / (t * λ i + γ))
```
and prove `D * E = 1` by `diagonal_mul_diagonal`, extensionality, and denominator nonzeroness. Then prove
```lean
(t • H + γ • 1) * (U * E * Uᵀ) = 1
```
and apply `Matrix.inv_eq_right_inv`. This avoids depending on `Matrix.diagonal_inv`’s precise interface.

Pitfalls:
- Prove the diagonal affine identity **entrywise** (`ext i j; by_cases i = j; simp [...]`), as in `ulaStep_eq_conj`.
- Use `Matrix.mul_add`, `Matrix.add_mul`, `Matrix.mul_smul`, `Matrix.smul_mul`; `smul_add` is the generic distributivity lemma.
- Do **not** simplify `γ • (1 : Matrix ...)` to `1` via `smul_one`; it is a scalar matrix.
- Control association explicitly around `Uᵀ * U` / `U * Uᵀ`, following `trace_mul_ulaCov`.
- For the contraction, expand `Matrix.trace`, `Matrix.mul_apply`, `Matrix.transpose_apply` if necessary. Prove `Xᵀ = X` before removing the transpose. `Matrix.trace_mul_cycle`, already used in the source, is especially convenient for cancelling the conjugation.

**(c) Confirmed:** once the existing integral identity supplies the scalar closed form, the corollary is entirely algebra and inequalities. No new integrability or measure-theoretic argument is needed.

### 3. Vote

**A**, with the tightness wording corrected; optionally add the cheap `p_min` / `20κ` corollary.