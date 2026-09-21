# Context for a Lean 4 / Mathlib formalisation step (tide `gaussian-quadratic`, seabed `laplace`)

Formalised (`Laplace/Sampler/`, Lean 4 + Mathlib pin Sep 2026): the ULA law `ulaCov P h` with eigenbasis entries, `trace_mul_ulaCov :
trace (P * ulaCov P h) = ∑ i, 1/(1 - h p_i/2)` and `ula_llc` (the "ULA-corrected LLC" `(t/2) trace (H Σ_ULA)` for `P = t H`);
`multivariateGaussian` push-forwards/convolutions, `ulaCov_invariant` (`N(0, Σ_ULA)` invariant), `ulaCov_unique_invariant`,
`tendsto_ula_iterate` (convergence in law from any start); `euclid A := toEuclideanCLM A`; `dotProduct_conj_mulVec`.
Also `Laplace/Multi/GaussianLLC.lean` (integral form, on `ι → ℝ` with the seabed's Gibbs integrals and hypothesis package):
`localised_gaussian_K_expectation : (∫ ½⟨u,Hu⟩ e^{-½⟨u,Pu⟩}) / Z = ½ ∑ᵢⱼ H_ij (P⁻¹)_ij`.

Mathlib facts checked: `covarianceBilin_multivariateGaussian (hS : S.PosSemidef) (x y) : covarianceBilin (multivariateGaussian μ S) x y = x.ofLp ⬝ᵥ S *ᵥ y.ofLp`,
`integral_id_multivariateGaussian : ∫ x, x ∂(multivariateGaussian μ S) = μ`, `IsGaussian.memLp_two_id`, `IsGaussian.integrable_id`,
`covarianceBilin_apply (h : MemLp id 2 μ) (u v) : covarianceBilin μ u v = ∫ x, ⟪x - μ[id], u⟫ * ⟪x - μ[id], v⟫` (form to check),
`inner_toEuclideanCLM (A) (x y) : ⟪x, euclid A y⟫ = x.ofLp ⬝ᵥ A *ᵥ y.ofLp`, `EuclideanSpace.basisFun`, `Matrix.trace`, `Matrix.trace_mul_comm`.

## Candidate (Claude)

**Q. Gaussian quadratic expectations in measure form.** On `E := EuclideanSpace ℝ ι`, for `S` PSD and any `H : Matrix ι ι ℝ`:
- (Q1) `∫ x, ⟪x, euclid H x⟫ ∂(multivariateGaussian 0 S) = trace (H * S)` (`= ∑ᵢⱼ H_ij S_ij` for symmetric `S`; in general `trace (H S)`).
  Route: `⟪x, H x⟫ = ∑ᵢⱼ H_ij x_i x_j`, `x_i = ⟪e_i, x⟫`, and `∫ x_i x_j = covarianceBilin μ e_i e_j = e_i ⬝ᵥ S e_j = S_ij` for the centred
  Gaussian (mean `0`), so the integral is `∑ᵢⱼ H_ij S_ij = trace (H Sᵀ) = trace (H S)` (PSD `S` is symmetric). Integrability of `x_i x_j`
  from `IsGaussian.memLp_two_id` (`MemLp id 2` ⟹ products of coordinates integrable).
- (Q2) With mean: `∫ ⟪x, H x⟫ ∂(multivariateGaussian m S) = trace (H * S) + ⟪m, euclid H m⟫` (translate by `m`, or expand).
- (Q3) **The sampler's LLC as an expectation under the invariant law.** For `P = t • H` positive definite (`H` the Hessian at the mode,
  `γ = 0`), `t ∫ x, ½⟪x, euclid H x⟫ ∂(multivariateGaussian 0 (ulaCov P h)) = ½ ∑ᵢ 1/(1 - h p_i/2)` (from Q1 and `trace_mul_ulaCov`),
  versus `d/2` under the Gibbs law `N(0, P⁻¹)`: `t ∫ ½⟪x, H x⟫ ∂(multivariateGaussian 0 P⁻¹) = d/2` (`trace (H P⁻¹) = trace(1)/t`).
  This states the note's "ULA inflates the LLC" as a statement about expectations under the actual stationary law of the sampler.
- (Q4, optional) `∫ x_i x_j` version: `∫ x, x.ofLp i * x.ofLp j ∂(multivariateGaussian 0 S) = S i j` as the reusable core.

## Questions
1. Are Q1–Q3 correct (in particular `trace (H * S)` vs `∑ H_ij S_ij` for non-symmetric `H`, and the mean term in Q2)?
2. The cleanest Lean route from `covarianceBilin` to `∫ x_i x_j`: `covarianceBilin_apply`/`covarianceBilin_apply'` (names and the exact
   centring form in the pin), with `integral_id_multivariateGaussian` giving mean `0`; how to write `x_i = ⟪e_i, x⟫` with
   `EuclideanSpace.basisFun`/`EuclideanSpace.single`, and `⟪x, euclid H x⟫ = ∑ᵢⱼ H_ij x_i x_j` (`inner_toEuclideanCLM`, `dotProduct`,
   `mulVec`)? Integrability of `x ↦ x_i x_j` from `MemLp id 2` (`MemLp.integrable_mul` after composing with the coordinate functionals)?
3. Would it be cleaner to prove Q1 through `IsGaussian.ext`-style bilinear identities (`covarianceBilin` as a bilinear form and the trace as
   `∑ᵢ covarianceBilin (e_i) (Hᵀ e_i)`) than through coordinates?
4. For Q3, `multivariateGaussian 0 P⁻¹` for PD `P`: `P⁻¹.PosSemidef` (`Matrix.PosDef.inv`?) and `trace (H * P⁻¹) = card ι / t` for `P = t • H`
   (`Matrix.inv_smul`? `Matrix.mul_nonsing_inv`, `trace_one`). Names to check.
5. Anything incorrect or a bigger nearby target of comparable size (e.g. the mean shift `E[x] = m` and the finite-time LLC trajectory
   `t E_k[K] = ½ tr(H Σ_k)` along the chain from the mode, using `gaussStep_iterate_zero`)? Please end with a one-line vote for a single target cluster.
