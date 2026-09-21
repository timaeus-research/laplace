# Context for a Lean 4 / Mathlib formalisation step (tide `gaussian-moments-posdef`, seabed `laplace`)

The multivariate track of the laplace seabed works on `ι → ℝ` (Lebesgue measure `volume = Measure.pi`) with
`quadForm (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) z := ∑ i, z i * (H z) i`, `gaussianWeight H u := exp (-(1/2) * quadForm H u)`,
`gaussianZ H := ∫ u, gaussianWeight H u`. Its Gaussian integration-by-parts theorem
`gaussian_second_moment_eq_inverse_entry_scalar (H Hinv) (hHinv : H.comp Hinv = id) (hH_inj) (i j)
  (h_int_gW : Integrable (gaussianWeight H)) (h_int_uk_uj_gW : ∀ k, Integrable (fun u => u k * u j * gaussianWeight H u))
  (h_int_uj_Hi_gW : ∀ i, Integrable (fun u => u j * (H u) i * gaussianWeight H u))
  (h_fubini : ∀ i, FubiniIBPHypothesis H i j) : ∫ u, u i * u j * gaussianWeight H u = gaussianZ H * (Hinv (Pi.single j 1)) i`
where `FubiniIBPHypothesis H i j : ∫ u, ((if i = j then 1 else 0) * gaussianWeight H u - u j * (H u) i * gaussianWeight H u) = 0`
is *assumed*, never discharged anywhere in the seabed (it was left as "Option A" in a 2026-05 memo). The same hypothesis package
appears in `Laplace/Multi/GaussianLLC.lean` (`localised_gaussian_K_expectation`) and in every multivariate Laplace theorem.

Separately, on `EuclideanSpace ℝ ι` we now have measure-form results from Mathlib's `multivariateGaussian`:
`∫ x, x.ofLp i * x.ofLp j ∂(multivariateGaussian 0 S) = S i j` for PSD `S` (`integral_coord_mul_multivariateGaussian`), and
`∫ ⟨x, H x⟩ = tr(H S)`. Also available in the seabed: `orthoOf`/`spectral_real` (`P = U diag(p) Uᵀ`, `U` orthogonal),
`Laplace.Multi.integrable_exp_neg_const_mul_sum_sq : 0 < c → Integrable (fun u : ι → ℝ => exp (-(c * ∑ i, (u i)^2)))`,
`integrable_coord_mul_coord_mul_exp_neg_const_mul_sum_sq`, 1D Gaussian moments `∫ x^(2k) exp(-(t x²)/2) = (2k-1)‼ √(2π) t^(-(k+1/2))`.

## Goal of this tide

For a positive definite matrix `P : Matrix ι ι ℝ`, with `H := toLin' P` as a continuous linear map on `ι → ℝ` (so
`quadForm H u = u ⬝ᵥ P *ᵥ u`), prove the four hypotheses and the closed forms:
- (D1) `Integrable (gaussianWeight H)`, `Integrable (fun u => u k * u j * gaussianWeight H u)`, `Integrable (fun u => u j * (H u) i * gaussianWeight H u)`
  (from `u ⬝ᵥ P u ≥ p_min |u|²`, `p_min > 0`, via the seabed's `exp(-c ∑ u_i²)` integrability and domination).
- (D2) `gaussianZ H = (2π)^(d/2) / √(det P)`.
- (D3) `∫ u, u i * u j * gaussianWeight H u = gaussianZ H * (P⁻¹) i j` (the second-moment identity), and hence
  `FubiniIBPHypothesis H i j` for all `i j` (the IBP identity is equivalent to `∑_k P_ik ∫ u_j u_k gW = δ_ij Z`).
- (D4) Corollaries: `localised_gaussian_K_expectation` with hypotheses `P.PosDef` only; the seabed's IBP theorem discharged for PD `P`.

Two routes for D2/D3:
- (R1) Linear change of variables: `u = M v` with `M = U diag(p^{-1/2})` (`M Mᵀ = P⁻¹`, `|det M| = (det P)^{-1/2}`), so
  `gaussianWeight H (M v) = exp(-|v|²/2)` and Lebesgue measure scales by `|det M|` (`MeasureTheory.Measure.addHaar_map_linearMap`
  or `map_linearMap_addHaar_eq_smul_addHaar`, `LinearMap.toMatrix'`/`Matrix.toLin'`, `Matrix.det`); then products of 1D Gaussians
  on `Measure.pi` (`MeasureTheory.integral_fintype_prod_eq_prod`, `volume_pi`) give `Z` and the moments `∫ v_k v_l e^{-|v|²/2} = δ_kl Z₀`.
- (R2) Identify the normalised weight with Mathlib's `multivariateGaussian 0 P⁻¹` pushed to `ι → ℝ` (needs a density formula for
  `multivariateGaussian`, or a characteristic-function computation of `∫ exp(i⟨t,u⟩) gW(u) du / Z` = `exp(-⟨t, P⁻¹ t⟩/2)`, which again
  needs the Gaussian integral with a linear term — essentially R1), then reuse `integral_coord_mul_multivariateGaussian`.

## Questions
1. Is the reduction "second-moment identity ⟹ FubiniIBPHypothesis" right as stated (so that the IBP hypothesis never needs a derivative)?
   Any subtlety with `H u` vs `P *ᵥ u` and `toLin'`?
2. Which route (R1/R2) is more tractable in Mathlib, and what are the load-bearing lemma names for the linear change of variables on
   `ι → ℝ` with Lebesgue measure (`Measure.pi`), the determinant factor, and the factorisation of `∫ ∏ f i (v i)` over `Measure.pi`?
   Does Mathlib have a Gaussian integral on `ι → ℝ`/`EuclideanSpace` with a PD matrix already (search names: `integral_exp_neg_quadratic`,
   `gaussianIntegral`, `integral_cexp_neg_mul_sq`, `Real.Gaussian`...)? A density lemma for `multivariateGaussian` (`multivariateGaussian_eq_withDensity`?)?
3. For D1, the cleanest way to get `p_min |u|² ≤ u ⬝ᵥ P u` from `P.PosDef` in the pin (Rayleigh / `Matrix.PosDef.eigenvalues_pos` + spectral
   form), and to apply the seabed's `integrable_exp_neg_const_mul_sum_sq` by domination (`Integrable.mono'`)? For the polynomial factors,
   `|u_k u_j| ≤ ∑ u_i²` style bounds or the seabed's `integrable_coord_mul_coord_mul_exp_neg_const_mul_sum_sq`?
4. How should the result be packaged so that the seabed's hypothesis structures (`LaplaceCov6MomentHypotheses`, the `fubini_ibp` field) can be
   discharged for the Gaussian case with minimal churn — a single theorem `gaussianHypotheses_of_posDef` producing all four facts?
5. Is this the right size for one excursion (estimate in lines/sub-tasks), and what should be cut first if it balloons? Please end with a
   one-line vote for a single target cluster.
