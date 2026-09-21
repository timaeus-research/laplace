# Context for a Lean 4 / Mathlib formalisation step (tide `ula-invariance`, seabed `laplace`)

Previous tides formalised, on `Matrix ι ι ℝ`: `ulaStep P h = 1 - h • P`, `ulaNoise h = (2h) • 1`,
`covStep A N X = A * X * Aᵀ + N`, `ulaCov P h = (P - (h/2) • (P*P))⁻¹`, `ulaCov_fixed : covStep (ulaStep P h) (ulaNoise h) (ulaCov P h) = ulaCov P h`
(for `Pᵀ = P` and `P - (h/2)P²` invertible), `ulaCov_posDef` (under `h p_i < 2`), and the unique-fixed-point theorem.
These are statements about the covariance recursion. The missing probabilistic statement is the one the note
*Sanity on Sampling* actually uses: on a Gaussian target the ULA chain `w ← A w + √(2h) ξ`, `ξ ~ N(0, I)`, has
`N(0, Σ_ULA)` as an invariant law ("the stationary law is exactly Gaussian with covariance Σ_ULA").

## Mathlib API available (pin of Sep 2026), checked by grep
- `ProbabilityTheory.multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) : Measure (EuclideanSpace ℝ ι)`
  defined as `(stdGaussian _).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)`; `isGaussian_multivariateGaussian`;
  `integral_id_multivariateGaussian : ∫ x, x ∂(multivariateGaussian μ S) = μ`;
  `covarianceBilin_multivariateGaussian (hS : S.PosSemidef) (x y) : covarianceBilin (multivariateGaussian μ S) x y = x ⬝ᵥ S *ᵥ y`;
  `charFun_multivariateGaussian (hS) (x) : charFun (multivariateGaussian μ S) x = exp (⟪x, μ⟫ * I - x ⬝ᵥ S *ᵥ x / 2)`;
  `multivariateGaussian_of_not_posSemidef : … = dirac μ`.
- `IsGaussian μ` (class on measures on a Banach space): `isGaussian_map (L : E →L[ℝ] F) : IsGaussian (μ.map L)`,
  `isGaussian_conv [SecondCountableTopology E] : IsGaussian (μ ∗ ν)` (Measure.conv, notation `∗` scoped in `MeasureTheory`),
  `IsGaussian.ext (hm : μ[id] = ν[id]) (hv : covarianceBilin μ = covarianceBilin ν) : μ = ν`,
  `IsGaussian.charFun_eq'`, `IsGaussian.memLp_two_id`, `IsGaussian.integrable_id`.
- `covarianceBilin_map (h : MemLp id 2 μ) (L : E →L[ℝ] F) (u v) : covarianceBilin (μ.map L) u v = covarianceBilin μ (L.adjoint u) (L.adjoint v)`;
  `integral_id_map (h : Integrable id μ) (L : E →L[𝕜] F)`; `charFun_conv (t) : charFun (μ ∗ ν) t = charFun μ t * charFun ν t`;
  `charFun_map_add_prod_eq_mul : charFun ((μ.prod ν).map (fun p ↦ p.1 + p.2)) = charFun μ * charFun ν`;
  `Measure.ext_of_charFun`.
- `Matrix.toEuclideanCLM (𝕜 := ℝ) : Matrix n n ℝ ≃⋆ₐ[ℝ] (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)` (a star-algebra
  equivalence, Analysis/CStarAlgebra/Matrix.lean), `inner_toEuclideanCLM (A) (x y) : ⟪toEuclideanCLM A x, y⟫ = ⟪x, toEuclideanCLM Aᴴ y⟫`
  (or similar; the star of a real matrix is its transpose).
- Seabed: `orthoOf`, `spectral_real`, `ulaCov_posDef`, `ulaCov_fixed`, `covStep`.

## Candidate (Claude)

**A. Gaussian invariance of the ULA step.** Let `Σ` be positive semidefinite, `A : Matrix ι ι ℝ` arbitrary,
`h > 0`, `μ := multivariateGaussian 0 Σ`, `ν := multivariateGaussian 0 ((2h) • 1)`, `L_A := toEuclideanCLM A`.
- (A1) `(μ.map L_A) ∗ ν = multivariateGaussian 0 (A * Σ * Aᵀ + (2h) • 1)` (the law of `A X + √(2h) ξ`).
- (A2) `μ.map L_A = multivariateGaussian 0 (A * Σ * Aᵀ)` (push-forward of a centred Gaussian by a linear map).
- (A3) Corollary: with `Σ = ulaCov P h`, `A = ulaStep P h`, `P` positive definite, `h p_i < 2`:
  `((multivariateGaussian 0 (ulaCov P h)).map (toEuclideanCLM (ulaStep P h))) ∗ multivariateGaussian 0 ((2h) • 1) = multivariateGaussian 0 (ulaCov P h)`,
  i.e. `N(0, Σ_ULA)` is invariant under one ULA step (by `ulaCov_fixed`).
- (A4, optional) Markov-kernel form: `κ x := multivariateGaussian (L_A x) ((2h) • 1)`; `μ.bind κ = (μ.map L_A) ∗ ν`,
  hence `(multivariateGaussian 0 (ulaCov P h)).bind κ = multivariateGaussian 0 (ulaCov P h)`.
Proof route for A1/A2: both sides are `IsGaussian`; apply `IsGaussian.ext`: means are `0` (`integral_id_map`, mean of a convolution
is the sum of means — is there `integral_id_conv`/`integral_conv`?), covariances via `covarianceBilin_map` (`L_A.adjoint = toEuclideanCLM Aᵀ`),
`covarianceBilin` of a convolution is the sum (is there `covarianceBilin_conv`?), and `covarianceBilin_multivariateGaussian`; then the
matrix identity `(Aᵀ x) ⬝ᵥ Σ *ᵥ (Aᵀ y) + 2h (x ⬝ᵥ y) = x ⬝ᵥ (A Σ Aᵀ + 2h I) *ᵥ y`. Alternative: `Measure.ext_of_charFun` with
`charFun_conv`, `charFun_multivariateGaussian`, and the charFun of a push-forward under `L_A` (`charFun (μ.map L) t = charFun μ (L.adjoint t)`?).

**B (stretch). The L² bridge for the AR(1) tide.** The previous tide proved the finite-chain sample-variance formula for a chain in an
abstract real inner product space with white noise `⟪η j, η k⟫ = v δ_jk`. Instantiate `E = Lp ℝ 2 P` for a probability space and
independent centred `η_k` with variance `v` (`MeasureTheory.L2.inner_def`, independence ⟹ `E[η_j η_k] = 0`), so the theorem becomes a
statement about `E[pooled sample variance]`.

## Questions
1. Is A correctly stated (hypotheses: `Σ.PosSemidef`, `0 < h`; is `A * Σ * Aᵀ + (2h)•1` automatically `PosSemidef`, and do the Mathlib
   lemmas require `PosSemidef` for both sides)? Any subtlety with `multivariateGaussian` being a `dirac` when the matrix is not PSD?
2. Which route is smoother in Mathlib: `IsGaussian.ext` (mean + `covarianceBilin`) or `Measure.ext_of_charFun`? Which lemmas give the
   mean and covariance of `μ ∗ ν` and of `μ.map L`? Is `(toEuclideanCLM A).adjoint = toEuclideanCLM Aᵀ` available (name), or should we
   go through `inner_toEuclideanCLM`?
3. For A4: how is `Measure.conv` defined (`(μ.prod ν).map (fun p => p.1 + p.2)`?), and is there a lemma connecting `μ.bind (fun x => ν.map (x + ·))`
   to `μ ∗ ν`? Is A4 worth including or better deferred?
4. Is B reachable in the same excursion, and what is the cleanest Mathlib formulation of "independent centred L² variables with variance v"?
5. Better or bigger nearby targets we missed (e.g. `IsGaussian` of the whole ULA chain, or the n-step law `N(0, Σ_n)` with the finite-time
   identity `Σ_n - Σ_∞ = A^n (Σ_0 - Σ_∞) (Aᵀ)^n` already formalised)?
Please end with a one-line vote for a single target cluster.
