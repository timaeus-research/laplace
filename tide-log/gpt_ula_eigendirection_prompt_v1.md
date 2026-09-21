# Context for a Lean 4 / Mathlib formalisation step (tide `ula-eigendirection`, seabed `laplace`)

Formalised (`Laplace/Sampler/`, Lean 4 + Mathlib pin Sep 2026):
- `AR1Chain E ρ v` (real inner product space, white noise `inner ℝ (η j) (η k) = if j = k then v else 0`), Gram table, and
  `AR1Chain.pooled_sample_variance`; realised version `AR1Real.lean`: `realChain ρ η` (pointwise recursion on a probability
  space `(Ω, P)`), `expected_pooled_sample_variance` under the moment table `∫ η c j * η c' k = if c = c' ∧ j = k then v else 0`
  (`hη : ∀ c k, MemLp (η c k) 2 P`), `white_of_indep` (centred pairwise independent innovations with second moment `v`).
- ULA on `E := EuclideanSpace ℝ ι`: `euclid A := toEuclideanCLM A`, `gaussStep`, invariance/uniqueness/convergence of
  `N(0, Σ_ULA)`, and `RandomMap.lean`: the law of `A X + √(2h) ξ` for independent `X`, `ξ ~ stdGaussian E` is `gaussStep`.
- Spectral packaging: `orthoOf hP : Matrix ι ι ℝ` orthogonal with `P = U diag(p) Uᵀ` (`spectral_real`), `ulaStep P h = 1 - h • P`,
  `ulaStep_eq_conj : ulaStep P h = U diag(1 - h p_i) Uᵀ`, `ulaCov_conj_apply` (eigenbasis variances `1/(p_i (1 - h p_i/2))`).

The note (E1, E2, E4) compares the *sampled per-eigendirection variance* of the ULA chain started at the mode with the
finite-chain prediction `ar1_expected_sample_variance(ρ_i = 1 - h p_i, σ_i² = 1/(p_i(1 - h p_i/2)), N, b, C)`. The missing
theorem: the ULA chain projected on an eigendirection *is* the AR(1) chain with `ρ = 1 - h p_i` and innovation variance `2h`.

Mathlib facts checked: `stdGaussian E`, `variance_dual_stdGaussian (L : StrongDual ℝ E) : Var[L; stdGaussian E] = ‖L‖²`,
`integral_id_stdGaussian`, `iIndepFun` (`iIndepFun.indepFun` for `i ≠ j`), `IndepFun.comp`, `IndepFun.integral_mul_eq_mul_integral`,
`integral_map`, `IsGaussian.memLp_id`, `innerSL ℝ u : StrongDual ℝ E`, `covarianceBilin_stdGaussian = innerSL ℝ`.

## Candidate (Claude)

**G. The ULA chain along an eigendirection.** Setting: `(Ω, P)` a probability space, `ξ : ℕ → Ω → E` with
`hξ : ∀ k, P.map (ξ k) = stdGaussian E` (each `ξ k` standard Gaussian) and `hind : iIndepFun ξ P` (mutually independent),
measurability `∀ k, AEMeasurable (ξ k) P` (or `Measurable`). The ULA chain from the mode: `w 0 = 0`,
`w (k+1) ω = euclid A (w k ω) + Real.sqrt (2*h) • ξ (k+1) ω` with `A = ulaStep P h`. For a unit vector `u` with `P *ᵥ u = p • u`
(an eigenvector), the projections `x k ω := inner ℝ u (w k ω)` satisfy the pointwise AR(1) recursion
`x (k+1) = (1 - h p) * x k + η (k+1)` with `η k ω := Real.sqrt (2h) * inner ℝ u (ξ k ω)`.
- (G1) `η k ∈ L²`, `∫ η j * η k = if j = k then 2h else 0` (independence for `j ≠ k` + centring; for `j = k`,
  `∫ (inner u (ξ k))² = Var = ‖innerSL ℝ u‖² = ‖u‖² = 1` via `variance_dual_stdGaussian` and `integral_map`).
- (G2) `x = realChain (1 - h p) η` (definitional/induction), so `expected_pooled_sample_variance` gives the note's
  finite-chain prediction for the *actual* ULA chain along `u`, with `ρ = 1 - h p`, `v = 2h`, `σ² = v/(1-ρ²) = 1/(p(1 - h p/2))`
  (the ULA variance).
- (G3) Several chains: `ξ : Fin C → ℕ → Ω → E` mutually independent across `(c, k)` (`iIndepFun` on `Fin C × ℕ`), giving the
  pooled version with `C` chains.
- (G4, corollary) Eigenvector from the spectral packaging: for `u := fun j => orthoOf hP j i` (the `i`-th column of `U`),
  `P *ᵥ u = p_i • u` and `‖u‖ = 1`, so the theorem applies to every eigendirection of `P`.

## Questions
1. Is G correctly stated? Is `iIndepFun` (mutual) the right hypothesis or does pairwise suffice (we only need `∫ η j η k = 0`
   for `j ≠ k`, which needs `IndepFun (ξ j) (ξ k)` and centring)? Is it cleaner to assume the moment table for the projections
   directly and derive it from independence in a corollary (as in `white_of_indep`)?
2. The Lean route for `∫ (inner u (ξ k ω))² dP = 1`: `integral_map` to move to `stdGaussian E`, then `variance_dual_stdGaussian`
   with `L = innerSL ℝ u` (`‖innerSL ℝ u‖ = ‖u‖`, is that `innerSL_apply_norm`?) — and the relation `Var[L; μ] = ∫ L² - (∫ L)²`
   (`variance_def'`/`ProbabilityTheory.variance_eq_integral_sub_sq`? names to check) with `∫ L = 0` from `integral_id_stdGaussian`
   and `L.integral_comp_comm`. Any pitfalls with `StrongDual` coercions?
3. `∫ inner u (ξ j) * inner u (ξ k) = 0` for `j ≠ k`: `IndepFun.comp` to push independence through `inner u ·`, then
   `IndepFun.integral_mul_eq_mul_integral` and `∫ inner u (ξ j) = 0`. Fine?
4. For G4, the cleanest way to get the `i`-th column of `orthoOf hP` as a unit eigenvector: from `spectral_real` and
   `orthoOf_transpose_mul` (`Uᵀ U = 1` gives `‖column‖ = 1`; `P U = U diag(p)` gives `P *ᵥ (U · e_i) = p_i • (U · e_i)`)?
   Mathlib names: `Matrix.mulVec_single`, `Matrix.mul_apply`, `Matrix.one_apply`?
5. Anything incorrect or a bigger nearby target of comparable size? Please end with a one-line vote for a single target cluster.
