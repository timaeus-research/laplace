# Context for a Lean 4 / Mathlib formalisation step (tide `sampler-bridges`, seabed `laplace`)

Formalised so far in `Laplace/Sampler/` (Lean 4, Mathlib pin Sep 2026):
- `gaussStep A R μ := (μ.map (euclid A)) ∗ multivariateGaussian 0 R` on `E := EuclideanSpace ℝ ι`, with `euclid A := toEuclideanCLM (𝕜 := ℝ) A`;
  `multivariateGaussian_map_conv : (N(m,S).map (euclid A)) ∗ N(b,R) = N(euclid A m + b, A S Aᵀ + R)`; invariance of `N(0, Σ_ULA)`;
  uniqueness of the invariant law and weak convergence from any start (`ulaCov_unique_invariant`, `tendsto_ula_iterate`, via charFun).
- `AR1Chain E ρ v` (structure, `E` a real inner product space): `x 0 = 0`, `x (k+1) = ρ • x k + η (k+1)`,
  `inner ℝ (η j) (η k) = if j = k then v else 0`; Gram table `inner ℝ (x k) (x l) = v/(1-ρ²) (ρ^(l-k) - ρ^(k+l))` (`k ≤ l`);
  `pooled_sample_variance (X : Fin C → AR1Chain E ρ v) (hcross : ∀ c c', c ≠ c' → ∀ j k, inner ℝ ((X c).η j) ((X c').η k) = 0) …`:
  `(1/(C N)) * ∑ c, ∑ i ∈ range N, ‖(X c).x (b+1+i)‖^2 - ‖(1/(C N)) • ∑ c, ∑ i ∈ range N, (X c).x (b+1+i)‖^2 = σ²(N - R₂)/N - σ²(T_N - R₁²)/(C N²)`.
Both are abstractions: `gaussStep` is a map on laws (convolution), and the AR(1) theorem is about Gram matrices in an abstract
inner product space. This tide adds the two bridges to the algorithm as implemented and to actual random variables.

Mathlib facts checked: `stdGaussian E : Measure E` (`isGaussian_stdGaussian`, `charFun_stdGaussian`, `covarianceBilin_stdGaussian`,
`stdGaussian_map (f : E ≃ₗᵢ[ℝ] F)`, `map_pi_eq_stdGaussian`), `multivariateGaussian μ S := (stdGaussian E).map (fun x ↦ μ + toEuclideanCLM (CFC.sqrt S) x)`,
`Measure.conv μ ν = (μ.prod ν).map (fun p ↦ p.1 + p.2)` (via `mconv`), `Measure.map_prod_map`, `IsGaussian.ext`, `covarianceBilin_map`,
`charFun_map_smul`, `MeasureTheory.L2.inner_def (f g : α →₂[μ] E) : ⟪f, g⟫ = ∫ a, ⟪f a, g a⟫`, `MemLp.toLp`, `MemLp.coeFn_toLp`,
`IndepFun.integral_mul_eq_mul_integral`, `Lp.coeFn_add`, `Lp.coeFn_smul` (a.e. statements).

## Candidates v1 (Claude)

**M. The ULA update as a random map.** For a probability measure `μ` on `E` and `h ≥ 0`:
- (M1) `(stdGaussian E).map (fun ξ => c • ξ) = multivariateGaussian 0 ((c ^ 2) • (1 : Matrix ι ι ℝ))` for `c : ℝ` (so `√(2h) ξ ~ N(0, 2h I)`).
- (M2) `(μ.prod (multivariateGaussian 0 R)).map (fun p => euclid A p.1 + p.2) = gaussStep A R μ` (the "sampling map" form: `Measure.map_prod_map`
  and the definition of `conv`).
- (M3) `(μ.prod (stdGaussian E)).map (fun p => euclid A p.1 + Real.sqrt (2 * h) • p.2) = gaussStep A ((2 * h) • 1) μ`: the law of the ULA update
  `w ↦ (I - hP) w + √(2h) ξ`, `ξ ~ N(0, I)` independent of `w`, is `gaussStep`. Hence (with the uniqueness tide) the ULA chain as
  implemented converges in law to `N(0, Σ_ULA)`.
Optional (M4): the ULA transition kernel `κ x := multivariateGaussian (euclid A x) ((2h)•1)` as a `Kernel E E` with `μ.bind κ = gaussStep …` (deferred
unless cheap).

**B. The finite-chain theorem for real random variables.** Let `(Ω, P)` be a probability space, `η : Fin C → ℕ → Ω → ℝ` with
`MemLp (η c k) 2 P` and the second-moment table `∫ ω, η c j ω * η c' k ω ∂P = if c = c' ∧ j = k then v else 0`. Define the realised chains
`x c 0 = 0`, `x c (k+1) = ρ * x c k + η c (k+1)` (pointwise), so `x c k ∈ L²`. Then
`∫ ω, ((1/(C N)) ∑_{c,i<N} (x c (b+1+i) ω)^2 - ((1/(C N)) ∑_{c,i<N} x c (b+1+i) ω)^2) ∂P = σ²(N - R₂)/N - σ²(T_N - R₁²)/(C N²)`,
i.e. the note's `ar1_expected_sample_variance` as a statement about the expected pooled sample variance of real chains.
Proof plan: build `AR1Chain (Lp ℝ 2 P) ρ v` from `MemLp.toLp` of the `x c k` and `η c k` (fields via `toLp` linearity and `L2.inner_def`),
apply `pooled_sample_variance`, then identify `‖f‖^2 = ∫ f²` and inner products of `toLp`s with the pointwise integrals (a.e. rewriting with
`MemLp.coeFn_toLp`, `Lp.coeFn_add`, `Lp.coeFn_smul`, `Lp.coeFn_sum`?). Second-moment orthogonality from pairwise independence + centring is a
separate corollary (`IndepFun.integral_mul_eq_mul_integral`).

## Questions
1. Are M1–M3 and B correctly stated? Any hypothesis missing (measurability, `0 ≤ h`, `0 < N`, `0 < C`, `|ρ| < 1`)?
2. M1: cleanest route (`IsGaussian.ext` with `covarianceBilin_map` and `covarianceBilin_stdGaussian`, vs `Measure.ext_of_charFun` with
   `charFun_map_smul` and `charFun_stdGaussian`)? Is `CFC.sqrt (c^2 • 1) = c • 1` available to go through the definition instead?
3. M2/M3: exact Mathlib lemmas to rewrite `(μ.prod ν).map (fun p => L p.1 + p.2)` as `((μ.map L).prod ν).map (fun p => p.1 + p.2)`
   (`Measure.map_prod_map` needs measurability side conditions; `Measure.map_map`), and how `Measure.conv` unfolds (`Measure.conv`/`mconv` definitional?).
4. B: the least painful way to move between pointwise real random variables and `Lp ℝ 2 P` elements: define the chain in `Lp` from the start
   (`x (k+1) := ρ • x k + η (k+1)` in `Lp`) and only at the end identify `‖·‖²` and inner products with integrals of the pointwise statistic
   (requires a.e. identities for finite sums and scalar multiples of `Lp` elements), or define pointwise and prove `MemLp` inductively?
   Which `Lp` coercion lemmas are load-bearing (`Lp.coeFn_add`, `Lp.coeFn_smul`, `Lp.coeFn_sum`/`Lp.coeFn_finset_sum`?, `L2.inner_def`,
   `Lp.norm_def`, `MemLp.toLp_add`, `MemLp.toLp_const_smul`, `MemLp.toLp_zero`)?
5. Is M + B a coherent single excursion, or should one be dropped? Anything bigger nearby (e.g. the ULA chain on the path space `ℕ → E` as a
   Markov chain with `Kernel`, or the L² Langevin chain along one eigendirection realising the AR(1) with `η_k = √(2h) ξ_k`)?
Please end with a one-line vote for a single target cluster.
