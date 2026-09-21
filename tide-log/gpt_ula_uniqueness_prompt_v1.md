# Context for a Lean 4 / Mathlib formalisation step (tide `ula-uniqueness`, seabed `laplace`)

Formalised so far (laplace, `Laplace/Sampler/`), on `Matrix ι ι ℝ` and `EuclideanSpace ℝ ι`:
- `covStep A N X = A * X * Aᵀ + N`; `lyapunovVia_fixed_iff` (unique fixed point for `A = U diag(a) Uᵀ`, `U` orthogonal, `|a i| < 1`);
  `covStep_iterate_sub_fixed : (covStep A N)^[k] X₀ - S = A^k * (X₀ - S) * (Aᵀ)^k` for any fixed point `S`;
  `covStep_iterate_zero : (covStep A N)^[k] 0 = S - A^k * S * (Aᵀ)^k`; `orthoOf`, `spectral_real : A = orthoOf hA * diagonal (eigenvalues) * (orthoOf hA)ᵀ`.
- `ulaStep P h = 1 - h • P`, `ulaCov P h = (P - (h/2) • P²)⁻¹`, `ulaCov_fixed`, `ulaCov_posDef`, `ulaStep_eq_conj : ulaStep P h = U * diagonal (fun i => 1 - h * p_i) * Uᵀ`.
- New (tide `ula-invariance`, being merged): `euclid A := toEuclideanCLM (𝕜 := ℝ) A`; `euclid_adjoint : (euclid A).adjoint = euclid Aᵀ`;
  `multivariateGaussian_map_euclid : (N(m,S)).map (euclid A) = N(euclid A m, A S Aᵀ)` (PSD `S`);
  `multivariateGaussian_conv : N(m,S) ∗ N(b,R) = N(m+b, S+R)`; `multivariateGaussian_map_conv`;
  `invariant_of_covStep_fixed : (N(0,S).map (euclid A)) ∗ N(0,R) = N(0,S)` when `covStep A R S = S`; `ulaCov_invariant`;
  `gaussStep A R μ := (μ.map (euclid A)) ∗ N(0,R)`; `gaussStep_iterate : (gaussStep A R)^[k] (N(m₀,S₀)) = N(euclid (A^k) m₀, (covStep A R)^[k] S₀)`;
  `gaussStep_iterate_zero : (gaussStep A R)^[k] (N(0,0)) = N(0, S - A^k S (Aᵀ)^k)` for a fixed point `S`.

Mathlib (pin Sep 2026), checked: `charFun_apply : charFun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ` (rfl), `charFun_zero : charFun μ 0 = μ.real univ`,
`norm_charFun_le_one`, `continuous_charFun : Continuous (charFun μ)` (in `MeasureTheory/Measure/CharacteristicFunction/TaylorExpansion.lean`, check
its hypotheses), `charFun_conv`, `charFun_multivariateGaussian (hS : S.PosSemidef) x = exp (⟪x, μ⟫ * I - x ⬝ᵥ S *ᵥ x / 2)`,
`Measure.ext_of_charFun`, `charFun_map_eq_charFunDual_smul` (dual form), `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`, `tendsto_pi_nhds`,
`tendsto_finset_sum`, `Filter.Tendsto.mul_const`, `tendsto_nhds_unique`. Lévy's continuity theorem: `Mathlib/Probability/CentralLimitTheorem.lean`
exists in the pin, so a form of `ProbabilityMeasure.tendsto_iff_tendsto_charFun` is likely present (name to be checked).

## Candidates v1 (Claude)

**U. Uniqueness of the invariant law.** Let `A` be real symmetric with an orthogonal diagonalisation `A = U diag(a) Uᵀ`, `|a i| < 1`, and
`R` PSD; let `S` be the fixed point of `covStep A R` (so `S = lyapunovVia U a R`). If a probability measure `μ` on `EuclideanSpace ℝ ι`
satisfies `(μ.map (euclid A)) ∗ N(0,R) = μ`, then `μ = N(0, S)`.
Proof sketch via characteristic functions: (i) `charFun (μ.map (euclid A)) t = charFun μ (euclid Aᵀ t)` (from `charFun_apply`, `integral_map`,
`adjoint_inner_left`/`inner_toEuclideanCLM`); (ii) invariance gives `charFun μ t = charFun μ (Aᵀ t) · exp(-(t ⬝ᵥ R *ᵥ t)/2)`; iterating,
`charFun μ t = charFun μ ((Aᵀ)^n t) · exp(-(t ⬝ᵥ ((covStep A R)^[n] 0) *ᵥ t)/2)` because `(covStep A R)^[n] 0 = ∑_{j<n} A^j R (Aᵀ)^j`
(induction) and the quadratic forms add; (iii) `(covStep A R)^[n] 0 = S - A^n S (Aᵀ)^n → S` and `(Aᵀ)^n t → 0` since `A^n = U diag(a^n) Uᵀ`
with `a_i^n → 0`; (iv) `charFun μ` is continuous with `charFun μ 0 = 1`, so `charFun μ t = exp(-(t ⬝ᵥ S *ᵥ t)/2) = charFun N(0,S) t`;
(v) `Measure.ext_of_charFun`. For the ULA step (`A = ulaStep P h`, `R = (2h)•1`, `P ≻ 0`, `0 < h p_i < 2`) this says `N(0, Σ_ULA)` is the
*unique* invariant probability law, with no moment assumption on `μ`.

**C. Convergence of the Gaussian marginals.** Under the same hypotheses, from any Gaussian start `N(m₀, S₀)` (PSD `S₀`), the marginal laws
`μ_k = N(A^k m₀, S_k)` satisfy `charFun μ_k t → charFun N(0,S) t` for every `t` (`A^k m₀ → 0`, `S_k → S` by `covStep_iterate_sub_fixed`),
hence (Lévy) `μ_k → N(0,S)` weakly. Sub-candidate C0: just the matrix limits `A^n → 0`, `(covStep A R)^[n] X₀ → S` in the matrix (Pi) topology,
which U also needs.

**D (stretch). Every invariant law has Gaussian marginals along the chain**: not needed; skip unless cheap.

## Questions
1. Is U correct as stated (any probability measure, no moment assumption)? Are the hypotheses on `A` (symmetric, `|a_i| < 1`) the right ones,
   or should it be stated for a general `A` with all eigenvalues inside the unit disc / `‖A‖ < 1` in some norm (harder)?
2. The cleanest Lean route for (i): is there a Mathlib lemma `charFun (μ.map L) t = charFun μ (L.adjoint t)` for a continuous linear `L`
   (candidate names), or should we derive it from `charFun_apply` and `integral_map`? Same for `charFun (μ ∗ ν)`: `charFun_conv` is available.
3. For (iii): the best way to get `Tendsto (fun n => A ^ n) atTop (𝓝 0)` for `A = U diag(a) Uᵀ` in Mathlib (matrix topology is the product
   topology; `Matrix.tendsto`? or go through `Matrix.diagonal` and `tendsto_pi_nhds` entrywise), and then `Tendsto (fun n => (A^n) *ᵥ t)` and
   `Tendsto (fun n => t ⬝ᵥ (A^n * S * (Aᵀ)^n) *ᵥ t)` to `0`. Is there a slicker route using `Matrix.linftyOpNormedRing` / `‖A‖ < 1`?
4. For C: the exact name/form of Lévy's continuity theorem in the pin, and whether weak convergence is worth including or only pointwise charFun
   convergence (C without Lévy) should be the target.
5. Anything incorrect or a better/bigger nearby target of comparable size?
Please end with a one-line vote for a single target cluster.
