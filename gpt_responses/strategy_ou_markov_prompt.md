# Strategy consult: the Markov / transition-kernel property of the pathwise OU process in Lean 4 + Mathlib (v4.33.0 pin)

## What exists (all machine-checked, zero sorry; file attached: OUBrownian.lean)

Setting: `ι` finite, `E := EuclideanSpace ℝ ι`, `H σ : Matrix ι ι ℝ`, `Hᵀ = H`.
`ouFlow H s := exp(−sH)`, `ouCovInt H D s := ∫₀ˢ e^{−uH} D e^{−uH} du`.

* `structure IsBrownianVec (W : ℝ≥0 → Ω → E) (P : Measure Ω) : Prop` with fields
  `gauss : IsGaussianProcess W P`, `centered : ∀ t i, P[fun ω => W t ω i] = 0`,
  `cov : ∀ s t i j, cov[fun ω => W s ω i, fun ω => W t ω j; P] = if i = j then min s t else 0`,
  `cont : ∀ᵐ ω ∂P, Continuous fun t => W t ω`.
* `ouProcess W H σ x₀ s ω := toLp 2 (ouSol H σ (ofLp x₀) (fun u => ofLp (W (toNNReal u) ω)) s)`,
  where `ouSol H σ x₀ w s = e^{−sH} x₀ + σ w_s − ∫₀ˢ e^{−(s−u)H} H σ w_u du` (pathwise, integration by parts;
  it solves `X_s = x₀ − ∫₀ˢ H X_u du + σ w_s` and is the unique continuous solution).
* `ou_marginal_law : P.map (ouProcess W H σ x₀ s) = multivariateGaussian (e^{−sH} x₀) (ouCovInt H (σσᵀ) s)` for `s ≥ 0`,
  proved via: increment sums `∑ₖ e^{−(s−uₖ)H} σ (W_{uₖ₊₁} − W_{uₖ})` over the uniform partition are Gaussian
  (`IsGaussianProcess.hasGaussianLaw_increments` + a CLM), converge a.s. to `X_s − e^{−sH}x₀`
  (deterministic Abel summation lemma `tendsto_incrementSum`), variances converge (Riemann sums),
  characteristic functions pass to the limit (`tendsto_integral_of_dominated_convergence`), `Measure.ext_of_charFun`.
* Also available: `ouStep H S s μ := (μ.map e^{−sH}) ∗ N(0, Σ_s)` with the semigroup identity, `ouCovInt_eq_ouCov` under Lyapunov,
  `ouCovInt_posSemidef`, the deterministic uniqueness `ouSol_unique`.

Mathlib API on this pin that looks relevant:
* `IsGaussianProcess.indepFun_of_covariance_eq_zero {X : S → Ω → ℝ} {Y : T → Ω → ℝ} (hXY : IsGaussianProcess (Sum.elim X Y) P) (mX) (mY) (h : ∀ s t, cov[X s, Y t; P] = 0) : IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P`
* `IsGaussianProcess.iIndepFun_of_covariance_eq_zero` (families), `HasGaussianLaw.iIndepFun_of_covariance_*`, `iIndepFun.hasGaussianLaw`, `IndepFun.hasGaussianLaw`.
* `IndepFun.charFun_map_add_eq_mul`, `charFun_conv`, `Measure.ext_of_charFun` (finite measures on complete second-countable inner product spaces; `E × E` with the product inner product is fine, or `WithLp 2 (E × E)`).
* `Measure.compProd`, `Kernel`, `ProbabilityTheory.condDistrib` (regular conditional distribution), `condDistrib_ae_eq_of_measure_eq_compProd`-style lemmas, `Measure.map_prod_map`, `Measure.prod`.
* `IndepFun` is defined via comap σ-algebras; `IndepFun.comp` with measurable maps; independence of a.e.-limits is not directly available.
* `MeasureTheory.Filtration`, `Adapted`, but no Itô integral; nothing about strong Markov.

## The question

We want the *process-level* content of "the OU equation driven by Brownian motion is the Markov process with transition kernel `ouStep`", without Itô calculus. Candidate formal statements, from weakest to strongest:

(A) **Two-time law.** For `0 ≤ s`, `0 ≤ r`: `P.map (fun ω => (X s ω, X (s+r) ω)) = (P.map (X s)) ⊗ₘ κ_r` where `κ_r : Kernel E E`, `κ_r x = multivariateGaussian (e^{−rH} x) (ouCovInt H (σσᵀ) r)`.

(B) **Independent increment decomposition.** `X (s+r) = e^{−rH} X s + Y_{s,r}` a.s., where `Y_{s,r}` is the pathwise Wiener integral over `[s, s+r]`, `Y_{s,r} ~ N(0, C_r)`, and `Y_{s,r}` is independent of `X s` (as random variables), or of the σ-algebra `⨆_{u ≤ s} MeasurableSpace.comap (W u)`.

(C) **Conditional law.** `condDistrib (X (s+r)) (X s) P =ᵐ[P.map (X s)] κ_r`, or the Markov property w.r.t. the natural filtration of `W`.

(D) **Finite-dimensional distributions** for all `0 ≤ s₁ < … < sₙ` as an iterated compProd (Chapman–Kolmogorov, `ouStep_semigroup` already proved).

Questions:
1. Which of (A)–(D) is the right target, given the tools above? Is (A) enough to be called "the transition kernel", and does (C) follow from (A) cheaply on this pin?
2. Proof route for the independence in (B): the natural argument is that the increment-sum approximants of `Y_{s,r}` (increments of `W` in `[s, s+r]`) and of `X s − e^{−sH}x₀` (increments in `[0, s]`) are jointly Gaussian with zero cross-covariance, hence independent; then pass to the a.s. limit. Is the cleanest way to pass independence to the limit via characteristic functions of the *pair* (`charFun (P.map (Xn, Yn)) = charFun … × charFun …` for each `n`, then dominated convergence on `E × E` and `Measure.ext_of_charFun`, giving `P.map (X s, Y) = (P.map (X s)).prod (P.map Y)`)? Or is there a Mathlib route through `IndepFun` and σ-algebras that avoids product-space characteristic functions? Watch for: `Measure.ext_of_charFun` needs an inner product space; `E × E` has the sup norm in Mathlib, so we would use `WithLp 2 (E × E)` or `EuclideanSpace ℝ (ι ⊕ ι)`.
3. Is it better to avoid independence altogether and prove (A) directly: compute `charFun` of the pair `(X s, X (s+r))` from the Gaussian approximants (the pair of approximants is a CLM image of the joint increment vector over `[0, s+r]`, hence Gaussian with an explicitly computable covariance), pass to the limit, and identify with the charFun of `μ_s ⊗ₘ κ_r` (which is `∫ charFun(κ_r x)(t₂) e^{i⟨x,t₁⟩} dμ_s(x)`, a Gaussian integral)? Which route has fewer moving parts?
4. Any hypothesis we are missing (e.g. `0 ≤ s` and `0 ≤ r` only; symmetry of `H`; whether `W_0 = 0` is needed for the shifted path; measurability of `X s` vs a.e.-measurability for `compProd`)?
5. Rough size in lines for the recommended route, and a sub-task list.
