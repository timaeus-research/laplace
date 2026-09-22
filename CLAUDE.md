# CLAUDE.md

Lean 4 + Mathlib formalisation of Laplace asymptotic expansions and Wick
contractions, following the SLT Susceptibility Primer (Elliott & Murfet, 2026).

## Project Goal

Formalise the routine "boring" calculations from the primer, starting small:

1. **Stage 1** — 1D centred Gaussian moments via integration by parts:
   `∫ x^(2k) e^{-x²/2}/√(2π) dx = (2k-1)!!`. Self-contained warm-up.
2. **Stage 2** — Anharmonic 1D Laplace expansion: for
   `L(w) = (λ/2)w² + (α/6)w³`, prove `Cov_t[w², w] = -2α/(λ³t²) + o(t⁻²)`.
   This is eq. (4.10) in the primer and the first concrete payoff.
3. **Stage 3** — Multivariate `Cov_t[φ, ψ] = (1/t)⟨∇φ, Σ ∇ψ⟩ + O(t⁻²)`
   (`lem:laplace_cov`). Requires building Wick contractions on `R^d`.

Source paper: `papers/SusceptibilityPrimer_main.tex` in the SRI repo.

## Tooling

### `scripts/lean-search`

Python wrapper around https://leansearch.net/ for semantic Mathlib search.

```bash
scripts/lean-search "gaussian moment integration by parts"
scripts/lean-search "Isserlis theorem"
scripts/lean-search "asymptotic expansion of integral"
```

Mathlib also exposes LeanSearch from inside Lean via the `LeanSearchClient`
package (auto-imported via Mathlib): `#leansearch "..."` in a `.lean` file.

### `scripts/sorries`

Audit `sorry`, `#exit`, `native_decide`, `axiom` across the codebase.

```bash
scripts/sorries
```

### Searching Mathlib directly

`rg` through the Mathlib source is the fastest first move (~0.2s):

```bash
rg 'isserlis|gaussian.*moment' .lake/packages/mathlib/Mathlib/
```

When you find a candidate lemma, confirm with `#check @TheName` in a scratch
file or via the Lean LSP in your editor.

## Build commands

```bash
lake exe cache get   # Download prebuilt Mathlib oleans (run after fresh clone or lake clean)
lake build           # Build the Laplace library (full)
```

The Mathlib cache is essential — building Mathlib from source is ~30+ min;
pulling the cache is ~1 min.

### Prefer the MCP Lean server for incremental checking

`lake build` is slow (~20-60s per file even when warm). For iterative
proof work, **use the project-local MCP server** registered in `.mcp.json`,
which wraps a persistent `lake serve` LSP. Tools exposed (Claude Code
namespaces them as `mcp__lean__<tool>`):

- `mcp__lean__lean_run_code` — run an ad-hoc Lean snippet (`#check`, `#eval`, mini-proof). Replaces "edit a scratch file and call `lake env lean` via Bash".
- `mcp__lean__lean_diagnostic_messages` — get errors/warnings for a file from the live LSP. Sub-second after warm.
- `mcp__lean__lean_goal` — proof state at a position. Useful while iterating on a tactic block.
- `mcp__lean__lean_hover_info`, `mcp__lean__lean_completions` — definition lookup, completions.
- `mcp__lean__lean_leansearch`, `mcp__lean__lean_loogle`, `mcp__lean__lean_leanfinder` — Mathlib semantic / pattern search.

Use `lake build` only as a final-verification fallback, or to refresh
oleans after a structural change. The MCP server is much faster and
keeps the iteration prefix small (cheaper sessions).

The MCP server runs `uvx --from lean-lsp-mcp lean-lsp-mcp` against this
project root. First invocation downloads the package (~30s, cached
thereafter); subsequent calls are sub-second. If the server appears
stuck, restart Claude Code or kill stale `lake serve` processes
(`pkill -f lake; pkill -f lean`).

## Lean / Mathlib conventions

- Toolchain pinned to `v4.29.0` in `lean-toolchain`; Mathlib pinned to the
  matching `v4.29.0` tag in `lakefile.toml`.
- Use `↦` (not `=>`) for lambda arrows: `fun x ↦ ...`
- Avoid `native_decide` — sidesteps the kernel's trust boundary. Prefer
  `decide +kernel`. We have no certificates here so this should not come up.
- Avoid `@[implemented_by]`, `@[extern]`, `unsafePerformIO` entirely.
- Prefer algebraic notation: `1` not `ContinuousLinearMap.id ℝ _`.

## Proof workflow

**Skeleton correctness > filling sorries.** A `sorry` with a correct statement
is valuable; a `sorry` with a wrong statement actively misleads. When auditing
reveals a wrong statement, fix the statement first.

**Verify against the primary source.** The primer is the ground truth. Always
re-read the relevant section before committing to a proof structure.

**Estimate before attacking a sorry.** Quick estimate of probability of direct
proof (e.g. 30%, 60%, 80%). If <50%, factor into intermediate lemmas first.

**Recognise thrashing.** After 3+ failed approaches to the same goal, stop and
ask the user. Signs: oscillating between approaches, growing helper count
without progress, repeated restructuring.

**Sanity-check formulas empirically.** Before a long proof, write a Python
script with `numpy`/`scipy.integrate.quad` that evaluates the formula at
specific parameter values and compares to numerical integration. A mismatch at
this stage is much cheaper to find than mid-proof. The primer's
`figures/plot1_convergence.png` already does this for the example formulas.

**"Easy to see" in papers is a red flag.** When the primer says a formula
"follows by Wick" without listing the contractions explicitly, write out all
contractions before formalising — formalisation needs every term named.

## Mathlib API reference (build out as we go)

### Gaussian / Gamma integrals

- `Real.Gamma_eq_integral {s : ℝ} (hs : 0 < s) : Gamma s = ∫ x in Ioi 0, exp(-x) * x^(s-1)`
- `Real.Gamma_nat_add_half (k : ℕ) : Gamma (k + 1/2) = (2*k - 1)‼ * √π / 2^k`
  (in `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`)
- `integral_rpow_mul_exp_neg_mul_rpow {p q b : ℝ} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) : ∫ x in Ioi 0, x^q * exp(-b * x^p) = b^(-(q+1)/p) * (1/p) * Gamma((q+1)/p)`
  (in `Mathlib.MeasureTheory.Integral.Gamma`)
- `integral_gaussian (b : ℝ) : ∫ x : ℝ, exp(-b * x^2) = √(π/b)` (full real line, `b ≥ 0`)
- `integral_gaussian_Ioi (b : ℝ) : ∫ x in Ioi 0, exp(-b * x^2) = √(π/b) / 2` (half line, `b > 0`)

### Symmetry / substitution

- `integral_comp_abs : ∫ x : ℝ, f|x| = 2 * ∫ x in Ioi 0, f x`
  (in `Mathlib.MeasureTheory.Measure.Lebesgue.Integral`)
- `integral_neg_eq_self f μ : ∫ x, f(-x) ∂μ = ∫ x, f x ∂μ` (needs `μ.IsNegInvariant`, holds for `volume`)
- `MeasureTheory.Measure.integral_comp_mul_right (g : ℝ → F) (a : ℝ) : ∫ x : ℝ, g(x * a) = |a⁻¹| • ∫ y : ℝ, g y`
  (in `Mathlib.MeasureTheory.Measure.Haar.NormedSpace` — note **`Measure.` prefix needed**)
- `integral_comp_rpow_Ioi_of_pos (g : ℝ → E) (hp : 0 < p) : ∫ x in Ioi 0, (p * x^(p-1)) • g(x^p) = ∫ y in Ioi 0, g y`

### Asymptotics

- `Asymptotics.IsBigO`, `Asymptotics.IsLittleO` and full API in
  `Mathlib.Analysis.Asymptotics.Defs` / `Lemmas` / `AsymptoticEquivalent`.
- Notation: `f =O[l] g`, `f =o[l] g`, `f ~[l] g`.

### Double factorial

- `Nat.doubleFactorial : ℕ → ℕ`, notation `n‼` (scope `Nat`)
- `Nat.doubleFactorial_add_two : (n+2)‼ = (n+2) * n‼`
- `Nat.doubleFactorial_pos : 0 < n‼`


### Real spectral theorem and matrix Lyapunov idioms (Sampler arc)

`Matrix.IsHermitian.spectral_theorem` (Mathlib pin of Sep 2026) reads
`A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))`.
Over `ℝ`, unfold with `Unitary.conjStarAlgAut_apply` (the `Matrix.`-prefixed name is gone),
turn `star U` into `Uᵀ` with `Matrix.star_eq_conjTranspose` +
`Matrix.conjTranspose_eq_transpose_of_trivial`, and close
`diagonal (RCLike.ofReal ∘ eigenvalues) = diagonal eigenvalues` with `congr 1` **alone**
(a following `funext`/`simp` errors with "no goals"). Packaged as `Laplace.Sampler.orthoOf`
/ `spectral_real` / `orthoOf_transpose_mul` / `orthoOf_mul_transpose`.

Orthogonality of `eigenvectorUnitary` as a real matrix: `Matrix.mem_unitaryGroup_iff` +
`Matrix.UnitaryGroup.star_mul_self`. Determinant of a symmetric matrix:
`hA.det_eq_prod_eigenvalues` (then `RCLike.ofReal_real_eq_id`). Positivity transport:
`Matrix.PosDef.diagonal` and `Matrix.PosDef.conjTranspose_mul_mul_same` (needs `Function.Injective
Uᵀ.mulVec`, from `Matrix.mulVec_mulVec` and `U Uᵀ = 1`).

Discrete Lyapunov equations `X = A X Aᵀ + N`: go **spectral, not Neumann**. Solve the diagonal
case entrywise (`X_ij = N_ij / (1 - a_i a_j)`, `|a_i| < 1`), transport by orthogonal conjugation
(`Laplace.Sampler.lyapunovVia_fixed_iff`). State stability eigenvalue-wise (`|a i| < 1`); the
operator norm on `ι → ℝ` is the sup norm and does not give `‖I - hP‖₂ < 1`.

Polynomial-in-`P` inverses commute with `P`: `Matrix.mul_nonsing_inv` / `nonsing_inv_mul` with
`isUnit_iff_isUnit_det`. `I - (I - hP)² = 2h(P - (h/2)P²)` is a `module` one-liner.
`congr 1` often closes the whole goal (e.g. `2 * h * 1 / D = 2 * h / D` needs `rw [mul_one]`, not
`rfl`); don't follow it with bullets unless the goals are shown.

`simp only [f_apply_eq_sum, ...]` loops when the expansion of `(H u) i` produces `(H e_j) i`,
which matches the same lemma: use `rw` inside `Finset.sum_congr` instead. Deprecations:
`integral_finset_sum → integral_finsetSum`, `integrable_finset_sum → integrable_finsetSum`.

### Inner-product notation and chains in a real inner product space (Sampler/AR1)

`⟪x, y⟫_ℝ` is **not** global notation in the current pin: `⟪x, y⟫_𝕜` is scoped in `InnerProductSpace`
and `⟪x, y⟫` (real) in `RealInnerProductSpace`; inside a `structure … where` field the `_ℝ` form fails to
parse even after `open scoped`. Write `inner ℝ x y` explicitly; the lemmas are `real_inner_smul_left/right`,
`sum_inner`, `inner_sum`, `real_inner_comm`, `real_inner_self_eq_norm_sq`. A chain defined by a recursion
is best given an explicit closed form first (`x k = ∑ j ∈ range k, ρ ^ j • η (k - j)` avoids ℕ-subtraction
pain: `Finset.sum_range_succ'` peels the `j = 0` term and `Nat.add_sub_add_right` handles the shift).
Sums with an `if` selecting one index: `Finset.sum_eq_single` plus `omega` for the index arithmetic.
`Nat.dist` facts: `Nat.dist_eq_sub_of_le`, `Nat.dist_eq_sub_of_le_right`, `Nat.dist_self`; shifts by
`unfold Nat.dist; omega`. `sq` in `rw` rewrites the first `_ ^ 2` it sees: pass the argument, `sq (∑ …)`.
`omit [DecidableEq ι] in` must come *before* the docstring, not between it and the theorem.
### Non-separable 2D potentials via a measure-preserving shear (TwoD/Rosenbrock)

A curved valley `L(x,y) = ((x-μ)² + a(y - g x)²)/2` becomes separable under the triangular shear
`(z,u) ↦ (μ + z, u + g(μ + z))`. Build it as a `Homeomorph` (`fun_prop` for both continuities) and coerce
with `Homeomorph.toMeasurableEquiv`; measure preservation is one application of
`MeasurePreserving.skew_product (measurePreserving_add_left volume μ) hgm hg` with
`hg := Filter.Eventually.of_forall fun z => map_add_right_eq_self volume _`. State the goal as
`MeasurePreserving (fun p => …) (volume.prod volume) (volume.prod volume)` via `change` first
(`volume` on `ℝ × ℝ` is `volume.prod volume` by `rfl`). Transport integrals with
`MeasurePreserving.integral_comp'` (for a `≃ᵐ`) and integrability with
`MeasurePreserving.integrable_comp_emb h T.measurableEmbedding`; separable integrability is
`Integrable.mul_prod`, separable integrals are `integral_prod_mul`.

`convert h using 2` between `Integrable f volume` and `Integrable f (volume.prod volume)` leaves
unprovable-looking instance goals (`Measure.prod.measureSpace.toMeasurableSpace = Prod.instMeasurableSpace`).
Ascribe the type of `h` with `volume` on the product and use `h.congr (Filter.Eventually.of_forall …)`
instead of `convert`.

Polynomial observables in the shear coordinates: a coefficient matrix `c : Fin 5 → Fin 5 → ℝ` given by
vector notation `![![…], …]`, expanded with `simp only [Fin.sum_univ_five]; simp; ring`; the moment
values `![1, 0, 1/(λt), 0, 3/(λt)²]` substitute through `funext_iff`. Harmonic moment values from
`gibbsExpectation_harmonic_pow_even/odd` need `norm_num [Nat.doubleFactorial] at h` to evaluate
`(2k-1)‼` and `2*k`, then `unfold harmonicMoment; simpa using h`.

### Multivariate Gaussians on `EuclideanSpace` (Sampler/GaussianInvariance)

`ProbabilityTheory.multivariateGaussian m S` is defined for every matrix and is a Dirac mass when `S` is not
`PosSemidef`; every moment/charFun lemma (`covarianceBilin_multivariateGaussian`, `charFun_multivariateGaussian`)
needs `hS : S.PosSemidef`, so carry PSD hypotheses and prove PSD of derived matrices
(`hS.conjTranspose_mul_mul_same Aᵀ` + `conjTranspose_eq_transpose_of_trivial` gives `A * S * Aᵀ`;
`PosSemidef.add`, `PosSemidef.one.smul (by positivity)`). Matrices act through
`Matrix.toEuclideanCLM (𝕜 := ℝ) A` (a `≃⋆ₐ[ℝ]`): `ofLp_toEuclideanCLM` is `rfl`, the adjoint is the transpose via
`← ContinuousLinearMap.star_eq_adjoint, ← map_star, Matrix.star_eq_conjTranspose`, products/powers via `map_mul`/
`map_pow`. Two Gaussian measures are equal by `IsGaussian.ext` (mean: `ContinuousLinearMap.integral_id_map`
after `simp only [id_eq]`; covariance: `covarianceBilin_map IsGaussian.memLp_two_id`, then `ext u v`) or by
`Measure.ext_of_charFun` with `charFun_conv` (`∗` is `Measure.conv`, scoped in `MeasureTheory`; probability
instances for `μ ∗ ν` exist). Quadratic-form algebra: `mulVec_transpose`, `dotProduct_mulVec`, `vecMul_vecMul`.
`ContinuousLinearMap.mul_apply` is deprecated: `mul_apply_eq_comp`.

### Polar coordinates, angular integrals and big-O inductions (Patterning/FourGonSusceptibility*, HorizonSecondOrder)

- `integral_polar_sep f R Θ (hf : ∀ r > 0, ∀ θ ∈ Ioo (-π) π, r * f (r cos θ, r sin θ) = R r * Θ θ) :
  ∫ f = (∫ r in Ioi 0, R r) * ∫ θ in -π..π, Θ θ` (from `integral_comp_polarCoord_symm`,
  `polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π` by `rfl`, `Measure.volume_eq_prod`, `integral_prod_mul`; no
  integrability needed). For `radialCov`-type identities `unfold` then `beta_reduce` before `rw`,
  since `radialExpectation (fun z => φ z * ψ z)` leaves a beta-redex that blocks the pattern.
- Angular integrals of `[cos θ]₊`: split `-π..π` at `±π/2` with `integral_add_adjacent_intervals`,
  kill the outer pieces with `relu_of_nonpos` (`cos_nonpos_of_pi_div_two_le_of_le`, needs `pi_pos`
  in `linarith`), then `integral_cos_sq`, `integral_cos_pow_three`. Shift angles with
  `intervalIntegral.integral_comp_sub_right` + `Function.Periodic.intervalIntegral_add_eq hg t s`
  (explicit, not dot notation). Odd integrands vanish via `integral_comp_neg` + `integral_neg` +
  `linarith`. Feature angles `0, π/2, π, −π/2` (not `3π/2`): then `simp [cos_sub, cos_add,
  cos_pi_div_two, sin_pi_div_two, cos_pi, sin_pi]` evaluates every `cos(θⱼ − θₖ)`.
- `Laplace.gibbsExpectation` (1D) shadows `Laplace.TwoD.gibbsExpectation` inside
  `namespace Laplace.Patterning` even with `open Laplace.TwoD`: write `Laplace.TwoD.` explicitly.
  `Continuous.dotProduct` is protected. `le_or_lt` is now `le_or_gt`. `Fin.castSucc (0 : Fin 4)`
  is defeq to `(0 : Fin 5)`: state the specialisation with a type ascription (`have h0 : f 0 = … := lemma 0`).
- `polarMoment G k = ∫ r ^ (k+1) * G (r^2)`: `∫ r ^ 4 * G (r^2) = polarMoment G 3` is `rfl`.
  Splitting `∫ (r^6 G − r^4 G)` needs integrability (`integrableOn_pow_mul_exp_neg_quartic` +
  `IntegrableOn.congr_fun`), so state general-`G` lemmas only for products and do differences for the
  concrete weight. After `field_simp` a trailing `ring` may hit "no goals": use `try ring`.
- Gamma facts on the pin: `Gamma_one_half_eq`, `Gamma_add_one`, `Gamma_mul_Gamma_add_half` (real
  Legendre duplication, `2 ^ (1 - 2s)` as rpow; rewrite the exponent *before* `2 * (3/4)`),
  `convexOn_log_Gamma` (no strict version): `convexOn_log_Gamma.2 hx hy ha hb hab` at weights ½,½
  gives `Γ(3/4)² ≤ √π`. Strict inequalities then come from `pi_gt_three`.
- Big-O inductions: `isBigO_zero _ _` (explicit args), `IsBigO.bound`, `IsBigO.of_bound c (∀ᶠ …)`,
  `IsBigO.trans_tendsto h tendsto_id`, `(CLM).isBigO_comp _ l |>.trans h`, `IsBigO.const_smul_left`,
  `IsBigO.congr_left (∀ x, f₁ x = f₂ x)`. Eventual smallness from a `Tendsto` to `0`:
  `filter_upwards [h.eventually (Metric.closedBall_mem_nhds 0 hr)]` then `rwa [dist_zero_right] at hε`
  (the membership is already unfolded to `dist`). The recursion identity for the error closes with
  `module` after `simp only [gdStep, horizonIter, Matrix.sub_mulVec, Matrix.one_mulVec,
  Matrix.smul_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub, smul_add, smul_smul]`.

### Independence, kernels and conditional laws (Patterning/OUMarkov)

- `IsGaussianProcess.of_isGaussianProcess (hX) (h : ∀ s, ∃ I : Finset T, ∃ L : (I → E) →L[ℝ] F, ∀ ω, Y s ω = L (I.restrict (X · ω)))`
  is the workhorse for "finite linear combinations of a Gaussian process form a Gaussian process";
  build the CLM as a structure literal with `toFun z := (z ⟨t₂, by simp⟩ - z ⟨t₁, by simp⟩) i` on
  `({t₁, t₂} : Finset _) → E` (as in Mathlib's `IsGaussianProcess.shift`), `cont := by fun_prop`.
  Then `IsGaussianProcess.indepFun_of_covariance_eq_zero` on `Sum.elim X Y` gives independence of two
  scalar arrays from zero cross-covariance, and `IndepFun.comp` with continuous maps transports it.
- Independence passes to a.s. limits through `indepFun_iff_charFunDual_prod` (Banach-valued; no
  inner product on `E × F` needed) plus dominated convergence of `charFunDual (P.map (Zn n)) L`.
- `condDistrib Y X P` needs `[IsFiniteMeasure P]` *in the statement*; `have := hW.isProbabilityMeasure`
  inside the proof is too late. `condDistrib_ae_eq_of_measure_eq_compProd X hY (hκ : P.map (X, Y) = P.map X ⊗ₘ κ)`
  turns a two-time law into a conditional law. A kernel `x ↦ ν.map (A x + ·)` is best built as
  `Kernel.map (Kernel.deterministic id measurable_id ×ₖ Kernel.const _ ν) (fun p => A p.1 + p.2)`,
  which carries `IsMarkovKernel` via `Kernel.IsMarkovKernel.map _ hf`; `(μ.prod ν).map (x, z) ↦ (x, A x + z) = μ ⊗ₘ κ`
  by `ext S hS` with `Measure.map_apply`, `Measure.prod_apply`, `Measure.compProd_apply` and `rfl` on preimages.
- After `set w := e with hw`, `simp only [defn]` may re-expose `e`; `rw [← hw]` restores `w` before using
  hypotheses stated in terms of `w`. `WithLp.toLp 2 (fun i => x.ofLp i) = x` is closed by `simp only` (eta + `toLp_ofLp`); a trailing `rfl` errors with "no goals".
- `notes/` is gitignored in this repo: `git add -f` for handoffs and digests.
- Landing on `main` while tides land concurrently: `git fetch && git merge origin/main && git push origin branch:main`
  in one command; a `lake build` in between loses the race. The merges are unions of disjoint files.

### Matrix-valued calculus and the topology diamond (Patterning/OU*)

- `Matrix ι ι ℝ` carries the Pi topology globally and the `linftyOp` norm only as a
  `local instance`. Bare `TopologicalSpace` searches in a *statement* (`HasDerivAt`,
  `Continuous`, `ContinuousOn`) pick the Pi instance; lemmas that require a
  `SeminormedAddCommGroup` produce the norm topology. The two are defeq at default
  transparency, so `exact` works but `simpa`, `simp` and unification with an undetermined
  codomain fail. Consequences: state the codomain explicitly
  (`isCompact_Icc.exists_bound_of_continuousOn (E := Matrix ι ι ℝ) hF'.continuousOn`), prefer
  `exact ((h₁.sub h₂).congr_deriv (sub_self _))` over `simpa using h₁.sub h₂`, and never write
  `IntervalIntegrable M volume a b` or `LinearMap.toContinuousLinearMap` for a matrix-valued
  `M` (the elaborator asks for `ENormedAddMonoid (Matrix ι ι ℝ)` w.r.t. the Pi topology and
  fails). Take `Continuous M` instead and derive integrability inside the proof.
- Avoid matrix-valued integrals altogether where possible: apply the FTC to the vector path
  `u ↦ F u *ᵥ v` (`integral_deriv_mulVec_const`) or to the scalar `u ↦ x ⬝ᵥ (C u *ᵥ y)`
  (`hasDerivAt_dotProduct_mulVec`, `ouCovInt_bilin`), and get symmetry/PSD of an integral
  matrix from the derivatives of its entries (`hasDerivAt_entry`, `is_const_of_deriv_eq_zero`).
- `IsCompact.exists_bound_of_continuousOn'` (primed) is the *multiplicative* version; the norm
  bound for additive groups is the unprimed `IsCompact.exists_bound_of_continuousOn`.
- `rw [← node_last s n]` rewrites *every* `s` in the goal, including the one inside `node s n k`;
  use a `calc` step instead of rewriting the right-hand side.
- `simp_rw [heq]` with `heq : ∀ n, f n = g n` does nothing on an eta-reduced `Tendsto f`; first
  `rw [show f = fun n => g n from funext heq]`. `simp_rw` also fails if *any* lemma in the list
  makes no progress: with `set m := e with hm`, rewrite `hm` before a lemma stated in terms of `e`.
- Mathlib Brownian API on this pin: `IsGaussianProcess.hasGaussianLaw_increments` gives the joint
  law of increments along `t : Fin (n+1) → T`; combine with `HasGaussianLaw.map_fun` of a CLM
  `∑ k, (L k).comp (ContinuousLinearMap.proj k)` for weighted increment sums. Scalar covariance
  arithmetic: `covariance_fun_sub_fun_sub`, `covariance_fun_sum_fun_sum`,
  `covariance_const_mul_left/right`, `covariance_self`, all needing `MemLp _ 2` (from
  `HasGaussianLaw.memLp_two`). Characteristic functions: `HasGaussianLaw.charFun_map_eq`,
  `charFun_map_const_add`, `charFun_multivariateGaussian`, `Measure.ext_of_charFun`; limits via
  `tendsto_integral_of_dominated_convergence` with bound `1` and `Complex.norm_exp_ofReal_mul_I`;
  a.e. measurability of the limit via `aemeasurable_of_tendsto_metrizable_ae`.
- Lake 5 keeps compiled modules of dependencies in a content-addressed artifact cache, so
  `lake env lean File.lean` fails with "object file ... does not exist" for cached imports. Check
  a file with `lake build Laplace.Patterning.File` (or `lean-state`, which uses `lake setup-file`).
### Characteristic functions, matrix limits, bundled probability measures (Sampler/GaussianUniqueness)

`charFun (μ.map L) t = charFun μ (L† t)` is not in Mathlib: prove it from `charFun_apply` (rfl), `integral_map`
(`L.continuous.measurable.aemeasurable`, `by fun_prop` for the integrand) and `ContinuousLinearMap.adjoint_inner_right`.
`continuous_charFun` lives in `MeasureTheory/Measure/CharacteristicFunction/TaylorExpansion.lean`; `charFun_zero` gives
`μ.real univ`, closed by `probReal_univ`. `Measure.isProbabilityMeasure_map` (namespace `Measure`) needs `AEMeasurable`.
Lévy: `ProbabilityMeasure.tendsto_of_tendsto_charFun` in `MeasureTheory/Measure/LevyConvergence.lean`, for finite-dimensional
real inner product spaces, with `ProbabilityMeasure` bundles. Anonymous constructors `⟨μ, inst⟩ : ProbabilityMeasure E`
inside a `Tendsto` statement make instance search fail on the unfolded subtype: wrap them in a `def` (`gaussStepPM`,
`gaussianPM`) and prove equalities of `charFun ↑(…)` by `exact` (defeq), not `simpa`.
Matrix limits: the matrix topology is the Pi topology but `rw [tendsto_pi_nhds]` does not see through `Matrix`; use
`refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_` (unification unfolds the def) and `Matrix.zero_apply`;
entries of a convergent matrix sequence via `(continuous_id.matrix_elem i j).tendsto _ |>.comp hM` (`exact`, not `simpa`).
`Filter.Tendsto.const_mul`/`mul_const`/`mul` work in `Matrix ι ι ℝ`; `A^n = U diag(a^n) Uᵀ` by induction with
`diagonal_mul_diagonal`; `|a i| < 1` gives `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`. `PiLp.continuous_toLp` transports
entrywise limits to `EuclideanSpace` (`euclid M t = toLp 2 (M *ᵥ ofLp t)` by `rw [← ofLp_toEuclideanCLM]`).

### Matrix norms, contractions and the PSD cone (Sampler/FullStep)

Matrix norms are scoped: `open scoped Matrix.Norms.Operator` gives the ℓ∞-operator norm (`linfty_opNorm_mul :
‖A * B‖ ≤ ‖A‖ * ‖B‖`; transposition is *not* an isometry, keep `‖Aᵀ‖`), `Matrix.Norms.Elementwise` the sup norm,
`Matrix.Norms.Frobenius` the Frobenius norm. `CompleteSpace (Matrix ι ι ℝ)` is `FiniteDimensional.complete ℝ _`.
Affine contractions: `LipschitzWith.of_dist_le_mul` with `dist_eq_norm`, then `ContractingWith K f := ⟨K < 1, lipschitz⟩`
(`K : ℝ≥0` as `⟨k, hk⟩`), and `ContractingWith.fixedPoint`, `fixedPoint_isFixedPt`, `fixedPoint_unique`,
`tendsto_iterate_fixedPoint`. `gcongr` mis-splits products of three norms; write the `calc` by hand.
Mathlib's `Matrix.PosSemidef M` is `M.IsHermitian ∧ ∀ x : n →₀ R, 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj`
(finitely supported vectors, not `dotProduct`): prove closedness of the PSD cone entrywise (`Matrix.IsHermitian.ext`,
`tendsto_nhds_unique`) and through this double sum (`simp only [Finsupp.sum]`, `continuous_finsetSum`), with entry continuity
from `(Matrix.entryLinearMap ℝ ℝ i j).continuous_of_finiteDimensional` (the operator-norm topology instance is not the Pi
one syntactically). Finite sums of PSD matrices: `Finset.sum_induction _ (fun M => M.PosSemidef) (fun _ _ => .add) .zero`.
`rw [← hS]` for a fixed-point equation `hS : f S = S` rewrites every `S`, including inside iterates: state the needed
identity with `covStep A N S` on one side and rewrite `hS` there instead.
### `Lp` packaging and product-measure push-forwards (Sampler/AR1Real, Sampler/RandomMap)

Real random variables into `Lp ℝ 2 P`: `MemLp.toLp`; identify `inner ℝ (hf.toLp f) (hg.toLp g) = ∫ f * g` through
`L2.inner_def` + `integral_congr_ae` + `filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp]`, and `‖toLp f‖² = ∫ f²` from it via
`real_inner_self_eq_norm_sq` (never through `Lp.norm_def`). Recurrences hold in `Lp` by `rw [← MemLp.toLp_const_smul,
← MemLp.toLp_add]; rfl` (the pointwise and `Pi` forms are defeq). `toLp` of a finite sum: induction with `Finset.sum_insert`
and `← MemLp.toLp_add; rfl`. `MemLp.zero`, `MemLp.const_mul`, `MemLp.add`, `memLp_finsetSum` (the deprecated
`memLp_finset_sum` returns the `fun a => ∑ i, f i a` form). `Integrable (fun ω => f ω ^ 2)` from `(hf.integrable_mul hf)`
after `simp only [sq]; exact this` (`simpa` fails on `f * f` vs the lambda).
Push-forwards of products: `Measure.map_map` needs its functions passed explicitly (`(g := …) (f := …)`) when the goal's
lambda differs syntactically from the proof term's inferred function (`measurable_fst.add measurable_snd` is stated for
`Prod.fst + Prod.snd`); `Measure.map_prod_map` with `measurable_id` and `conv_rhs => rw [← Measure.map_id]` to introduce
`ν.map id`; `Measure.conv` unfolds by `change` to `(μ.prod ν).map (fun p => p.1 + p.2)`. `measurable_const_smul` for
`fun ξ => c • ξ`. Independence to product law: `(indepFun_iff_map_prod_eq_prod_map_map hX hξ).mp hind` and
`AEMeasurable.map_map_of_aemeasurable`. `‖t‖² = t.ofLp ⬝ᵥ t.ofLp` on `EuclideanSpace` via `real_inner_self_eq_norm_sq`
and `EuclideanSpace.inner_eq_star_dotProduct`.

### Gaussian second moments in measure form (Sampler/GaussianQuadratic)

`∫ xᵢ xⱼ ∂N(m,S) = Sᵢⱼ + mᵢ mⱼ` comes from `covarianceBilin_multivariateGaussian hS (EuclideanSpace.single i 1) (single j 1)`
rewritten with `covarianceBilin_apply IsGaussian.memLp_two_id` (`∫ ⟪eᵢ, z - μ[id]⟫ ⟪eⱼ, z - μ[id]⟫`), `integral_id_multivariateGaussian`,
`EuclideanSpace.inner_single_left`, `conj_trivial`; the single-vector quadratic form `(single i 1) ⬝ᵥ S *ᵥ (single j 1)` is closed by
`simp`. Coordinate functionals: `EuclideanSpace.proj (𝕜 := ℝ) i : StrongDual ℝ _` (pass `𝕜`), `comp_memLp'` for `MemLp 2`,
`MemLp.integrable_mul` for products, `integral_comp_comm` for the mean. `integral_add`/`integral_sub` rewrites need the
integrability facts stated for the *lambda* forms appearing in the goal (`have : Integrable (fun x => f x - g x) := hf.sub hg`),
because `hf.sub hg` alone has type `Integrable (f - g)` (Pi subtraction) and the rewrite pattern `(f - g) a` does not match
`f a - g a`. `integral_finsetSum` needs `(f := fun i x => …)` explicitly under a double sum. `Matrix.posDef_inv_iff.mpr`,
`Matrix.inv_eq_right_inv` for `(t • H)⁻¹ = t⁻¹ • H⁻¹`, `trace (H * S) = ∑ᵢⱼ Hᵢⱼ Sᵢⱼ` needs `S` symmetric (`hS.1.apply`).
A hypothesis stated with `ulaNoise h` does not rewrite a goal containing `(2 * h) • 1`: restate it with the goal's spelling
(`have hfix : covStep _ ((2 * h) • 1) _ = _ := ulaCov_fixed …`, accepted by defeq).
### Projections of Gaussian noise and pushing laws through functionals (Sampler/ULAEigen)

Work under `stdGaussian E` first, with the functional `innerSL ℝ u` (`innerSL_apply_apply : innerSL 𝕜 v w = inner v w`,
`innerSL_apply_norm : ‖innerSL 𝕜 x‖ = ‖x‖`): mean `∫ innerSL u = 0` by `(innerSL ℝ u).integral_comp_comm (μ := stdGaussian E)
(φ := id) IsGaussian.integrable_id` (pin `μ`, otherwise `IsGaussian ?μ` is stuck), second moment by
`variance_dual_stdGaussian` + `variance_of_integral_eq_zero`, `MemLp` by `IsGaussian.memLp_two_id` (implicit `μ`, give the
expected type) and `ContinuousLinearMap.comp_memLp'`. Transfer to random variables with law `P.map ξ = stdGaussian E` via
`integral_map (f := fun z => …)` and `memLp_map_measure_iff (g := fun z => …)`: pass the lambda explicitly, since the
measurability proof terms mention `⇑(innerSL ℝ u)` and the rewrite pattern would not match `inner ℝ u z`. Mutual independence
`iIndepFun ξ P` gives pairs by `hind.indepFun hij`, pushed through a functional by `IndepFun.comp (φ := …) (ψ := …)`.
When a lemma has an implicit numerical parameter fixed by one hypothesis (`white_of_indep (v := …)`), pass it: otherwise the
first `rw` that closes a goal by `rfl` assigns it to an unsimplified expression.
A deterministic projection lemma (`inner_vecChain_eq_realChain`, by induction with `inner_add_right`, `real_inner_smul_right`)
keeps all probability out of the AR(1) identification; columns of `orthoOf hQ` are unit eigenvectors by entrywise algebra from
`Q * U = U * diagonal p` (`mul_apply`, `mul_diagonal`) and `Uᵀ U = 1` (`one_apply_eq`), packaged with `WithLp.toLp 2`.

### Gaussian integrals on `ι → ℝ` by linear change of variables (Multi/GaussianMomentsPosDef)

Lebesgue measure under a matrix: `Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := Matrix.toLin' M) (h : LinearMap.det f ≠ 0)
: map f volume = ENNReal.ofReal |det f|⁻¹ • volume` with `LinearMap.det_toLin'`, `abs_inv`; hence the substitution
`∫ g = |det M| * ∫ g (M *ᵥ ·)` (`integral_map`, `integral_smul_measure`, `ENNReal.toReal_ofReal`) and
`Integrable (g ∘ M) ↔ Integrable g` (`integrable_map_measure`, `integrable_smul_measure`), both needing
`AEStronglyMeasurable g` (continuity). Matrices act on `ι → ℝ` through `LinearMap.toContinuousLinearMap (Matrix.toLin' P)`
(`matCLM`), `quadForm (matCLM P) u = u ⬝ᵥ P *ᵥ u`. Whitening `M = orthoOf hP * diagonal (√p)⁻¹`: `MᵀPM = 1`, `MMᵀ = P⁻¹`
(`Matrix.inv_eq_right_inv`, `symm` first), `|det M| = (√det P)⁻¹` from `det (MᵀPM) = 1` via `Real.sqrt_sq_eq_abs`, `Real.sqrt_inv`.
Product Gaussians: `Real.exp_sum` + `Finset.mul_sum` turn `exp(-½ Σ v_i²)` into `∏ exp(-v_i²/2)`; `integral_fintype_prod_volume_eq_prod
(fun (i : ι) (x : ℝ) => …)` (pass `f` explicitly) and `Integrable.fintype_prod` after `rw [volume_pi]`; coordinates as products
`v k * v l = ∏ i, (if i = k then v i else 1) * (if i = l then v i else 1)` (`Finset.prod_ite_eq'`), then split `k = l`
(`Finset.prod_congr` + `split_ifs`, `Finset.prod_const`) / `k ≠ l` (`Finset.prod_eq_zero`); rewrite ifs under binders with
`simpa [hkl]`, not `rw`. 1D inputs: `integral_gaussian (1/2)`, seabed `Laplace.OneD.integral_pow_mul_exp_neg_sq_half/odd`,
`integrable_pow_mul_exp_neg_half_sq`. `Finset.sum_ite_eq` (unprimed) matches `if a = x`, primed matches `if x = a`.
The seabed's `FubiniIBPHypothesis P i j` follows from the second moments: `∫ u_j (Pu)_i g = Σ_k P_ik ∫ u_k u_j g = Z (P P⁻¹)_ij`;
apply the moment theorem with indices `k j` to land on `P⁻¹ k j`.

## Monomial cumulant ladder (OneD)

The symmetric even-monomial track (`MonomialPotential`/`MonomialVariance`/`MonomialKurtosis`/`MonomialSixthCumulant`,
plus `MonomialMomentAsymptotic`) now has the even cumulants κ₂, κ₄, κ₆ of `x` against `exp(-t·x^(2k)/(2k)!)` in Gamma closed form:
`monomial_variance_even` (2nd cumulant `⟨x²⟩` cov) and `monomial_excess_kurtosis` (4th cumulant
`⟨x⁴⟩ - 3⟨x²⟩²`). RECIPE for the next rung: mirror `monomial_variance_even` verbatim — rewrite the
observable powers into `x^(2·j)` form (`rfl`, since `2*j` reduces), substitute
`gibbsExpectation_kthPotential_even` at the needed `j`s, fold the common power via
`((2k)!/t)^(a/k) = (((2k)!/t)^(1/k))^a` (`Real.rpow_add`), then `push_cast; rw [hpow]; ring` (the
Gamma ratios ride as opaque atoms; push_cast MUST precede the power rewrite so the ℕ-cast exponent
matches the ℝ-literal in the `rpow` lemma). Gaussian sanity check `k=1`: excess kurtosis `= 0`.
`monomial_sixth_cumulant` = κ₆ = ⟨x⁶⟩−15⟨x⁴⟩⟨x²⟩+30⟨x²⟩³ (Gaussian κ₆=0) + its t^(-3/k) scaling; each even moment/cumulant and its `_isEquivalent_rpow` power law now exist. POWER-FOLD for a cube: `((2k)!/t)^(3/k) = (((2k)!/t)^(1/k))^3` via `← Real.rpow_natCast _ 3` then `← Real.rpow_mul hfac_t_pos.le` + `push_cast; ring`. Ladder COMPLETE at clean frontier (general even cumulant needs Bell-polynomial/set-partition machinery).

## Proof tactics (build out as we go)

**`(2 * k : ℕ)` vs `2 * (k : ℝ)`.** Mathlib's `integral_rpow_mul_exp_neg_*` lemmas use real
exponents (`Real.rpow`) for the integrand. Our user-facing theorems use natural-number
exponents (`Monoid.npow`). Bridge for `x > 0`:
```lean
rw [show (2 * (k : ℝ) : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, rpow_natCast]
```

**Cascading `rw [(1/2) = 2⁻¹]` stomps inside exponents.** If you rewrite `(1/2)` to
`2⁻¹` while exponents like `↑k + 1/2` are still in the goal, the `1/2` inside the
exponent gets rewritten too, producing `↑k + 2⁻¹`. Fix: use `nth_rewrite` for
positional rewrites, or factor scalar arithmetic into a side `have` so the
exponent stays unmolested.

**`ring` cannot unify under `exp`.** `exp` is opaque to `ring`. For goals like
`x^n * exp(a) = x^n * exp(b)`, use `congr 2; ring` (peels one `*` and one `exp`)
rather than plain `ring`.

**`positivity` proves `0 < x` and `0 ≤ x`, not `c < x` for nonzero `c`.** For
`(-1 : ℝ) < 2 * (k : ℝ)`, use
`by have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith`.

**Even-function symmetry: cleanest path is `integral_comp_abs`.** Phrase the
integrand as `f(|x|)` and then `integral_comp_abs` directly gives `2 * ∫_{Ioi 0} f`.
For `x^(2k)` (even Nat power):
```lean
rw [show x^(2*k) = |x|^(2*k) from by rw [pow_mul x 2 k, ← sq_abs x, ← pow_mul]]
```
For `x^2`: `(sq_abs x).symm` gives `x^2 = |x|^2`.

**Matrix/vector idioms from the Patterning arc.** `Σ` is the sigma-type token and cannot
name a binder (use `S`). `Matrix.smul_mulVec : (b • M) *ᵥ v = b • M *ᵥ v` (there is no
`smul_mulVec_assoc`); `Matrix.mulVec_transpose : Aᵀ *ᵥ x = x ᵥ* A`;
`Matrix.dotProduct_mulVec : v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w`, while `dotProduct_comm/sub/neg/zero`
live at the root. `Matrix.diagonal_add/sub` are oriented
`diagonal a - diagonal b = diagonal fun i => a i - b i`; `Matrix.diagonal_smul :
diagonal (r • d) = r • diagonal d`, so `← diagonal_smul` pulls a scalar inside.
`Matrix.trace_one : trace 1 = Fintype.card n` (as a cast). For `U diag(a) Uᵀ` algebra,
prove `(U diag a Uᵀ)⁻¹ = U diag a⁻¹ Uᵀ` via `Matrix.inv_eq_left_inv` and reuse it
(`Profile.lean`: `inv_spectral`, `spectral_mul_spectral`, `trace_spectral`).
Deprecations on this pin: `tendsto_finset_sum → tendsto_finsetSum`,
`Set.mem_setOf_eq → Set.mem_ofPred_eq`. For derivatives of products use
`h.congr_deriv (by simp only [id_eq, Pi.neg_apply]; ring)` rather than `convert h using 1`,
which leaves instance-mismatch goals. `field_simp` only clears a denominator whose
nonzero-ness hypothesis matches syntactically (`2 - lam * η ≠ 0` is not `2 - η * lam ≠ 0`).

**Analysis idioms from the Patterning fundamentals (Jacobi, RadialVirial, GaussianFourth).**
The `∫ x in s, body` notation parses `body` at precedence 60, so `∫ f + c * ∫ g` is
`∫ (f + c * ∫ g)`: parenthesise `(∫ x in s, f x) + c * (∫ x in s, g x)`. `HasDerivAt.sum` produces
the Pi-sum `∑ i, A i` as the function; use `HasDerivAt.fun_sum` for `fun y ↦ ∑ i, A i y`, or
`congr_of_eventuallyEq` with `Finset.sum_apply`. There is no `HasDerivAt.finset_prod` on this
pin; `Jacobi.lean` has `hasDerivAt_finset_prod` by induction. `Matrix.det_apply'` gives the
Leibniz sum with a real sign `((sign σ : ℤ) : ℝ)`; column replacement branches on `j = i`
(`updateCol_self/ne`), and `cramer_apply` + `cramer_eq_adjugate_mulVec` turn the column-replaced
sum into `tr(adj A · B)`. With `open Matrix`, `add_apply`/`smul_apply` are ambiguous with
`Matrix.add_apply`: write `_root_.add_apply`. `field_simp` normalises *inside* integrands and
breaks syntactic matching with an earlier `have`; clear denominators by hand
(`eq_sub_iff_add_eq`, `← mul_div_assoc`, `← add_div`, `div_eq_iff`) when a hypothesis must be
reused. Distributing `(∑ i, ∑ j, f) * (∑ k, ∑ l, g) * K` with `simp only [Finset.sum_mul,
Finset.mul_sum]` fixes the nesting order to (i, j, k, l); `rw [Finset.sum_mul_sum]` then
`simp only [Finset.sum_mul_sum]`, then `simp only [Finset.sum_mul]` gives (i, k, j, l); state the
expanded form in whichever order the tactic produces and never rely on `simp` to permute
four-fold sums (use `Finset.sum_comm` under `conv` and match the trace expansion order
`(i, l, k, j)` of `tr(A S B T)`). `integral_finset_sum`/`integrable_finset_sum` are
`integral_finsetSum`/`integrable_finsetSum`; rewriting `∫ ∑∑ f` needs the summand function
passed explicitly (higher-order pattern), see `integral_sum2`/`integral_sum4`. Stein in a
non-coordinate direction: `stein_quadKernel` with `v = toEuclideanCLM H⁻¹ (single a 1)`, using
`inner_toEuclideanCLM`, `ofLp_toEuclideanCLM`, `dotProduct_mulVec`, `← mulVec_transpose` and the
symmetry `Hᵀ = H` from `hH.1.eq` via `conjTranspose_eq_transpose_of_trivial`; `LowPoly`
(`MonomialVisibility.lean`) supplies smoothness and growth of monomials and of their
directional derivatives (`LowPoly.deriv_dir`), and `EuclideanSpace.proj i |>.hasFDerivAt.mul`
gives the explicit product-rule derivative. `Matrix.PosDef.det_pos` lives in
`Mathlib/Analysis/Matrix/PosDef.lean`.

**Idioms from the parallel Patterning round (HorizonNonlinear, IsotropicExpansion, VolumeExponent,
MovingMinimizer, PosteriorSusceptibility).** Parity of Gaussian moments is free via
`MeasureTheory.Measure.integral_comp_smul` with `R = -1` (odd integrands against an even kernel
integrate to zero), which replaces Stein computations of fifth moments. Scaling a Gaussian's
precision by `σ⁻²` is `integral_dilation` on numerator and denominator (no integrability needed).
The moving critical point of an implicit equation `G s w = 0` is best obtained from the inverse
function theorem on `Φ(s,w) = (s, G s w)` (`HasStrictFDerivAt.localInverse`,
`localInverse_apply_image`, `eventually_right_inverse`, `to_localInverse`), packaging the derivative
as a `ContinuousLinearEquiv` via `ContinuousLinearEquiv.equivOfInverse` with an explicit inverse built
from `LinearMap.toContinuousLinearMap (Matrix.toLin' H⁻¹)`; Mathlib's implicit-function API is more
awkward. `tendsto_log_mul_rpow_nhdsGT_zero` is root-namespace (not `Real.`); `ε^a (−log ε)^n → 0`
follows from it with exponent `a/(n+1)`, no induction. `pow_sub₀` is stated with `* (·)⁻¹` on this
pin, so `div_eq_mul_inv` first. The primer's hypothesis packages (`PotentialJetApprox`,
`LaplaceCovHypotheses`) survive adding a quadratic localiser `(ρ/2)‖w‖²` with Hessian `H + ρ·id`;
`FubiniIBPHypothesis` stays an input (the repo never derives it). Trailing `ring` after a closing
`field_simp` errors with "no goals".

**Mathlib namespace gotchas.** Some lemmas live under deeper namespaces than
expected. `integral_comp_mul_right` is `MeasureTheory.Measure.integral_comp_mul_right`,
not `MeasureTheory.integral_comp_mul_right`. When in doubt, write a scratch
`#check @SomeName` snippet via `lake env lean /tmp/probe.lean`.

**`rpow_natCast` for converting Nat to Real powers.** `x ^ ((n : ℕ) : ℝ) = x ^ n`
unconditionally. Use it when the goal mixes `x^(n:ℝ)` (rpow) with `x^(n:ℕ)` (npow).

**Pi.add vs single-lambda mismatch in `rw [MeasureTheory.integral_add ...]`.**
`Integrable.add` returns `Integrable (f + g)` where `f + g` is `Pi.add` —
*not* a single lambda `fun u => f u + g u`. When `rw [MeasureTheory.integral_add (h1.add h2) h3]`
fires, Lean's pattern-matcher tries to syntactically match
`∫ a, ((fun x => ...) + fun x => ...) a + h3.f a` (Pi.add over lambdas)
against the goal `∫ u, T1 u + T2 u + T3 u`. Beta-reduction is automatic
in `rw`, but Pi.add unfolding is *not*. Symptom: `rewrite failed: did not
find an occurrence of the pattern` even though the math is correct.

Workaround: introduce a *type-ascribed* single-lambda integrability
witness:

```lean
have h_12 : Integrable (fun u : ι → ℝ => T1 u + T2 u) volume := h1.add h2
-- ... now `MeasureTheory.integral_add h_12 h3` matches cleanly because
-- h_12.f IS a single lambda, so the pattern reduces under beta only.
```

The same class occurs for **`Pi.div`**: `isEquivalent_iff_tendsto_one`
produces a ratio `(f / g)` as `Pi.div` of lambdas, which `field_simp`
will not see through. `simp only [Pi.div_apply]` first, then `field_simp`.
Related: `tendsto_rpow_atTop` / `tendsto_rpow_neg_atTop` are top-level
constants (not `Real.`-namespaced), and `tendsto_nhds_unique` against a
constant function needs the `tendsto_const_nhds` witness type-ascribed
(`have h : Tendsto (fun _ : ℝ ↦ c) atTop (nhds c) := tendsto_const_nhds`)
or the elaborator unifies the function the wrong way.

**Identities mixing `t` and `Real.sqrt t`: fold the radical into an atom
first.** `ring`/`field_simp` do not know `(√t)² = t`. The safe pattern:
`set st := Real.sqrt t` (folds every `√t` in the goal into the opaque
local `st`), then `rw [show t = st * st from (Real.mul_self_sqrt ht.le).symm]`
— safe exactly because after the `set`, no goal occurrence of `t` sits
inside a radical. The identity is then rational in `st` and closes with
`field_simp; ring`. Used for the quadratised six-term decomposition
(`Laplace/OneD/JnSecondOrder.lean`).

**Calc chains over multi-term sum integrands push past the default
heartbeat budget.** A calc chain that combines `MeasureTheory.integral_congr_ae`
+ N×`MeasureTheory.integral_add` + N×`MeasureTheory.integral_const_mul`
over a 4-term integrand can exceed the default 200000 heartbeat budget
in `whnf`/`isDefEq`. Symptom: `(deterministic) timeout at whnf` on the
calc step, not on any specific tactic. Workaround:
`set_option maxHeartbeats 1600000 in` on the lemma. Add a comment
explaining why (the linter requires it).

**Smoothness grades and derivatives of differences (NormalizedSingular).**
`ContDiff.differentiable` / `continuous_fderiv_apply` want `∞ ≠ 0` and
`ContDiff.fderiv_right` wants `∞ + 1 ≤ ∞`; `le_top` does NOT prove these
(the top of `WithTop ℕ∞` is `ω`). Use `(by simp)` for the first and
`(contDiff_infty_iff_fderiv.mp h).2` instead of `fderiv_right`. For `C²`
at an analytic point use `hA.contDiffAt` (any grade), not `.of_le`.
`fderiv_sub` is stated for `Pi` subtraction and does not rewrite
`fun w ↦ f w - g w`; use `(hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv`.
Scaled sets `c • S` need `open scoped Pointwise`; `Pi.single` needs
`classical` for `DecidableEq`. `ContDiffBump` continuity is `f.continuous`
(`fun_prop` fails). Grep the library for `SuperPoly.*` before declaring a
helper: `SuperPoly.sub` (CutoffRemoval) and `SuperPoly.congr`
(LocatedCutoff) already exist and a per-file `lean-state check` will not
see the clash at the library root.

**Finite grade from `ContDiff ℝ ∞` has no one-liner (ProjectiveClosure).**
`h.of_le (by simp)` does not discharge `(2 : WithTop ℕ∞) ≤ ∞` on this pin
and `le_top` is wrong (top is `ω`). Where an `AnalyticAt` hypothesis is in
scope use `hA.contDiffAt` (any grade); otherwise take `ContDiffAt ℝ 2 K p`
as a hypothesis and let callers discharge it. Also: never combine
`variable (h : P)` with an explicit `(h : P)` on declarations in the same
section (the name double-binds and later applications feed data into the
proposition slot); and for `rw` with lemmas whose function arguments are
lambdas, elaborate the lemma first with named `(f := fun x ↦ ...)` and
close by `Eq.trans` + `congr 1; funext` rather than rewriting.

**whnf timeout on a whole declaration: bisect with `sorry` (TotalVariation).**
A `(deterministic) timeout at whnf` reported at the theorem's first line,
with every `have` fine in isolation, is located fastest by inserting
`sorry` at successive tactic positions and re-running `lean-state check`
(three runs found one term). The culprit there was
`hcont.integrable_of_hasCompactSupport (hη2s.mul_right)`: `mul_right`
yields `HasCompactSupport (f * g)` in `Pi` form and the unifier unfolds
its way to the lambda. Name the fact first with its lambda type
(`have hsupp : HasCompactSupport fun w ↦ f w * g w := hη2s.mul_right`)
and pass `hsupp`. Also: `∫ w, f w + g w` parses `+ g w` INTO the
integrand — parenthesise `(∫ w, f w) + …`; the pretty-printer shows the
two readings identically.

**`omit [Fintype ι] in` and norms on `ι → ℝ` (LocalUniform).** The Pi
normed-group instances need `Fintype ι`, so `omit` is refused for any
statement mentioning `fderiv`/`‖·‖` on `ι → ℝ`, and even where the
linter says the instance is unused in the *type*, omitting it can make
elaboration hit an `isDefEq` timeout (`hasFDerivAt_expWeight`). Leave the
instance in place and accept the unused-section-variable warning.
`HasFDerivAt.sub` returns a `Pi`-form function: name the derivative fact
with the lambda type in a `have` before `rw [h.fderiv]`. `ring` does not
distribute a symbolic power over a product; `rw [mul_pow]` first.

**`rw [this]` with an equation whose RHS contains its LHS rewrites the
copies inside the RHS too (DerivativeAgreement).** Rewriting
`s * Dh = A - (A - s * Dh)` in a goal that mentions `A - s * Dh` elsewhere
produces nested `A - (A - (A - …))` terms and `linarith` dies. Prove the
triangle step as a separate `have` from `abs_sub` + `sub_sub_cancel`
instead of rewriting. Also: in a rewrite chain that must normalise both a
real-valued norm on the left and `‖s‖` on the right, use
`Real.norm_of_nonneg hs.le` for the specific scalar; the generic
`Real.norm_eq_abs` fires on the first norm it meets.

**Finite grades below `∞`: use `natCast_le_infty` (AllOrders).** The
recurring side conditions `(k : WithTop ℕ∞) ≤ ∞`, `↑k + 1 < ∞`, `2 ≤ ∞`
that `by simp`/`le_top` do not discharge are closed by
`by exact_mod_cast natCast_le_infty k` / `natCast_lt_infty (k + 1)`
(`Laplace/Multi/AllOrders.lean`; proof: `← WithTop.coe_natCast` then
`WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)`). So `h.of_le (by
exact_mod_cast natCast_le_infty 2)` DOES give `C²` from `ContDiff ℝ ∞`.
Also: `∞` is ambiguous (`ℕ∞ω` vs `ℝ≥0∞`) when both `open scoped ENNReal`
and `open scoped ContDiff` are in force — drop the one you do not need.

**A custom inner product on a `Submodule` of a function space needs the
uniformity pinned (StableRecovery).** `let core : InnerProductSpace.Core ℝ V
:= …; let _ : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup
(𝕜 := ℝ)` (the `(𝕜 := ℝ)` is required or the instance problem is stuck) and
`let _ : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore` work
for norms and `LinearMap.exists_antilipschitzWith`, but `CompleteSpace K` /
`IsUniformAddGroup K` for a submodule `K` of `V = ↥(homogPolySpan d k)` fail:
`V` is a subtype of `EuclidD d → ℝ`, which carries the Pi uniformity, and
instance search picks that one. Add `let _ : UniformSpace V :=
PseudoMetricSpace.toUniformSpace` and `let _ : TopologicalSpace V :=
UniformSpace.toTopologicalSpace` right after the normed-group `let`; then
`FiniteDimensional.complete ℝ K`, `HasOrthogonalProjection`, and
`K.isCompl_orthogonal` all resolve. Mark the core `@[instance_reducible]`
(class-type def linter). Also: `rw [hwQ]` with `hwQ : w = …` fails when the
goal contains `⟨w, hw⟩` (motive not type correct) — `change` the goal to a
`w`-only form first; and `pdflatex … > foo.out` CLOBBERS hyperref's
bookmark file `foo.out` — redirect to `.stdout`.

**Measure-theory gotchas from the Abelian-transfer arc (AbelianTransfer*,
EmpiricalTransfer, OneDimSufficient).** `∫⁻ x, ∫⁻ ε in s, H x ε ∂μ` attaches
`∂μ` to the INNER integral — parenthesise `(∫⁻ ε in s, H x ε)`. A.e. equality of
sets `s ∩ t =ᵐ[μ] u` needs `(… : Set ℝ)` ascriptions or the elaborator asks for
`Inter (ℝ → Prop)`. `.const_mul`/`.mul_const` on an `IntegrableOn` yield an
`Integrable` (an `And`), so `.congr_fun` fails: name the result with an explicit
`IntegrableOn` type first. `setIntegral_mono_set` wants the inclusion as
`(h : s ⊆ t).eventuallyLE`; `Eventually.of_forall h` elaborates the set as
`Membership.mem s` and `linarith` then cannot match integrals. For
`Integrable.of_bound` pass `Measurable.aestronglyMeasurable (by fun_prop)`; a
bare `by fun_prop` for `AEStronglyMeasurable` tries continuity (fails on rpow).
`Measure.volume_eq_prod ℝ ℝ` needs explicit type arguments;
`Real.volume_real_Icc_of_le`/`Real.volume_Ioc` are namespaced. `∀ᵐ x, x ≠ 0` is
`rw [ae_iff]; simp`. `Matrix.PosDef` is Finsupp-based on this pin: `hH.2 x hx`
does not typecheck for `x : n → ℝ`; for `1 × 1` use `hH.det_pos` +
`Matrix.det_fin_one`. `Nat.doubleFactorial_zero/one` do not exist — use
`norm_num [Nat.doubleFactorial]`. `Set.mem_setOf_eq` is deprecated for
`Set.mem_ofPred_eq`. `pdflatex … > foo.out` clobbers hyperref's bookmark file.
Multi-line `by` blocks inside parenthesised arguments break parsing — hoist to a
`have`.

**Pi-form products and other friction from the sufficient-family / Stein arc
(CutoffMonomialFamily, GaussianStein, TaylorMonomialExpansion).**
`Continuous.mul`, `HasPolynomialGrowth.mul`, `HasCompactSupport.add` return
`f * g` / `f + g` in Pi form; after feeding them to a lemma the integrand
carries `(f * g) x` redexes that `ring` treats as atoms — `simp only
[Pi.mul_apply]` (or `Pi.add_apply`) first. `HasFDerivAt.mul` on lambdas: name
the result with an explicit lambda type (`have hd : HasFDerivAt (fun y ↦ y i *
F y) _ x := …`) before `rw [hd.fderiv]`, or the rewrite looks for the Pi form.
Coordinate derivatives on `EuclidD d` are `(EuclideanSpace.proj (𝕜 := ℝ)
i).hasFDerivAt`; `EuclideanSpace.single_apply` is deprecated for
`PiLp.single_apply` and `ext j; simp [Finset.sum_apply, Pi.single_apply]`
proves `∑ i, x i • single i 1 = x`. Composing a `HasFDerivAt` with a real
`HasDerivAt` (`comp_hasDerivAt`) lands in the `RCLike`-derived `Module ℝ ℝ`
instance; `convert this using 1 <;> rfl` closes the instance diamond where
`simpa`/`exact` fail. `gcongr` cannot discharge side goals like `0 ≤ χ w`
from hypotheses — spell out `mul_le_mul`. `omit [..] in` must come BEFORE the
docstring. `le_or_lt` is now `le_or_gt`. The multivariate Taylor remainder is
cheapest through `taylor_mean_remainder_bound` on `g s = φ (p + s • v)` with
`ℓ.iteratedFDeriv_comp_right` + `iteratedFDeriv_comp_add_left` identifying the
iterated derivatives along the line.

**Second-order Laplace arc (SecondOrderEngine, SecondOrderLaplace,
SecondOrderRadial).** `abs_exp_neg_sub_one_add_le` already exists in
`CovarianceSharp` with the `exp|r|` weight; the Gaussian-friendly endpoint bound
`|e^{-v} − 1 + v| ≤ v²(1 + e^{-v})` is `abs_exp_neg_sub_one_add_le_endpoint` —
the root module fails to import on a duplicate name even when `lean-state
check` of the file is clean, so grep for the name before adding a lemma.
`rw [taylorTail_smul_succ]` without arguments rewrites the FIRST matching
Taylor tail (often the one on the other side of the equation) — pass the
degree explicitly. `rw [← pow_add, add_comm]` reorders whichever sum it sees
first; use `show (2 : ℕ) + ρ = ρ + 2 by ring`. `add_le_add_left h a : a + b ≤
a + c`? In this Mathlib the argument order made `add_le_add le_rfl h` the safe
choice. `Σ` (U+03A3) is a reserved token — `hΣ0` does not parse as an
identifier. `Finset.sum_eq_add_of_mem 0 2 h0 h2 (by norm_num) hrest` collapses a
sum whose other terms vanish (the `hrest` binder is `∀ c ∈ s, c ≠ a ∧ c ≠ b →
f c = 0`). `iteratedFDeriv_const_of_ne hn c : iteratedFDeriv 𝕜 n (fun _ ↦ c) =
0` is a FUNCTION equality, so after rewriting an applied term you get `0 0` —
follow with `Pi.zero_apply`. `ContinuousMultilinearMap.zero_apply/smul_apply`
are deprecated for the root `zero_apply/smul_apply`. `∞` in `ContDiff ℝ ∞ f`
needs `open scoped ContDiff` (otherwise "type expected, got (ContDiff ℝ : …)").
Higher-order unification cannot infer `a : ℕ → ℝ` from `a (ρ + j)`; pass the
coefficient sequences explicitly `(a := fun m ↦ …)` and let beta reduction
match `m + 2` against `ρ + j + 2`. Directional-derivative growth of a smooth
homogeneous `Q` (needed for the Stein identities) comes from
`iteratedFDeriv_smul_eq_of_isHomogeneous` at `j = 1` plus
`exists_abs_le_of_isHomogeneous`
(`hasPolynomialGrowth_fderiv_of_isHomogeneous`). Analyticity of `qform` is
`(innerSL ℝ).analyticAt_bilinear … |>.comp₂ analyticAt_id (A.analyticAt x)` then
`convert … using 2 with y; simp [qform]`.

**Weighted-jet arc (WeightedDegree, KernelComparison,
WeightedPolynomialComparison, WeightedTemperatureAdapter).** Coefficient
uniqueness for `∑ α ∈ S, c α * mvMonomial α u = 0` goes through
`MvPolynomial.funext` with `p := ∑ α ∈ S, monomial (Finsupp.equivFunOnFinite.symm α) (c α)`;
`MvPolynomial.eval_monomial` + `Finsupp.prod_pow` evaluate to `mvMonomial` by `rfl`
(`coe_equivFunOnFinite_symm` is rfl), and `coeff_sum` + `coeff_monomial` +
`Finset.sum_eq_single` extract a coefficient (the `if` compares Finsupps, use
`Finsupp.equivFunOnFinite.symm.injective`). `isLittleO_one_iff.mp` is an "unknown
constant" — `rwa [isLittleO_one_iff] at h` works. Binders from `filter_upwards
[self_mem_nhdsWithin] with ε hε` have type `ε ∈ Set.Ioi 0`; `pow_pos hε` needs
`Set.mem_Ioi.mp hε` (or `have : 0 < ε := hε`). A section `variable [Fintype ι]` is
included in every declaration and lints as unused — put `[Fintype ι]` on the
individual declarations that sum over `ι` (or `omit [Fintype ι] in`). Dot notation
`W.foo` only works if `W` genuinely occurs in `foo`'s signature; a def in
`namespace IntWeights` that does not mention `W` is `IntWeights.foo`, not `W.foo`.
`rw [show W.wdeg α = (W.wdeg α - D) + D from …]` rewrites every occurrence
including the one inside the target `W.wdeg α - D` — state the power identity
`ε ^ W.wdeg α = ε ^ (W.wdeg α - D) * ε ^ D` as a `have` and rewrite with that.
`Tendsto.div`/`.mul`/`.sub` on function-valued limits produce Pi-form
`(f / g) h` redexes: `simp only [Pi.div_apply]` before `field_simp`. For the
normalized-quotient algebra, keep the kernel-level theorem
(`tendsto_normalizedKernel_difference_div_pow`) free of exponentials and prove the
exponential/masked versions as wrappers.
More from the same arc: `Fintype.piFinset` needs `DecidableEq ι` — a def using it
under `open Classical in` must be `noncomputable`. A def taking the section
variable `(W : IntWeights ι)` explicitly cannot be used with dot notation on a
structure that mentions `W` in its type (`J.rem N x` puts `J` in the first
`WeightedJet` slot and shifts everything else): declare such helpers with
`omit W in noncomputable def WeightedJet.rem {W : IntWeights ι} …`. `rw` cannot
rewrite `ε ^ 1` under `fun ε ↦ …` inside a `Tendsto` (bound variable) — state the
continuous majorant without the exponent and rewrite the pointwise bound instead.
`|a| / c` is not `|a| / |c|`: to get `|a/c − b/c| ≤ |a|/c + |b|/c` use
`rw [← sub_div, abs_div, abs_of_pos hc, ← add_div]` then `abs_sub`. In this
Mathlib `add_le_add_left h c : h.lhs + c ≤ h.rhs + c` (adds on the RIGHT); use
`add_le_add le_rfl h` / `add_le_add h le_rfl` to avoid guessing. Flat analytic ⇒
zero germ: mirror `HasFPowerSeriesAt.apply_eq_zero` (strong induction, partial
sum `k+1` collapses to `p k` on the diagonal, `isBigO_sub_partialSum_pow (k+1)`,
`IsBigO.continuousMultilinearMap_apply_eq_zero`), then `hasFPowerSeries_diag_eq`
+ `ContinuousMultilinearMap.eq_of_diag_eq` with symmetry from
`(h.analyticAt.contDiffAt (n := ω)).iteratedFDeriv_comp_perm` (needs
`open scoped ContDiff` for `ω`).
Follow-up arc (WeightedTaylor, WeightedCoercivity, WeightedReconstruction): the
matrix-vector notation `*ᵥ` is scoped — `open Matrix` or it fails with
"elaboration function for subscriptTerm has not been implemented". `set S := …`
cannot abstract an expression that occurs inside a dependent binder type
(`v : S.filter … → ℝ`); pass the finset as a parameter with an equation
`(hSk : Sk = S.filter …)` and `rw [hSk] at h` for membership (`hSk ▸ h` picks the
wrong motive). `rw [div_eq_inv_mul] at h` rewrites the FIRST division, which may be a
real exponent `D / a i`; rewrite the goal side with `← div_eq_inv_mul` instead. The
`unusedFintypeInType` lint on a theorem whose type has no `Fintype` but whose proof
sums over `univ`: state it with `[Finite ι]` and open with `have := Fintype.ofFinite ι`.
Regrouping a word expansion by exponent: `Finset.prod_comp` gives
`∏ j, x (m j) = ∏ i ∈ univ.image m, x i ^ #{j | m j = i}` (extend to `univ` with
`Finset.prod_subset`), `Finset.card_eq_sum_card_fiberwise` gives the total degree, and
`Finset.sum_fiberwise_of_maps_to (g := wordExp)` collapses the sum over words into a
sum over exponents; a `subst` on `totalDeg α = n` transports `Fin n → ι` sums.
`HasFPowerSeriesOnBall.uniform_geometric_approx' hf (h : ↑r' < r)` is the one-ball
uniform Taylor remainder; `HasFPowerSeriesOnBall.hasFPowerSeriesAt` needs no positivity
argument (the structure carries `r_pos`). `zero_le` has an implicit argument here:
write `lt_of_le_of_lt zero_le h`, not `zero_le _`.
Cutoff arc (WeightedCutoff): `norm_integral_le_of_norm_le hg (f := …) (h)` needs the
explicit `f` or the `NormedSpace` instance search sticks; `Set.indicator_le_self` needs a
canonically ordered codomain — over `ℝ` use `Set.indicator_le_self' (fun _ _ ↦ nonneg)`;
after `refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)` the goal is a beta-redex
`(fun u ↦ …) u` — `beta_reduce` before `rw [Set.indicator_of_mem]`; `W.integral_dil hε (f := …)`
should name `f` or the lambda is inferred from the measurability proof in `∘` form and the
`rw` fails; `t⁻¹ ≤ t^(-(1/D))` for `t ≥ 1` is `Real.rpow_le_rpow_of_exponent_le` after
`← Real.rpow_neg_one`; `Set.indicator_le_indicator_of_subset hUU' (fun _ ↦ nonneg) x` is the
pointwise monotonicity of indicators in the set.

**Research-item arc (TruncatedBlindness, CylinderSufficient, SeparableTangential,
RotationCounterexample).** Fubini along a coordinate splitting `ι₁ ⊕ ι₂`:
`volume_measurePreserving_sumPiEquivProdPi (fun _ ↦ ℝ)` + `.integral_comp'` + `integral_prod_mul`;
state the chain as a `calc` whose first step is `rfl` (the equiv's components are definitionally
`w ∘ Sum.inl` / `w ∘ Sum.inr`) — a `rw [← integral_prod_mul, ← h]` does not find the pattern because the
product integral carries `∂volume.prod volume`. Linear changes of variables on `Fin 2 → ℝ`:
`Real.map_linearMap_volume_pi_eq_smul_volume_pi (hf : LinearMap.det f ≠ 0)` gives
`map f volume = ofReal |det⁻¹| • volume`; package an involution as a `MeasurableEquiv` literal
(`toFun := S, invFun := S, …`) and use `MeasurePreserving.integral_comp'`. `LinearMap.det_toLin'` +
`Matrix.det_fin_two_of` evaluate `det (toLin' !![a,b;c,d])`; `rw [Matrix.toLin'_apply]; ext i; fin_cases i <;>
simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]` computes the vector, and component lemmas `rot y 0 = …`
close by `rw [rot_apply]; rfl`. After `fin_cases i` the index is `⟨1, _⟩`, not `1`: `linarith`/`rw` on
lemmas stated with `0`/`1` fail syntactically while `exact` (defeq) succeeds — prove the per-index facts as
separate lemmas with literal indices and finish by `fin_cases i <;> exact …`. Real-arithmetic defs (`/ 2`)
must be `noncomputable`. `√2` algebra: rewrite with `Real.mul_self_sqrt`/`Real.sq_sqrt` after
`div_mul_div_comm`/`div_pow` rather than `field_simp; linear_combination` (whose coefficient depends on
field_simp's normal form). `AnalyticAt.div_const` takes the constant implicitly (`(c := 2)`); `AnalyticAt` of a
coordinate is `(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).analyticAt 0` (both implicits needed).
Lemmas with implicit observables (`tempMoment_add {φ ψ}`) applied via `rw` need `(φ := fun y ↦ …) (ψ := …)`
named, or continuity proofs built by `Continuous.const_smul` instantiate `φ` in Pi-`•` form and the rewrite
fails. `LipschitzOnWith.dist_le_mul h x hx y hy` takes the points explicitly. `integrable_const` needs a finite
measure — for an indicator of a ball use `(integrable_indicator_iff hmeas).mpr (integrableOn_const
measure_ball_lt_top.ne)`. `Measure.addHaar_ball_of_pos volume q hρ` + `Module.finrank_fintype_fun_eq_card` +
`measureReal_def`/`ENNReal.toReal_mul`/`toReal_ofReal` turn `volume.real (ball q ρ)` into
`ρ ^ card ι * (volume (ball 0 1)).toReal`; positivity of the latter is `ENNReal.toReal_pos
(Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne`. Quadratic bound at a minimum of a
`C²` function: `hV.contDiffAt.fderiv_right (m := 1) (by norm_num)` then `ContDiffAt.exists_lipschitzOnWith`,
`IsLocalMin.fderiv_eq_zero`, and `(convex_closedBall q ‖y − q‖).norm_image_sub_le_of_norm_fderiv_le` — the
fderiv version with `DifferentiableAt` hypotheses elaborates instantly (the HasFDerivWithinAt gotcha above
is about mixing the two).

**Smoothness of a parametric integral: use the convolution theorem (MarginalCutoff).** Mathlib has no
general "differentiate under the integral to all orders" lemma, but
`contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := volume) (f := fun _ ↦ (1 : ℝ)) (n := ⊤)
(ContinuousLinearMap.mul ℝ ℝ) isOpen_univ hk hgs (locallyIntegrable_const 1) hg` gives
`ContDiffOn ℝ ∞ (fun q ↦ (1 ⋆ g q.1) q.2) (univ ×ˢ univ)` for a family `g : P → G → ℝ` smooth in `(q, y)` with
`g q y = 0` for `y ∉ k` (`k` compact, independent of `q`), and `(1 ⋆ g q) 0 = ∫ y, g q (−y) = ∫ y, g q y`
(`convolution_def`, `ContinuousLinearMap.mul_apply'`, `integral_neg_eq_self`) — so `q ↦ ∫ g q y dy` is smooth.
Needs `open scoped Convolution`; `n : ℕ∞` there, `(⊤ : ℕ∞)` coerces to `∞`. Joint smoothness of
`(q, y) ↦ χ (Sum.elim q y)`: `↿g = χ ∘ ⇑(LinearMap.toContinuousLinearMap
(LinearEquiv.sumArrowLequivProdArrow ι₁ ι₂ ℝ ℝ).symm.toLinearMap)` by `funext; rfl`, then
`hχ.comp (ContinuousLinearMap.contDiff _)`. Fubini for a non-product integrand along the coordinate
splitting: `volume_measurePreserving_sumPiEquivProdPi_symm` + `.integral_comp'`, integrability transported by
`(hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr`, then
`rw [Measure.volume_eq_prod (ι₁ → ℝ) (ι₂ → ℝ), integral_prod _ hint']` (explicit type arguments so only the
product-space `volume` is rewritten); `(sumPiEquivProdPi _).symm (x, y) = Sum.elim x y` is `rfl`, so a `change`
to the glued form works. `dist_pi_lt_iff hr` splits a sup-norm ball on `ι₁ ⊕ ι₂ → ℝ` into transverse and
tangential balls (`cases i with | inl | inr`).

**Empirical / visibility arc (EmpiricalRelative, HarmonicWitness, MonomialVisibility).** A theorem
named `Foo.fderiv` shadows the root `fderiv` inside its own proof (every `fderiv ℝ` then elaborates
as the theorem, "argument ℝ … expected LowPoly") — name derivative lemmas `deriv_dir` or similar. Inside
`induction h with | coord_mul i hF ih` the constructor's implicit function is inaccessible; write
`| @coord_mul q i F hF ih` to name it, and never use `_` for it in `have` statements. `∀ᶠ n in atTop, P`
with `n` unused in `P` leaves `n`'s type a metavariable ("typeclass instance problem is stuck
Preorder ?m") — derive the fact from `(h.and h').exists` instead. `abbrev K x := quadKernel 1 x` is NOT
seen through by `rw` with lemmas stated for `quadKernel 1 x`; use `local notation "K₁" =>
quadKernel (1 : Matrix (Fin d) (Fin d) ℝ)` (section variables are fine inside a local notation).
`stdKernel` already exists in `StdGaussian` — grep before naming. `Matrix.PosDef.one` (not
`posDef_one`) is the identity's positivity; `simp` proves `toEuclideanCLM 1 = 1` and
`EuclideanSpace.inner_single_right/left` evaluate `⟪x, single i 1⟫`. `HasFDerivAt.pow` gives the
derivative of `z ↦ (ℓ z)^k` for a CLM `ℓ` into `ℂ` as `(k • ℓ z ^ (k-1)) • ℓ`; take re/im parts with
`Complex.reCLM.hasFDerivAt.comp`, and rewrite the function by `funext; simp [harmRe]` before `.fderiv`.
`HasFDerivAt.mul` / `.add` / `.const_mul` produce Pi-form functions — state the `HasFDerivAt` with the
lambda type in a `have` before `rw [h.fderiv, add_apply, smul_apply, smul_eq_mul]`; `(EuclideanSpace.proj i) v = v i`
is `rfl` (there is no `EuclideanSpace.proj_apply`). `Continuous.mul` inferring `f` for
`integrable_mul_quadKernel_of_polynomialGrowth` yields `(F * G) a` Pi redexes that `rw [integral_add …]`
cannot match — state the `Integrable` facts with explicit lambda types. `abs_of_nonneg (by positivity)`
inside `rw` rewrites the FIRST `|·|` it sees when positivity's goal is a metavariable — give the explicit
nonnegativity proof. `Real.exp_le_exp.mpr`, `abs_le`, and `nlinarith` handle `e^{-tδ} ≤ e^{-t(K−L)} ≤ e^{tδ}`.
`positivity` cannot use `∀ n, 0 ≤ δ n`; instantiate `have := hδ n` first.

**Tilt / trace arc (TiltInterpolation, TiltCauchySchwarz, TraceVisibility, EmpiricalRescaled).**
Differentiation under the integral: `hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun u x ↦ …)
(F' := …) hs hmeasF hint hmeasF' hbound hbound_int hdiff` with `hs : Metric.ball u₀ 1 ∈ 𝓝 u₀`
(`Metric.ball_mem_nhds`), the bound stated as `∀ᵐ x, ∀ u ∈ ball u₀ 1, ‖F' u x‖ ≤ bound x`
(`|u| ≤ |u₀| + 1` from `Metric.mem_ball` + `Real.dist_eq` + `abs_add_le`), and the pointwise
derivative from `((hasDerivAt_id u).const_mul c)` simplified BEFORE `.neg`/`.exp` (applying `.neg`
first produces a `-fun y ↦ …` that `simpa` cannot match). Name `F`/`F'` explicitly or the
higher-order unification fails. Quotient rule: `hN.div hZ hZ0` gives a Pi-form function and the raw
`(c' d − c d')/d²` derivative; finish with `hdiv.congr_deriv hval` where `hval` is proved by
`field_simp; ring` after `unfold` — `convert … using 1; field_simp` leaves the function-equality goal
untouched ("field_simp made no progress"). Mean value on `[0,1]`:
`norm_image_sub_le_of_norm_deriv_le_segment' (f := …) (f' := …) (a := 0) (b := 1) (C := …) hderivWithin
hbound 1 (Set.right_mem_Icc.mpr zero_le_one)` then `simpa`. `abs_add` is now `abs_add_le`; the
inequalities `−|a| ≤ a`, `a ≤ |a|`, `−a ≤ |a|` are `neg_abs_le`, `le_abs_self`, `neg_le_abs`.
Cauchy–Schwarz for a covariance without L²: expand `Var(f − λ g) ≥ 0`, feed `discrim_le_zero` (needs the
quadratic written as `a * (l * l) + b * l + c`), `rw [discrim]`, `nlinarith`, then `Real.abs_le_sqrt`
and `Real.sqrt_mul`. `Integrable.bdd_mul (hg : Integrable g) (hf_meas) (bound : ∀ᵐ x, ‖f x‖ ≤ c)`
gives `Integrable (fun x ↦ f x * g x)` — the bounded factor must come FIRST in the product. A
structure of Props (`TiltData`) is a good carrier for standing hypotheses; put `[Nonempty X]` on the
lemmas that extract `0 ≤ M` from a bound `∀ x, |R x| ≤ M`. Trace arc: theorem names must not end in
a definition's name used inside (`SmoothHomog.pd` shadowed `pd`); prove homogeneity of `fderiv` in
degree 1 by continuity in the dilation parameter (`tendsto_nhds_unique` along `𝓝[≠] 0`); the basis
expansion `∑ i, x i • single i 1 = x` is `(EuclideanSpace.basisFun _ ℝ).sum_repr x` with
`basisFun_apply`/`basisFun_repr` simp; `integral_finset_sum` is now `integral_finsetSum`; `rw [hc]` with
`hc : f = fun _ ↦ f 0` is fine but `simp [hc]` loops. EmpiricalRescaled: `LocalLaplaceDomain.weight`
and `integrable_integrand` already existed (SecondOrderLaplace, LocationRecovery) — a chained
`; git commit` after a failed root build pushed a broken import; gate commits on the build exit
code explicitly. `tendsto_pairwise_normalized_moment_difference` lives in namespace
`HigherLaplaceDomain`.

## Architecture: the generic-(k₁,k₂) 2D lift pattern

The `Laplace/TwoD/KthKth*.lean` trio (Partition, Numerator, Moment)
asymptotics are all instances of a single mirror-shape pattern that
lifts a 1D closed-form result against `kthPotential k` to a 2D
asymptotic on the separable potential `addSeparable (kthPotential k₁) (kthPotential k₂)`.

The pattern has four packaged theorems per lift:

1. **Factorisation step.** Use the 2D-separable machinery in
   `Laplace/TwoD/AddSeparable.lean` to express the 2D quantity as a
   product of two 1D ones:
   - For the unnormalised numerator: `integral_separable_addSeparable`
     (just needs `Integrable (fun x => f x * exp(-(t * U x)))` on each
     factor, which is `Laplace.OneD.kth_integrable_pow_pot` for the
     `x^(2j) · exp(-...)` family).
   - For the Gibbs partition function: `partitionFunction_addSeparable_factor`
     (just needs `Integrable (fun x => exp(-(t * U x)))`, which is the
     `n = 0` specialisation of `kth_integrable_pow_pot`).
   - For the Gibbs expectation of a separable observable:
     `gibbsExpectation_separable_addSeparable` (needs both `Z` nonzero
     and the four integrabilities).

2. **`const × t^(-...)` step.** Substitute the 1D closed forms
   (`kth_moment_even` for the numerator; `partitionFunction_kthPotential`
   for the partition; `gibbsExpectation_kthPotential_even` for the
   Gibbs moment), then peel off the `t`-dependence via
   `Real.div_rpow` + `Real.rpow_add` + `Real.rpow_neg` and finish with
   `ring`.

3. **Rescaled `Tendsto`.** Multiply by the inverse power; the result
   is `eventually equal to a constant function`, so
   `tendsto_const_nhds.congr'` finishes after `Real.rpow_add` +
   `add_neg_cancel` + `Real.rpow_zero`.

4. **`IsEquivalent` packaging.** `Asymptotics.IsEquivalent.refl.congr_left`
   plus `filter_upwards` over `Filter.eventually_gt_atTop (0 : ℝ)`
   plus the exact reformulation of step 2.

Each tide following this pattern lands in ~120-155 lines.

### When to instantiate the pattern

A new `Laplace/TwoD/<SomeKthKth>.lean` file is justified when:

- A new 1D base lemma exists in `Laplace/OneD/`.
- The 2D-separable machinery already covers the observable shape
  (one of: pure exp, `f(x) · g(y) · exp`, `f(x) · exp`).
- The asymptotic form is wanted in addition to the closed form.

The first instance was `QuarticSexticPartitionAsymptotic` /
`QuarticSexticMomentAsymptotic` / `QuarticSexticNumeratorAsymptotic`
at the fixed `(k₁, k₂) = (2, 3)`; the generic-`(k₁, k₂)` trio
(`KthKthPartitionAsymptotic`, `KthKthMomentAsymptotic`,
`KthKthNumeratorAsymptotic`) lifted those on 2026-05-21.

**`open scoped Nat` steals `φ` (and `!`).** The `Nat` scope defines `φ` as
notation for `Nat.totient`, so after `open scoped Nat` a binder like
`{f φ : ℝ → ℝ}` fails to parse (`unexpected token 'φ'; expected '}'`).
Identifiers *containing* φ (`hφ_c`, `Mφ`) are fine — only the bare name
breaks. If a file needs both a `φ` variable and double factorials, skip the
scoped open and write `Nat.doubleFactorial (…)` explicitly; the closed-form
lemmas stated with `‼` still apply, since `‼` is notation for the same
constant.

**New-file header: include `Authors:` or the header linter warns.** The Mathlib
`linter.style.header` emits `Copyright too short!` on fresh elaboration when the copyright
block lacks an `Authors:` line. Most existing seabed files predate the linter and carry the
warning latently (cached, so it only surfaces when the file is rebuilt). For a warning-clean
build, give new files the full Mathlib header form:
```
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
```

**A `lake build` proves nothing about a file outside the import
closure.** The build gate is vacuous for a new file until
`Laplace.lean` imports it: `lake build` and CI both pass while the
file has arbitrarily many errors (this shipped an uncompiled file in
PR #55). After creating a file, verify BOTH the import line in
`Laplace.lean` AND the presence of the new `.olean` under
`.lake/build/lib/lean/` before reporting a build result. Job-count
deltas are too noisy to serve as the check.

**Additions to a widely-imported file rebuild ALL dependents, surfacing their
pre-existing lint.** Appending a theorem to a core file (e.g. `TwoD/AddSeparable.lean`)
forces every downstream file to re-elaborate, and any of them lacking an `Authors:` header
then emits `Copyright too short!` — a cascade of warnings unrelated to your change (and not
worth fixing across dozens of files). Prefer a NEW LEAF file that imports the core one for
additive results; the core file stays untouched, nothing downstream rebuilds, and the tide's
build is warning-clean. (Also why `scripts/sorries`/full-build warning counts spike when you
touch a hub file — it is latent debt, not your diff.)

**`CFC.sqrt` on matrices needs `open scoped MatrixOrder` in every
file.** The matrix `PartialOrder` instance is scoped; without the
open, every `CFC.sqrt`/`PosSemidef.nonneg` use site errors with a
baffling `failed to synthesize PartialOrder (Matrix ...)` (no
missing-import hint). Same for `CFC.sqrt_mul_sqrt_self H
(ha := hH.posSemidef.nonneg)` — the nonneg argument is an autoParam,
pass it named.

**Class-level `map_star` fails on `Matrix.toEuclideanCLM`.** Instance
synthesis cannot find `StarHomClass` for the star-algebra-equivalence
type `Matrix n n ℝ ≃⋆ₐ[ℝ] (EuclideanSpace ℝ n →L[ℝ] ...)`. Use the
structure field directly: `(Matrix.toEuclideanCLM (𝕜 := ℝ)).map_star'
A : toEuclideanCLM (star A) = star (toEuclideanCLM A)` — accepted as
a term (defeq through the raw `toFun`), though `rw` with it can
stumble; bind it in a `have` with the coerced statement first.

**`rfl` bridging `(CLM S * CLM S) x` to a def-wrapped composition
times out at whnf.** Deterministic heartbeat timeout, not an error in
the maths. Fold the composition into an equation (`have hcomp :
toEuclideanCLM H = whitening H * whitening H`), then rewrite with
`ContinuousLinearMap.mul_apply`; never ask `rfl` to unfold CLM
multiplication applied to a point.

**`PiLp.continuous_apply` takes `p` and `β` explicitly.** A bare
coordinate index as first argument silently coerces into the `p` slot
(`Fin d → ℝ≥0∞`!) and produces `Invalid field 'mul': ...
Function.mul` at the use site. Call as `PiLp.continuous_apply 2
(fun _ : Fin d ↦ ℝ) a`.

**`integral_fintype_prod_volume_eq_prod` needs NO integrability.**
Mathlib's finite-product Fubini for `∏ i, f i (x i)` on pi types is
unconditional; combined with `PiLp.volume_preserving_toLp` +
`MeasurePreserving.integral_comp` (the FourierTransform.lean idiom)
this makes coordinate-moment computations on `EuclideanSpace`
essentially free. The one-hot factor trick: integrate
`fun i t ↦ if i = a then t else 1` and collapse the product with
`Finset.prod_ite_eq'`.

**Passing `HasFDerivWithinAt` hypotheses to
`Convex.norm_image_sub_le_of_norm_fderiv_le` is a unification bomb.**
That lemma wants `∀ x ∈ s, DifferentiableAt 𝕜 f x` and a bound on
`fderiv 𝕜 f x`; feeding it explicit-derivative hypotheses makes the
elaborator attempt a whnf-unfolding unification that survives even
8M heartbeats (minutes of wall clock, then death). The
explicit-derivative variant is
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` (dot-notation
on the `Convex` fact) — with it the same application elaborates
instantly. Symptom to recognize: `(deterministic) timeout at whnf`
pointing at the theorem's `:=` line while every `have` checks fine.

**`ω` (analytic grade) is scoped notation.** Without `open scoped
ContDiff`, a bare `ω` in a theorem statement silently auto-binds as a
free implicit variable; the symptom is an "expected `ContDiffAt ℝ ⊤`,
got `ContDiffAt ℝ ω`" mismatch at use sites (Mathlib displays the
analytic grade as ⊤ of `WithTop ℕ∞`). Higher-order symmetry of
iterated derivatives (`ContDiffAt.iteratedFDeriv_comp_perm`) exists
ONLY at ω regularity; for C^k, Mathlib has just order-2
(`second_derivative_symmetric`). Polarization and any
tensor-symmetry consumer should take an abstract `IsSymm` hypothesis
and let callers discharge it (J3 pattern).

**`field_simp`/`linarith` on equations between integrals: fold the
integral values into scalar atoms first.** field_simp rewrites under
integral binders, reassociating mul/div inside the integrand and
silently desynchronizing what linarith needs to see as one atom
(symptom: linarith failure where the hypothesis and goal print
almost-identical integrals differing in integrand association).
Fix: `set B := ∫ x, ... with hB` for each integral value (scalars
are safe to fold — no lambda under them), then the equation is pure
scalar algebra. Also: squeeze arguments against a previously proven
Tendsto must reuse its RAW statement — a `simpa using h.norm`
renormalizes `-c * ‖x‖^2` to `-(c * ‖x‖^2)` inside binders and the
squeeze's syntactic matching dies.

**`grep` may be shadowed (rg-style) in the user shell: `-c` with zero
matches prints NOTHING instead of `0`.** The retrospective compile
gate `N=$(grep -cE '^!|Error|Overfull' file.log)` then sets `N` empty
— `exit $N` succeeds vacuously and real errors (e.g. Unicode
characters in `\code{}` spans) pass the gate silently. Always use
`/usr/bin/grep` in gate expressions, and treat an empty `[$N]` echo as
a broken gate, not a pass.

**`integral_congr_ae` (and `Integrable.congr`) hand pointwise goals as
applied lambdas.** Every `rw` inside then dies on the beta redex
(`(fun w ↦ ...) x = ...`). Run `beta_reduce` (or a goal-changing
`change` — the style linter rejects `show` for this) before any
rewrite in such blocks. Same for the per-point goals of
`setIntegral_congr_fun`.

**`positivity` cannot see nonnegativity/positivity of opaque
structure fields or `choose`-extracted constants.** `D.lambda / 4 > 0`
or `0 ≤ D.remConst` fail even when provable: derive a local fact once
(`by linarith [D.lambda_pos]`, or an explicit `mul_nonneg` chain) and
thread it.

**Argument-orientation renames on this pin.** `add_le_add_right h c`
produces `c + a ≤ c + b` (adds on the LEFT) — use
`add_le_add h le_rfl` for the right-hand form. `div_eq_iff` wants the
division on the LEFT of the equation (`eq_div_iff` for the right).
`MeasureTheory.integral_div` rewrites `∫ f x / c` forward; the `←`
pattern `(∫ f)/c` is often not present. `Finset.sum_div` pushes a sum
through division numerator-first; convert per-term with
`mul_div_assoc` afterwards. `tsum_le_tsum` is now dot-notation
`Summable.tsum_le_tsum` on the LHS summability. `Real.sqrt_le_one` is
an iff. `IsLittleO.neg` is `IsLittleO.neg_left`. `push_neg` is
deprecated for `push Not`.

**`set ... with` must run AFTER obtaining the hypotheses it should
fold.** Instances pulled from an `∀ᶠ`-fact after the `set` contain
fresh unfolded copies, and `linarith`/`field_simp` then see two
different atoms. Order: `filter_upwards`/`have` the instances first,
then `set` (which folds every existing occurrence).

**`rw [Real.exp_add]` with identical instantiations rewrites all
copies at once.** A three-factor exponential split needs two
`exp_add` rewrites, not three; the third fails with
"did not find an occurrence".

**λ cannot appear inside an identifier** (`hλ` fails to parse — it is
the anonymous-function token). Use `hlam`.

**`rw [show (0:ℝ) = ∫ 0 ...]` rewrites the zero inside the filter
`𝓝[>] (0:ℝ)` too.** State the DCT conclusion with `∫ 0` and transfer
by `simpa`, never rewrite the goal's zero.

**`Real.rpow_neg_one` does not exist.** Only the NNReal/ENNReal
versions do. For a real base write
`show t⁻¹ = t ^ (-1 : ℝ) from by rw [Real.rpow_neg ht.le, Real.rpow_one]`
and then `← Real.rpow_mul` for `(t⁻¹)^r = t^(-r)` manipulations.

**`have`-bound constructors are opaque: consume postconditions
through structure fields.** `have A := someConstructor ...` erases
the definition, so a later `(A k).field = <constructed value> := rfl`
cannot reduce (symptom: "application type mismatch ... ?m = ?m"
against the projection). Even with the application inlined, internal
`Exists.choose` terms are Classical-opaque and cannot be re-derived
by spelling them identically. The pattern: have the constructor set
RELATED fields from the same local (e.g. `U := ball 0 ρ` and
`delta := ρ`), then callers get `U = ball 0 delta` by `rfl` and
positivity from `delta_pos` — postconditions read off fields, never
reconstructed from choice chains.

**A sibling theorem missing from the import closure presents as an
unknown identifier.** With forty-plus files in one namespace,
`Laplace.Multi.Foo.bar` failing to resolve usually means the FILE is
not imported, not that the name is wrong. Check the import chain
before renaming anything.

**`have h := f a b ?_` + `case _ =>` does not defer the trailing
explicit argument.** The elaborator inserts the metavariable eagerly
and the `case` block finds no goal (symptom: `introN` failure then
"unknown identifier h"). Pass the argument as an inline lambda (with
a `by` block if tactics are needed), or restate it as a separate
`have` with an explicit type.

### Name clashes across modules surface only at `Laplace.lean`

Two modules in the same namespace may each compile, yet `lake build` of the
umbrella `Laplace.lean` fails with `import X failed, environment already
contains 'Laplace.Multi.foo._proof_1' from Y`. `lean-state check` on the new
module cannot see this (it does not import the sibling). Before naming a new
def in `Laplace.Multi`/`Laplace.Sampler`, `grep -rn "def foo\b" Laplace/`;
e.g. `whitening` already lives in `QuadForm.lean` (a `Fin d` CLM `√H`), so the
matrix version is `whiteningOf`.
## Gotchas from the Morse–Bott / cyclic-blindness arc (2026-09-21)

- `open Complex` brings the NOTATION `cexp` for `Complex.exp`: a def named `cexp` silently becomes
  `Complex.exp` applied to your arguments ("Function expected at cexp ↑N"). Pick another name.
- `conj` needs `open ComplexConjugate`; otherwise "Unknown identifier conj" and downstream terms
  elaborate with `sorry` types (e.g. `w : ℕ` for a complex root).
- `PiLp.continuous_ofLp` takes explicit `p` and `β`: `PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ)`.
- `⬝ᵥ` / `*ᵥ` are scoped: `open scoped Matrix` (error: "elaboration function for subscriptTerm").
- `volume` on a product type is `Measure.volume_eq_prod` (namespace `MeasureTheory.Measure`), then
  `integral_prod_symm f hf : ∫ z, f z = ∫ y, ∫ x, f (x, y)` (integrability of the JOINT function).
- `continuous_of_dominated` (root namespace, MeasureTheory) for parametric integrals; bound must be
  independent of the parameter, hence assume uniform ellipticity globally rather than derive it.
- `Continuous.ae_eq_iff_eq` takes the measure EXPLICITLY: `(hf.ae_eq_iff_eq volume hg).mp`.
- After `set A := ∫ … with hA`, hypotheses introduced LATER still contain the integral, not `A`;
  `rw [hA]` (forward) unfolds `A` in the goal to match them.
- `rw [← integral_const_mul]` picks the FIRST `c * ∫` it sees (possibly the wrong side); do
  `rw [mul_assoc]; congr 1` first to isolate the factor you mean.
- Rotation invariance of Lebesgue measure on `ℂ`: `Measure.map_linearMap_addHaar_eq_smul_addHaar`
  with `f := ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ)` and `det_rotation`; then
  `MeasurePreserving.integral_comp _ (rotation a).toHomeomorph.measurableEmbedding` (no integrability
  needed), `Circle.coe_exp` to unfold `rotation (Circle.exp θ)`.
- `Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (hN : N ≠ 0) : exp (2πI k / N) = 1 ↔ N ∣ k`.
- `IsAlgClosed.exists_pow_nat_eq (x : ℂ) (hn : 0 < n) : ∃ z, z ^ n = x` for N-th roots.
- Stone–Weierstrass: `ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints`
  with `A := Algebra.adjoin ℝ (Set.range coords)` in `C(K, ℝ)`, `K = tsupport f` (`CompactSpace K`
  from `isCompact_iff_compactSpace`); `Algebra.adjoin_induction with | mem | algebraMap | add | mul`.
- `Submodule.span_mul_span` + `Submodule.mul_mem_mul` to show a span is closed under products when
  generators multiply to generators (monomials via `Fin.append`, `Fin.prod_univ_add`).
- `ring` that only closes via `ring_nf` prints an info "Try this: ring_nf"; use `ring_nf` there.

### Gaussian integration by parts on `ι → ℝ` (tide `gaussian-moments-high`)

- Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` works on `ι → ℝ` with `volume`
  (the `IsAddHaarMeasure` instance is found). It takes three integrability facts and
  `∀ x ∈ tsupport g, DifferentiableAt ℝ f x` (give `fun x _ => (h x).differentiableAt`). Prove
  `HasFDerivAt` statements and rewrite with `.fderiv`; never unfold `fderiv`.
- Product rule: `HasFDerivAt.finsetProd (hg : ∀ i ∈ u, HasFDerivAt (g i) (g' i) x) :
  HasFDerivAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) x` (the `finset_prod`
  spelling is deprecated). Coordinates: `hasFDerivAt_apply i u : HasFDerivAt (fun f => f i) (proj i) u`.
  Sums of functions: `HasFDerivAt.sum` after `have : quadForm H = ∑ i, fun u => u i * (H u) i := by
  funext u; simp [quadForm, Finset.sum_apply]`. Evaluate derivatives with
  `simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
  ContinuousLinearMap.proj_apply, smul_eq_mul]` (`ContinuousLinearMap.sum_apply` etc. are deprecated).
- `Integrable.neg.congr` presents the function as `-f` (Pi negation): put `Pi.neg_apply` in the simp
  set, otherwise `ring` faces `(-fun u => …) u`.
- `∏_{s ≠ r}` as `∏ s, if s = r then 1 else f s`: `prod_erase_eq_prod_ite` converts from
  `univ.erase r` (`Finset.prod_erase` with `f r = 1`), `prod_ite_eq_prod_succAbove` reindexes to
  `Fin n` (`Fin.prod_univ_succAbove`, `Fin.succAbove_ne`); the `Fin 0` case is `r.elim0` after
  `cases n`.
- Products of linear forms: `Finset.prod_univ_sum` then `Fintype.piFinset_univ` gives
  `∏ s, ∑ k, f s k = ∑ k : Fin n → ι, ∏ s, f s (k s)`. Monomial to exponent form:
  `rw [← Finset.prod_fiberwise univ k (fun s => v (k s))]` on the `Fin n` product *before*
  `← Finset.prod_mul_distrib` against an `ι`-indexed product (the two products have different index
  types until then).
- Instantiating a `Fin n → ι` statement at `![a, b, c]`: `simp only [Fin.sum_univ_three,
  Fin.prod_univ_three, Fin.isValue, cons_val_zero, cons_val_one, cons_val, mul_ite, mul_one, ite_mul,
  one_mul, Fin.reduceEq, ↓reduceIte, one_ne_zero, zero_ne_one] at h` (from `simp?`). Do not let
  `simp` at the hypotheses fire lemmas that change the shape you later `rw` against: `matCLM_apply`
  is `@[simp]`, so `rw [integral_sub hI1 hI2]` fails on `(P *ᵥ u) l` vs `(matCLM P) u l` unless the
  simp set is explicit (or `-matCLM_apply`).
- `LaplaceCovHypotheses`, `LaplaceCov4MomentHypotheses`, `LaplaceCov6MomentHypotheses` are Props:
  build them with `theorem … where`, not `def`.
- `linter.unusedFintypeInType` fires falsely on `HasFDerivAt`/`fderiv` statements over `ι → ℝ` (the
  Pi norm needs `Fintype ι`; `omit [Fintype ι]` breaks elaboration): use
  `set_option linter.unusedFintypeInType false in`.
- `continuous_gaussianWeight` (RescaledIntegrals) carries an unneeded `[DecidableEq ι]`;
  `unfold gaussianWeight quadForm; fun_prop` proves continuity without it.

### Finite tensor contractions on `Fin d` (tide `oneloop-rosenbrock`)

- Write contractions as `Matrix.of fun i j => ∑ k, ∑ l, …` over `Fin d`; concrete `Fin 2` instances
  close by `ext i j; fin_cases i <;> fin_cases j <;> simp [defs, Fin.sum_univ_two] <;> field_simp <;> ring`.
  Prove each contraction (`contractQ`, `bubble`, `tadpoleLine`) as its own lemma before assembling
  `Π` and `SΠS`; a 4-fold sum inside a triple matrix product in one `simp` call is slow and opaque.
- `simp` unfolds your definitions *before* trying your rewrite lemmas about them: in
  `simp [tadpoleLine, contractT_rosenbrock …, rosenT, rosenSigma]` the `contractT_rosenbrock` rewrite
  never fires because `rosenT`/`rosenSigma` were already unfolded. Do `simp only [tadpoleLine,
  Matrix.of_apply, contractT_rosenbrock …]` first, then the unfolding `simp`.
- On `Fin 1` matrices, `fin_cases` + `simp` leaves `vecHead (c • vecHead (c' • fun i j => …))`;
  add `Matrix.vecHead, Pi.smul_apply, smul_eq_mul` to the simp set.
- Nested vector notation `![![![…], …], …] : Fin 2 → Fin 2 → Fin 2 → ℝ` for a tensor works fine under
  `Fin.sum_univ_two`; an `if i = 0 ∧ j = 0 ∧ … then c else 0` tensor also reduces.
- 1D Taylor tensors as constant functions `fun _ _ _ => alpha`; `!![lam]⁻¹` via
  `Matrix.inv_eq_right_inv` + `fin_cases` + `simp [Matrix.mul_apply]; field_simp`.
- Squeeze idiom for a rate bound `∀ {t}, T ≤ t → |f t − c/t| ≤ K/(t√t)` to a limit of `t·(f t)`:
  `filter_upwards [eventually_ge_atTop T, eventually_gt_atTop 0]`, `rw [mul_sub, mul_div_assoc',
  mul_div_cancel_left₀ c ht.ne']`, `abs_mul`, `abs_of_pos`, then
  `tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using squeeze_zero' … hev hk)`
  with `hk : Tendsto (fun t => K / √t) atTop (𝓝 0)` from
  `(tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul K` and `simpa [div_eq_mul_inv]`.
- `gibbsCov L t id id` unfolds to `gibbsExpectation (fun x => x * x)`; `simp only [gibbsCov, ← pow_two]`
  matches the seabed's `fun x => x ^ 2` moments.
- The linter `unnecessarySeqFocus` flags a trailing `<;> ring` when `simp` already closed all goals
  but one; put `ring` on its own line.

### Tilted Gaussians and translation (tide `localised-bias`)

- `MeasureTheory.integral_add_right_eq_self (f) (g) : ∫ x, f (x + g) = ∫ x, f x` holds on `ι → ℝ`
  with `volume` and needs no integrability; use it as
  `rw [← integral_add_right_eq_self (fun u => f u * gW (u - m)) m]; simp only [add_sub_cancel_right]`
  (the name is generated by `to_additive` from `integral_mul_right_eq_self`, so `grep` for the
  additive name finds nothing).
- `integral_add hf hg` needs `hf`/`hg` about *lambdas*: `h1.add h2` produces the Pi-sum
  `(fun u => …) + (fun u => …)` and `rw [integral_add (h1.add h2) h3]` then fails to match
  `A u + B u + C u`. Ascribe: `have h12 : Integrable (fun u => A u + B u) := h1.add h2`.
- First moments of the centred Gaussian: `simpa using gaussian_stein_prod_coord_matCLM hP
  (fun k : Fin 0 => Fin.elim0 k) i`; integrability of `u i * gW u`:
  `simpa using integrable_prod_coord_mul_gaussianWeight_matCLM hP (fun _ : Fin 1 => i)`.
- `x ⬝ᵥ P *ᵥ y = y ⬝ᵥ P *ᵥ x` for `P.PosDef` without `matCLM` (hence without `DecidableEq`):
  `rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPt, dotProduct_comm]` with
  `hPt : Pᵀ = P` from `hP.1.eq` and `Matrix.conjTranspose_eq_transpose_of_trivial`.
- `Matrix.PosDef` and `PosSemidef` need no `Fintype` (Finsupp sums): `omit [Fintype ι] in` for
  `(t • H + γ • 1).PosDef := (hH.smul ht).add_posSemidef (Matrix.PosSemidef.one.smul hγ)`.
  `omit … in` must come *before* the docstring.
- When the statement is `DecidableEq`-free but the proof goes through `matCLM`, write
  `omit [DecidableEq ι] in theorem … := by classical; …`.
- `simp only [...] at h` on a hypothesis mentioning `(t • H) i j` can fail with "function expected
  `(t • H) x`" (Matrix-as-function transparency); prefer `Finset.sum_congr rfl fun j _ => by
  rw [Matrix.smul_apply, smul_eq_mul]` on goals, and `hdiag`-style pointwise lemmas.
### Symbolic coefficient matrices over the shear coordinates (tide `valley-quadratic`)

- The Rosenbrock pattern `gibbsExpectation_valley_of_poly … ![![…], …] _ (fun q => by simp only
  [Fin.sum_univ_five, quadFn, valleySlope]; simp; ring)` works unchanged with symbolic entries
  (`μ * quadFn b c e μ`, `2 * valleySlope μ b c * b`); keep the floor `quadFn` and the slope
  `valleySlope` as named defs in statements and unfold them only inside the `hφ` proof.
- In a section with `variable (g : ℝ → ℝ) (hg : Continuous g)` and `include hg`, lemmas whose
  statement mentions `μ` only through `valley μ g a` need `(μ := μ)` when used as `have h := …`.
- After `simp` on the closed forms a stray `b * t⁻¹ = b / t` may remain: finish with `ring`.
- `field_simp` closes all but one of the `fin_cases` branches: put the final `ring` on its own
  line (the `unnecessarySeqFocus` linter flags `<;> ring` otherwise), and drop `Matrix.smul_mulVec`
  / `dotProduct_smul` rewrites before `congr 1` (they leave a spurious `True ∨ b = 0 ∨ t = 0`
  goal); `simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring` does it directly.

### Uniform subsets and finite-population counting (tide `minibatch-fpc`)

- `Finset.card_filter_powersetCard_subset s t n (hst : s ⊆ t) (hsn : #s ≤ n) :
  #((t.powersetCard n).filter (s ⊆ ·)) = (#t − #s).choose (n − #s)` counts the `n`-subsets containing
  `s`; convert the predicate with `Finset.filter_congr fun B _ => Finset.singleton_subset_iff.symm`
  (singletons) or `rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]` (pairs; a bare `simp
  [Finset.insert_subset_iff]` times out here). The pair count `C(n−2, m−2)` is *wrong at `m = 1`*
  under truncated subtraction: guard it (`if 2 ≤ m then … else 0`) and prove the `m = 1` branch by
  `Finset.card_le_card` of `{i, j} ⊆ B`.
- Double counting: `∑ i ∈ B, F i = ∑ i, if i ∈ B then F i else 0` (`← Finset.sum_filter` +
  `univ.filter (· ∈ B) = B`), then plain `Finset.sum_comm`, then `← Finset.sum_filter`,
  `Finset.sum_const` and the count. **Never `simp_rw` with that indicator lemma**: its right-hand
  side is again a `Finset` sum and `simp` loops to a heartbeat timeout; use
  `rw [Finset.sum_congr rfl fun B _ => lemma B f]`.
- Binomials: `Nat.add_one_mul_choose_eq n k : (n+1) * choose n k = choose (n+1) (k+1) * (k+1)`
  (`succ_mul_choose_eq` no longer exists); reindex `n = n' + 1` with `obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1
  := ⟨n - 1, by omega⟩`. Cast cross-multiplied ℕ identities to ℝ with `exact_mod_cast`, and
  `Nat.cast_sub (by omega : 1 ≤ n)` for `((n − 1 : ℕ) : ℝ)`.
- Bilinear maps `β : V →ₗ[ℝ] V →ₗ[ℝ] W`: `LinearMap.map_smul₂`, `LinearMap.map_sum₂` for the first
  argument (`rw [map_smul]`/`rw [map_sum]` picks the *second* argument first and then
  `LinearMap.smul_apply`/`sum_apply` find nothing). Build instances with `LinearMap.mk₂ ℝ f h₁ h₂ h₃ h₄`
  (`add_vecMulVec`, `smul_vecMulVec`, `vecMulVec_add`, `vecMulVec_smul`; for `X * S * Yᵀ`: `simp
  [add_mul]`, `simp`, `simp [Matrix.transpose_add, mul_add]`, `simp [Matrix.transpose_smul]`).
- nsmul from `Finset.sum_const` versus real smul: `← Nat.cast_smul_eq_nsmul ℝ`, then `sub_smul`,
  `smul_smul`; scalar bookkeeping as a separate lemma with `N₁ = C m / n` via `(eq_div_iff hn).mpr`
  then `field_simp; ring`.
- Definitions in a section with `variable [Fintype ι] [DecidableEq ι]` inherit the instances even
  if unused (`Matrix ι ι ℝ`, `vecMulVec`, `X * S * Yᵀ` need only `Fintype` or nothing); `omit … in`
  the defs too, or every user of them needs the instance.

### Reusing the rate theorems and the observable packages (tide `hessian-route`)

- `cov2Coefficient`/`cov2Coefficient_full` in `CovarianceExplicit.lean` were `private`, so the tagged
  theorem `gibbsCov_first_order_rate_explicit` could not be restated outside its file; they are now
  public. A `private def` appearing in a public theorem statement is a usability defect: avoid it.
- Building an `ObservableTensorApprox φ a` by hand: fields in order `phi_continuous`, `phi_zero`,
  `local_radius/const` (+ positivity), `local_bound`, `poly_growth : HasPolyGrowth φ` (witnesses
  `⟨K, p, hK, fun w => …⟩`), then the jet layer `qφ`, `qφ_continuous`, `qφ_even : Function.Even qφ`,
  `qφ_bound_const(_nonneg)`, `qφ_bound`, `jet_radius/const` (+ positivity/nonneg), `jet_bound`
  (`‖w‖³`), then `A`, `A_symm : dot u (A v) = dot v (A u)`, `qφ_eq_A_diag`, `Φ`, `Φ_symm`,
  `Φ_jet_bound` (`‖w‖⁴`; same radius and constant as `jet_bound`, so take `min`/`max` when the
  potential package has different ones). With `a = 0`, clear `dot 0 w` by
  `simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]` (`Pi.zero_apply` is
  essential). `Φ := 0` satisfies `Φ_symm` by `simp`.
- Sup norm on `ι → ℝ`: `|w i| ≤ ‖w‖` is `norm_le_pi_norm w i` (+ `Real.norm_eq_abs`);
  `|wᵀPw| ≤ (∑ᵢⱼ |Pᵢⱼ|) ‖w‖²` by `Finset.abs_sum_le_sum_abs` twice and `gcongr`.
- `abs_add` is `abs_add_le` at this pin; `add_le_add_right` adds on the left here, so prefer
  `add_le_add h le_rfl`. `gcongr` leaves side goals like `0 ≤ hV.local_const` that `positivity`
  cannot see: use `mul_le_mul_of_nonneg_left h hV.local_const_nonneg` explicitly.
- `trASig (matCLM P) (matCLM P⁻¹) = card ι`: `simp only [trASig, matCLM_apply, Matrix.mulVec_mulVec,
  hPP, Matrix.one_mulVec, Pi.single_eq_same, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
  mul_one]` with `hPP : P * P⁻¹ = 1`.
- After changing an imported seabed file, `lake build <Module>` for it and then `lean-state restart`
  before `check`ing dependents (the daemon holds the old oleans).

### Unfolding the second-order coefficient (tide `covk-closed-form`)

- `cov2Coefficient` unfolds to four terms in `trASig`, `dot`, `tensorContractMatrix` and nested
  `ContinuousLinearMap.comp`s. Cancel `matCLM P ∘ matCLM P⁻¹` with dedicated equalities
  (`comp_inv_comp_eq`, `inv_comp_comp_inv_eq`) proved by `← ContinuousLinearMap.comp_assoc h g f`
  with all three maps given explicitly (otherwise `rw` reassociates the inner composition), then
  `matCLM_comp_inv`/`matCLM_inv_comp` and `id_comp`/`comp_id`; pointwise `Hinv (A (Hinv v)) = Hinv v`
  by `matCLM_inv_apply_matCLM`.
- Structure projections of a `def` (`(quadObservable P hP).A`, `.Φ`, `.jet_radius`) are exposed
  with `rw [show … = … from rfl]`; `simp` will not unfold them, and `simpa using` fails on them.
- `trASig`, `tensorContractMatrix` mention `Pi.single`, so they need `[DecidableEq ι]`: do not `omit`
  it on lemmas about them ("cannot omit referenced section variable").
- `tensorContractMatrix 0 Sig = 0` is `funext i; simp [tensorContractMatrix]` (the `Fin 3` match is
  harmless once the zero multilinear map is applied); `trASig (B.comp Hinv) 1 = trASig B Hinv` is
  `simp [trASig]`.
- After changing an imported seabed file, a fresh worktree needs `lake build <Module>` before the
  daemon can `check` dependents; the first `check` may report a spurious "file elaboration timed
  out" while the big oleans load — rerun it.
### Random affine steps: averaging over batch and Gaussian noise (tide `minibatch-step`)

- Keep both expectations in density/finite-average form: `stdExp φ := (∫ φ ξ * gW(matCLM 1) ξ) / Z`
  (with `Matrix.PosDef.one`, `P⁻¹ = 1` via `inv_one`) and `batchAvg m F := (n.choose m)⁻¹ • ∑ B ∈
  powersetCard m univ, F B`; vector/matrix expectations entrywise (`stdExpVec`, `stdExpMat` as
  functions, `ext i j` to enter). Polynomial integrands of degree ≤ 2 in the Gaussian variable:
  expand with `ring` inside a `hexp : ∀ ξ, … = …`, `simp_rw [hexp]`, then `integral_add` with
  *lambda-typed* integrability facts (`have h12 : Integrable (fun ξ => A ξ + B ξ) := h1.add h2`).
- `batchAvg_const` needs the lambda's domain spelled out: `batchAvg m (fun _ : Finset (Fin n) => x)`;
  otherwise the implicit `n` cannot be inferred from the statement.
- Linear maps under `batchAvg`: `batchAvg m (fun B => outerBilin x (Δ B)) = outerBilin x (batchAvg m Δ)`
  by `unfold batchAvg; rw [map_smul, map_sum]` (second argument) or
  `rw [LinearMap.map_smul₂, LinearMap.map_sum₂]` (first argument), then
  `simp only [outerBilin, LinearMap.mk₂_apply]`. Do **not** `simpa [batchAvg, outerBilin]`: `simp`
  distributes `vecMulVec` over sums and turns `c • X = 0` into disjunctions.
- Expanding `vecMulVec (x − c • y) (x − c • y)`: `simp only [sub_vecMulVec, vecMulVec_sub,
  smul_vecMulVec, vecMulVec_smul]` then `module` (not `abel`, which treats `c • (X + Y)` as an atom).
  `vecMulVec (A *ᵥ w) (A *ᵥ w) = A * vecMulVec w w * Aᵀ` is `Matrix.mul_vecMulVec`,
  `Matrix.vecMulVec_mul`, `Matrix.vecMul_transpose`.
- `Matrix.smul_mulVec : (c • A) *ᵥ v = c • A *ᵥ v` (there is no `smul_mulVec_assoc`);
  `Matrix.sum_mulVec : (∑ i, x i) *ᵥ y = ∑ i, x i *ᵥ y`.
- Law form with a probability measure: entrywise scalar integrals against hypotheses
  `∫ w i = q i`, `∫ w i * w j = M i j` plus their `Integrable` facts; entry lemmas
  `(A * X * Aᵀ) i j = ∑ k ∑ l, A i k * A j l * X k l` (`Matrix.mul_apply`, `Finset.sum_mul`,
  `Finset.sum_comm`, `ring`) and `vecMulVec (D *ᵥ w) g i j = ∑ l, (D i l * g j) * w l`;
  `integral_const` gives `μ.real univ • c`, discharged by `simp only [measureReal_def, measure_univ,
  ENNReal.toReal_one]` (`measureReal_univ_eq_one` does not exist at this pin).
- After `set A := …` and unfolding a definition that re-introduces the same expression, `rw [← hA]`
  before `ring`; and when one side has `c * ∑ f` and the other `∑ c * f`, `simp only
  [← Finset.mul_sum]` first.
- Under `open scoped Nat`, `φ` is the totient NOTATION: a binder `(φ : ι → …)` fails with
  "unexpected token 'φ'; expected identifier". Rename the family (`F`) or don't open `Nat`.
- `rw [show (1 : ℕ) = 2 * 0 + 1 by norm_num]` rewrites the `1` inside `Fin 1` too (motive not type
  correct); derive the specialised fact with `simpa using lemma H 0` instead.

### Geometric tails, Toeplitz sums and eigenbasis conjugation (tide `direction-closures`)

- `∑_{k<N} x^k ≤ 1/(1−x)` for `0 ≤ x < 1`: `geom_sum_eq` (needs `x ≠ 1`) then `div_le_div_of_nonneg_right`/`div_le_iff₀`; the
  numerator `1 − x^N ≤ 1` is `pow_le_one₀`. Toeplitz double sums `∑_{i<N} ∑_{j<N} ρ^{|i−j|}` are bounded termwise via
  `(N − m − 1) ρ^{m+1} ≤ N ρ^{m+1}` after `Finset.sum_range_succ`-style reindexing; do not try to evaluate them in closed form.
- A bound of the shape `a − X ≤ a·(u + v)` with `X` a definitional unfolding: prove the identity `a − X = …` with `ring`/`field_simp`
  first (`have hX : X = …`), then `linarith`/`gcongr` on the pieces. `gcongr` leaves side goals it cannot discharge on
  products of nonnegative factors; give `mul_le_mul_of_nonneg_left h (by positivity)` explicitly.
- Realising an abstract chain bound for ULA: rewrite the seabed theorem's RHS into the abstract form with `change … ≤ _` (definitional
  unfolding of `finiteChainPrediction`), apply the abstract bound, then relax `(1+ρ)/(1−ρ) ≤ 2/(hp)` via
  `div_le_div_of_nonneg_right` after `show (1:ℝ) − (1 − h*p) = h*p by ring`. No measure theory is needed at this level.
- Eigenbasis conjugation of `t•H + γ•1` with `U = orthoOf hH.1`: `effectivePrecision = U * diagonal (t λᵢ + γ) * Uᵀ` from
  `spectral_real` plus `U * Uᵀ = 1` (`Matrix.mul_smul`, `smul_diagonal`... prove the diagonal affine identity entrywise with
  `ext i j; by_cases h : i = j; simp [diagonal, h]`). Inverting: `(U D Uᵀ)⁻¹ = U D⁻¹ Uᵀ` via `Matrix.inv_eq_right_inv` and
  associating explicitly around `Uᵀ U` — after `rw [← Matrix.mul_assoc Uᵀ U, hUtU, Matrix.one_mul]` the goal already has the form
  `D⁻¹ * 1`, so a second `hUtU` rewrite fails; finish with `Matrix.mul_one`.
- `∑ᵢⱼ Aᵢⱼ Bᵢⱼ = trace (A * Bᵀ)`; for symmetric `B` cycle with `Matrix.trace_mul_cycle`, cancel `Uᵀ U`, and finish with
  `diagonal_mul_diagonal` + `trace_diagonal`. Along an eigenvector `H u = λ u`, `(tH+γ)u = (tλ+γ)u` (`Matrix.add_mulVec`,
  `Matrix.smul_mulVec`, `one_mulVec`), so `(tH+γ)⁻¹ u = (tλ+γ)⁻¹ u` by applying the inverse to both sides
  (`Matrix.mulVec_mulVec`, `nonsing_inv_mul`).
- `Measure.integral_comp_mul_left (g) (a) : ∫ x, g (a * x) = |a⁻¹| • ∫ g` lives in the `Measure`
  namespace (Haar/NormedSpace); `integral_comp_abs : ∫ x, f |x| = 2 * ∫ x in Ioi 0, f x` is root.
  Gamma-type values: `integral_rpow_mul_exp_neg_rpow (hp : 0 < p) (hq : -1 < q) :
  ∫ x in Ioi 0, x ^ q * exp (-x ^ p) = (1/p) * Gamma ((q+1)/p)` (rpow exponents; convert with
  `Real.rpow_natCast`, which is unconditional).
- `field_simp` rewrites `-1 / (2k)` to `-(1 / (2k))` inside rpow EXPONENTS, so a hypothesis
  `hA : ∫ … a y ^ (-1 / (2k)) ≠ 0` no longer matches afterwards; cancel with
  `mul_div_mul_left/right _ _ h` BEFORE `field_simp`, or restate the exponent.
- `conv_lhs => rw [← Real.rpow_one x]` rewrites EVERY `x` on the lhs (also inside `x ^ e`); use
  `have := Real.rpow_add hx 1 e; rw [Real.rpow_one] at this; rw [← this]` instead.
- `rw [show (1 : ℕ) = … ]` / `show (4:ℕ) = 2*2` style rewrites hit numerals inside `Fin 1`, `Fin 4`
  (motive not type correct); specialise the lemma instead (`simpa using lemma H 0`).
- `Real.rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z` gives exponent injectivity
  (`le_antisymm` of both directions); `Real.rpow_left_injOn (hz : z ≠ 0)` gives base injectivity on
  `{0 ≤ y}`.
- `congrArg (fun x ↦ c * x) h` is already beta-reduced; a following `simp only at this` errors
  with "no progress".

### Eigenbasis traces, quadratic forms and running means (tide `llc-closures`)

- Trace of a product in the eigenbasis: conjugate *both* factors (`(Uᵀ P U) (Uᵀ Σ U)`), fold the middle `U Uᵀ = 1` with
  `simp only [Matrix.mul_assoc]` + one `← Matrix.mul_assoc`, then `Matrix.trace_mul_cycle`; `simp only [Matrix.trace, Matrix.diag,
  Matrix.diagonal_mul]` turns `tr(diagonal p * X)` into `∑ i, p i * X i i`. `trace_mul_ulaCov` is the template.
- `∑ i, (Uᵀ C U) i i = tr C` is `change (Uᵀ * C * U).trace = C.trace; rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]`; nonnegativity of
  the diagonal from `hC.conjTranspose_mul_mul_same U` + `Matrix.conjTranspose_eq_transpose_of_trivial` + `.diag_nonneg`.
- Rewriting `P` by `spectral_real hP` fails with a motive error when `hP : P.IsHermitian` appears in the goal (inside `orthoOf hP`);
  state the rewritten form as a `have … := by rw [← spectral_real hP]` instead. The quadratic form `x ⬝ᵥ P *ᵥ x = ∑ pᵢ ((Uᵀ x)ᵢ)²` is then
  `← mulVec_mulVec` twice, `dotProduct_mulVec`, `← mulVec_transpose`, `simp only [dotProduct, mulVec_diagonal]`, termwise `ring`; the
  Euclidean wrapper is `inner_toEuclideanCLM` and, for `(Uᵀ x)ᵢ = ⟨orthoCol i, x⟩`, `simp only [EuclideanSpace.inner_eq_star_dotProduct,
  star_trivial, orthoCol, mulVec, dotProduct, transpose_apply]` + `mul_comm` termwise. `(t • H) *ᵥ x` is `smul_mulVec` (not
  `smul_mulVec_assoc`).
- `field_simp` only clears a denominator whose `≠ 0` fact is present *in the normal form it produces*: after clearing `/ 2` it wants
  `2 - h * pmax ≠ 0`, and it commutes products (`p * h`, not `h * p`); when `ring` fails after `field_simp`, read the goal with
  `lean-state goal` and add the missing `≠ 0` facts in both orders rather than fighting the normal form.
- Sum-then-divide bookkeeping in running means: `∑ i, f i / d = (∑ i, f i) / d` is `← Finset.sum_div`; `∑ i ∈ range N, (1 - a i) =
  N - ∑ a i` is `Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one`. For a chain of `integral_finsetSum`
  under a double sum use `Finset.sum_congr rfl fun c _ => integral_finsetSum _ fun i _ => hint c _` inside `rw`.
- Geometric tails with possibly negative `ρ`: state `∑ ρ^{2(b+1+i)} ≤ ρ^{2(b+1)}/(1 - ρ²)` with the hypothesis `ρ ^ 2 < 1` and prove
  `0 ≤ ρ ^ (2 * (b + 1))` by `rw [pow_mul]; positivity` (`positivity` cannot see the even exponent through `2 * (b + 1)`).
- `ulaChain`/`euclid` need `[DecidableEq ι]` (`toEuclideanCLM`), so `omit [DecidableEq ι]` is refused there; `omit [IsProbabilityMeasure P]`
  is right for the `MemLp`/`Integrable` lemmas that never integrate.
### Fourth moments of chains: Hölder, block independence and Gaussian transport (tide `estimator-variance`)

- Products of `L⁴` functions: declare `instance : ENNReal.HolderTriple 4 4 2` once (`inv_add_inv_eq_inv` via
  `show (4 : ENNReal) = 2 * 2`, `ENNReal.mul_inv`, `ENNReal.inv_two_add_inv_two`); then `hg.mul hf : MemLp (f * g) 2` and
  `MemLp.integrable_mul` (`HolderConjugate 2 2` is an instance) give `Integrable (f * g * (k * l))` for four `L⁴` factors. Keep every
  integrand *homogeneous of degree four* and written as a product of exactly four factors (`X * Y * (W * G)`), then a single
  helper covers all integrability side goals; `simpa only [sq, pow_one, mul_assoc]` bridges to the `^ 2`/`^ 1` spellings.
- `Finset.sum_coe_sort` does not fire in `simp` (the pattern `f ↑i` is not a higher-order pattern); use
  `rw [Finset.sum_coe_sort s (fun i => a i * g i ω)]` with the function given explicitly.
- Block independence from `iIndepFun g P`: `hind.indepFun_finset s {n} (Finset.disjoint_singleton_right.mpr hn) hmeas`, then
  `.comp` with the *pair* map `fun z : s → ℝ => (∑ i : s, a i * z i, ∑ i : s, b i * z i)` (measurable by `fun_prop`) and the
  evaluation `fun z : ({n} : Finset κ) → ℝ => z ⟨n, Finset.mem_singleton_self n⟩`; `convert this using 1` leaves the pair goal
  (`funext`, `Function.comp_apply`, the explicit `sum_coe_sort`) and the `g n = _ ∘ _` goal (`rfl`). Independence of `X` and of `Y`
  from `g n` separately does not give independence of `X * Y`; always go through the pair.
- Factorising `∫ φ (X ω, Y ω) * g n ω ^ k`: `IndepFun.comp hφ (measurable_id.pow_const k)` then
  `IndepFun.integral_fun_mul_eq_mul_integral` (needs only `AEStronglyMeasurable`). Pass `φ` explicitly as a lambda
  (`(fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) 2`); the instantiated statement is beta-reduced so `rw` matches the goal written
  as `X ω * Y ω * g n ω ^ 2`. Afterwards `rw [pow_one]` fails under the integral binder — use `simp only [pow_one]`, which also
  reduces the `(X ω, Y ω).1` projections.
- Finset induction with opaque abbreviations: `obtain ⟨X, hXd⟩ : ∃ X : Ω → ℝ, X = fun ω => ∑ i ∈ s, a i * g i ω := ⟨_, rfl⟩`
  (not `set`, whose body is not syntactically in the goal); `IsLinComb g s X := ⟨a, fun ω => by rw [hXd]⟩`; expansions
  `hexp : ∀ ω, … = …` by `simp only [hXd, hYd]; ring` then `simp_rw [hexp]`. `integral_add` needs the combined integrability
  facts typed as lambdas (`have h12 : Integrable (fun ω => A ω + B ω) P := h1.add h2`), or the `f a + g a` pattern will not match.
- `memLp_finset_sum` (no prime) is the `fun a => ∑ i ∈ s, f i a` form; the primed one is the `Pi` sum. `pow_le_pow_left` is now
  `pow_le_pow_left₀`. The deprecated `integral_finset_sum`/`integrable_finset_sum` are `integral_finsetSum`/`integrable_finsetSum`.
- Gaussian transport for `⟨u, ξ⟩`, `ξ ~ stdGaussian E`, `‖u‖ = 1`: `IsGaussian.hasGaussianLaw` (after `have : IsGaussian (P.map ξ)`
  by `rw [hlaw]; infer_instance`), `.map_fun (innerSL ℝ u)`, `.map_eq_gaussianReal`; the mean via `← integral_map` +
  `integral_innerSL_stdGaussian`, the variance via `variance_map (X := ⇑(innerSL ℝ u)) (μ := P) (Y := ξ)` (the `μ` must be
  given), `Function.comp_def`, `variance_dual_stdGaussian`, `innerSL_apply_norm`; finish with `Real.toNNReal_one`. Moments of
  `gaussianReal 0 1`: `integral_gaussianReal_eq_integral_smul one_ne_zero`, `gaussianPDFReal_def`, then the seabed's
  `Laplace.OneD.integral_pow_mul_exp_neg_sq_half`/`_odd` (write `Real.pi`, not `π`, unless `open Real`). `MemLp 4` by
  `memLp_id_gaussianReal' 4` + `memLp_map_measure_iff`. State `integral_map`/`memLp_map_measure_iff` with the map in the lambda form
  `fun ω => innerSL ℝ u (ξ ω)` (a `Measurable.comp` term has type `Measurable (f ∘ g)` and its `∘` will not match the goal).
- `Qᵀ` in a statement needs `open Matrix`; a parse error "unexpected token 'ᵀ'" is the symptom.

### Four-way Wick by Finset induction (tide `wick4`)

- Prove block independence once and abstractly: `indepFun_block_of_notMem : IndepFun (fun ω => F fun i : s => g i ω) (g n) P` for any
  measurable `F : (s → ℝ) → β`; the pair and quadruple versions are `convert … using 1` + `funext` + the explicit
  `Finset.sum_coe_sort s (fun i => a i * g i ω)` rewrites (`fun_prop` proves measurability of the tuple of sums).
- Nested pairs `((X, Y), (Z, W))` with `φ : (ℝ × ℝ) × (ℝ × ℝ) → ℝ` work well: pass each `φ` as an explicit projection lambda
  (`fun p => p.1.2 * p.2.1 * p.2.2`) and the instantiated statement is beta-reduced, so `rw` matches the goal written as
  `Y ω * Z ω * W ω * g n ω ^ 1`.
- Sixteen-term expansions: state the expansion as an equality of *functions* built with `Pi` addition of lambdas
  (`(fun ω => …) + ((fun ω => …) + …)`), prove it by `funext ω; simp only [Pi.add_apply, hXd, …]; ring`, then `rw [hexp]` and split with
  `integral_add' (h.add h') h''` — the `Integrable (f + g)` types line up with `Integrable.add` without retyping any lambda. Group the
  terms by the power of the new innovation so the `integral_add'` chain mirrors the grouping.
- One-line integrability helpers per term shape (`f * g * k * l ^ 1`, `f * g * l ^ 2`, `f * l ^ 3`, `l ^ 4`) via
  `simpa only [pow_one / sq / pow_succ, pow_zero, one_mul, mul_assoc] using integrable_mul_mul_mul_of_memLp_four …`.
- Second moments of the opaque abbreviations: a local `hpair : ∀ U V u w, U = (fun ω => ∑ …) → V = … → ∫ U * V = v * ∑ u * w` proved once
  by `← integral_linComb_mul` + `congr 1; funext; simp only [hU, hV]` saves six copies.

### Estimator algebra over finite index products (tide `frobenius-law`)

- Quantify linear-combination/`L⁴` hypotheses only over the *window* actually used
  (`∀ c i k, k ∈ range N → IsLinComb g s (x c i (b + 1 + k))`); a hypothesis for all times is false for a chain whose innovations
  beyond the window are not in `s`, and the proofs only ever need membership (`(Finset.mem_product.mp ha).2`).
- Variance of a weighted sum as a covariance double sum: `(q ∑ f)^2 = q^2 ∑∑ f_a f_b` (`mul_pow`, `sq`, `Finset.sum_mul_sum`), integrate
  with `integral_finsetSum` twice (the inner one through `Finset.sum_congr rfl fun a ha => integral_finsetSum _ …`), and finish with a
  generic identity `∑∑ (I a b - m a * m b) = ∑∑ I - (∑ m)^2` proved once for abstract `I m` (`sq`, `Finset.sum_mul_sum`,
  `← Finset.sum_sub_distrib` twice) so that `ring` never sees sums.
- Kronecker bookkeeping: rewrite the pointwise covariance first (`by_cases hij : i = j; subst; simp only [and_true, if_true];
  split_ifs <;> ring` / `simp only [hij, Ne.symm hij, and_false, if_false, …]`), then collapse `∑ c' (if c = c' then _ else 0)` with
  `Finset.sum_product_right` + `Finset.sum_ite_eq` + `Finset.mem_univ`, and pull the constant `if i = j then 2 else 1` out with
  `← Finset.mul_sum`; cancel `C`, `N` at the very end with `field_simp` (no trailing `ring` — it errors with "no goals" when
  `field_simp` closes the goal).
- `Finset.sum_eq_single i (fun j _ hji => by simp [Ne.symm hji]) (fun h => absurd (Finset.mem_univ i) h)` isolates the diagonal of a
  sum over `univ`; a sum of the form `∑ k, c * (a * (1 - r k))` is normalised by `← Finset.mul_sum, Finset.sum_sub_distrib,
  Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one` before `field_simp`.
- `gcongr` on `a * b ≤ c * d` with factors of mixed sign structure leaves side goals; `mul_le_mul h₁ h₂ (nonneg c) (nonneg b')` with
  explicit `mul_le_mul_of_nonneg_left` pieces is more predictable.
- `(univ : Finset ι)` needs `[Fintype ι]`, so `omit [Fintype ι]` is refused for statements mentioning it; `omit [MeasurableSpace Ω]`
  is fine for purely algebraic chain lemmas (it drops `P` too).
- Chains with *different* coefficients but orthogonal noise are orthogonal: `inner_x_x_of_orthogonal'` generalises the seabed's
  same-`ρ` lemma with the identical proof; the multi-direction Gram table then follows from `toAR1Chain` per `(c, i)` and the white
  table of the whole innovation family.
### Metropolis–Hastings in `lintegral` form (tide `mala-invariance`)

- State MH invariance with unnormalised densities and `lintegral` of `ENNReal.ofReal`: no integrability side conditions, Tonelli is
  `lintegral_lintegral_swap (hf : AEMeasurable (uncurry f) (μ.prod ν))` (take `ν := μ.restrict E` for the set integral), and constants
  move with `lintegral_const_mul' _ _ (h : r ≠ ∞)` (no measurability needed; `ENNReal.ofReal_ne_top`, `ENNReal.inv_ne_top.mpr hZ0`).
- Prove the flux identity over `ℝ` first: `π x * q x y * min 1 (π y * q y x / (π x * q x y)) = min (π x * q x y) (π y * q y x)` is
  `mul_min_of_nonneg _ _ hpos.le, mul_one, mul_div_cancel₀ _ hpos.ne'`; then transport through `ENNReal.ofReal_mul (hπ x).le`. The
  symmetric flux `mhFlux` is what gets swapped, never the acceptance probability.
- ENNReal subtraction `1 - a x` is safe once `a x ≤ 1` (`ENNReal.div_le_iff hZ0 hZtop` + `lintegral_mono`); finish with
  `add_tsub_cancel_of_le`. Indicators: `Set.indicator_of_mem hx`/`Set.indicator_of_notMem hx` after `by_cases` (`Set.indicator_apply`
  needs a `Decidable` instance and `simp only` may refuse it); `lintegral_indicator hE` turns `∫⁻ indicator` into `∫⁻ x in E`.
- Measurability of `x ↦ ∫⁻ y, f x y ∂ν` is `Measurable.lintegral_prod_right (hf : Measurable (uncurry f))`; for `min`/`div` use
  `Measurable.min`, `Measurable.div`, with `hqm.comp measurable_swap` for `q y x`. Give the measurability facts their function
  form by a typed `have` — a `.comp`/`.div_const` term carries `∘` and will not match `lintegral_withDensity_eq_lintegral_mul`.
- A numeral matrix must be pinned when nothing else fixes the index type: `propZ ((1 / (4 * h)) • (1 : Matrix ι ι ℝ))` — otherwise
  "typeclass instance problem is stuck: OfNat (Matrix ?n ?n ℝ) 1". Likewise `(Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul`.
- `c • M *ᵥ v` parses as `c • (M *ᵥ v)`; write `(c • M) *ᵥ v` explicitly when the term comes from a matrix identity such as
  `G = -(h/4) • (P * P)`, or `smul_mulVec` will not fire.
- Gaussian normalisations: row integrals of `exp(-(y - A x)ᵀ S (y - A x))` are all `∫ exp(-yᵀ S y)` by
  `lintegral_sub_right_eq_self (fun z => …) (A *ᵥ x)` (Lebesgue on `ι → ℝ` is add-invariant); positivity via
  `lintegral_pos_iff_support` + `isOpen_univ.measure_pos`; finiteness via the seabed's `integrable_gaussianWeight_matCLM` and
  `Integrable.lintegral_lt_top`, after rewriting `exp(-yᵀ S y) = gaussianWeight (matCLM (2 • S)) y` (`quadForm_matCLM`).
- The transpose/drift bookkeeping `(v - A u)ᵀ S (v - A u) = vᵀSv - 2 vᵀ(SA)u + uᵀ(AᵀSA)u` is `mulVec_sub, dotProduct_sub,
  sub_dotProduct` plus the three helpers (`dotProduct_mulVec_symm hS`, `mulVec_mulVec`, and `← vecMul_transpose A u,
  ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc` for `(Au)ᵀ S (Au)`).
## Gotchas from the truth-variation arc (2026-09-21)

- `HasDerivAt.sum` / `HasFDerivAt.sum` return the Pi-sum function `∑ j, fun u ↦ …`; convert with
  `have hfun : (fun u ↦ ∑ j, f j u) = ∑ j, fun u ↦ f j u := by funext u; simp [Finset.sum_apply]`.
- Matrix entries: `hasDerivAt_pi.mp (hasDerivAt_pi.mp hH i) j : HasDerivAt (fun u ↦ H u i j) (H' i j) u`.
- `qform_eq_dotProduct` + `simp only [dotProduct, Matrix.mulVec]` (root `dotProduct`) unfolds the
  quadratic form to `∑ i, x i * ∑ j, A i j * x j` and closes the goal by itself — no trailing `rfl`.
- Chain `hq.neg.div_const 2 |>.exp` then `.congr_deriv` for `u ↦ exp (-q u / 2)`; `convert … using 1`
  on a `HasDerivAt` leaves `NormedAddCommGroup`/`Module` instance goals instead.
- `Measure.integral_comp_mul_left g a` on `ℝ`: to solve for the ORIGINAL integral write
  `∫ F = a⁻¹ * ∫ F (a⁻¹ x)` via `rw [h, ← mul_assoc, inv_mul_cancel₀, one_mul]` (no `field_simp`).
- `continuousWithinAt_of_dominated` (domination only on `𝓝[Ici 0] s₀`) + `ContinuousOn.comp_continuous`
  when a parametric integral is only well-behaved for `s ≥ 0`.
- `Tendsto.const_mul_atTop (hr : 0 < r) (hf : Tendsto f l atTop)` (not a dot-lemma on `hf`).
- After `field_simp` closes a goal, a trailing `ring` errors "No goals"; likewise after `rw` that
  turns the goal into `rfl`, drop the following `congr 1`.
- `a⁻¹ * (a * X)`-style cancellations: `mul_div_mul_left _ _ (inv_ne_zero h)`; the `(√t)^r` factors
  cancel with `mul_div_mul_left _ _ (pow_ne_zero _ …)` after `simp only [Pi.div_apply]`.

### Packaging a sampler as a `ProbabilityTheory.Kernel` (tide `mala-kernel`)

- A `Kernel X X` is a measurable `X → Measure X`; build it with `Measure.measurable_of_measurable_coe _ fun E hE => …`, proving
  measurability of `x ↦ K x E` for each measurable `E` after rewriting `K x E` to the set formula (`withDensity_apply _ hE`,
  `Measure.add_apply`, `Measure.smul_apply`, `Measure.dirac_apply' _ hE`, then `by_cases hx : x ∈ E <;> simp [hx]` for the indicator).
  The constructor's measurability field cannot take hypotheses from thin air: make them arguments of the `def` (`mhKernel hπm hqm μ hZ0`).
- `IsMarkovKernel κ` is `⟨fun x => ⟨κ x univ = 1⟩⟩`; evaluate with the set formula, `Set.indicator_univ`, `Measure.restrict_univ`, and
  `add_tsub_cancel_of_le`.
- The fixed-point statement is literally `ν.bind κ = ν`: `ext E hE; rw [Measure.bind_apply hE κ.measurable.aemeasurable]`, rewrite the
  integrand with the set formula (`simp_rw`), and apply the `lintegral` invariance theorem. `n`-step stationarity is
  `Function.iterate_succ_apply'` + induction, three lines.
- Real integrals against a `withDensity` measure with an `ℝ≥0∞` density: `integral_withDensity_eq_integral_toReal_smul₀ (hf.aemeasurable)
  (ae_of_all _ fun x => ENNReal.div_lt_top ENNReal.ofReal_ne_top hT0) g`, then `ENNReal.toReal_div`, `ENNReal.toReal_ofReal (nonneg)`;
  integrability likewise via `integrable_withDensity_iff_integrable_smul₀'`. The normaliser's `toReal` is
  `integral_eq_lintegral_of_nonneg_ae (ae_of_all _ …) (cont.aestronglyMeasurable)` read backwards.
- `P⁻¹` and `matCLM` need `[DecidableEq ι]`: give it as an explicit instance binder on the theorems whose *types* mention them, and use
  `classical` inside proofs that only need it internally (the `unusedDecidableInType` linter flags the other arrangement).
- Total-variation bounds from uniform-in-test bounds: test against the sign of the remainder,
  `f := fun x ↦ if 0 ≤ g x then 1 else -1` (`Measurable.ite (measurableSet_le measurable_const hg)`),
  so `∫ f * g = ∫ |g|`; avoids the signed-measure API entirely.
- Bounds `a ^ e ≤ a₀ ^ e` for `0 < a₀ ≤ a`, `e ≤ 0`: `Real.rpow_neg` on both sides then
  `inv_anti₀ (Real.rpow_pos_of_pos …) (Real.rpow_le_rpow …)`; `positivity` cannot see `a > 0` from
  a hypothesis, so give `(Real.rpow_pos_of_pos ha _).le` explicitly.
- A cutoff family vanishing off a common `K` has vanishing `u`-derivative off `K`: `HasDerivAt.unique`
  against `hasDerivAt_const` after rewriting the family to the zero function.
- `omit [Nonempty X] in` before theorems that don't use the section instance (linter
  `unusedSectionVars`); `(_h : TiltData …)` keeps dot-notation while silencing unused-variable.
- Unicode `Θ` in the slop LaTeX breaks pdflatex: write `$\Theta$`.

### `Fin 2` directional corollaries of a closed-form covariance (tide `rosenbrock-e5`)

- Directional variances `v ⬝ᵥ M *ᵥ v` for explicit `![…]` vectors and `!![…]` matrices: `simp [mulVec, dotProduct, Fin.sum_univ_two]`
  then `field_simp` closes rational identities (no trailing `ring` — it fails with "no goals" when `field_simp` finishes). Rewrite the
  matrix by its closed form first (`rosenCov_eq_laplace_add`, `rosenHess_smul_inv`); `add_mulVec` is not needed once `simp` sees the
  explicit matrices.
- Numeric instances (`a = 100`, `t = 1000`): do **not** rewrite with the multiplicative-identity theorem and `norm_num` the factor — the
  goal keeps `1000 • M` on one side and `1000 * M` on the other. Rewrite both sides to their closed forms (`rosenCov_stiff`,
  `laplace_stiff`) and let `norm_num` compare rationals.
- Explicit Frobenius sums `∑ i, ∑ j, (M i j) ^ 2` over `Fin 2`: `simp [Fin.sum_univ_two]` after the closed form, then `field_simp`/`ring`.
- Namespaces: the 2D `gibbsExpectation`/`gibbsCov` live in `Laplace.TwoD` (SemiDegenerate.lean), the Rosenbrock helpers
  `rosenHess_smul_inv`, `rosenSigma` in `Laplace.Multi` (OneLoop.lean); `open Laplace.Multi` inside `namespace Laplace.TwoD`.
- The seabed's `rosenbrock` carries the factor `1/2`, so its Hessian is `!![1 + 4a, -2a; -2a, a]` and the note's `200/t` is `2a/t`;
  `H (2,-1) = 5a (2,-1) + (2,0)` (not `10a`).
### Joint Gaussian independence across a product index (tide `gaussian-table`)

- Independence of the scalar projections of independent Gaussian vectors: restrict the block index to a finite window with
  `iIndepFun.precomp (g := fun a : Fin C × Fin T => ((a.1, (a.2 : ℕ)) : Fin C × ℕ)) (injective)`, get the joint law with
  `iIndepFun.hasGaussianLaw (hG : ∀ a, HasGaussianLaw (ξ a) P)`, push it through
  `L := ContinuousLinearMap.pi fun a => (innerSL ℝ (u a.2.2)).comp (ContinuousLinearMap.proj (a.1, a.2.1))` and conclude with
  `HasGaussianLaw.iIndepFun_of_covariance_inner`. Use `HasGaussianLaw.map_of_measurable L L.continuous.measurable`, **not** `map_fun`:
  the latter expects the CLM with the normed-space instances on the Pi type (`Pi.normedSpace.toModule`), while the CLM you build carries
  `Pi.module`, and instance arguments are compared at reducible transparency. After `convert … using 2` the goal is already pointwise;
  `simp [L]` closes it.
- The covariance hypothesis quantifies over scalar probes `x y : ℝ` with `⟪x, z⟫ = z * x` (`RCLike.inner_apply`, `conj_trivial`);
  rewrite `fun ω => Z ω * c` to `fun ω => c * Z ω` by a small `funext`/`mul_comm` lemma and pull the constants out with
  `covariance_const_mul_left/right`. Same block: `covariance_map` (forms `X ∘ Z`, use `Function.comp_def`) then
  `← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id` and `covarianceBilin_stdGaussian`, finishing with `rfl` (`innerSL` applied is
  `inner`). Different blocks: `(hindW.indepFun hblock).comp` — state the resulting `IndepFun` with a typed `have` in lambda form, or
  `covariance_eq_zero` will not match.
- From finite windows to an `ℕ`-indexed family: `iIndepFun_iff_measure_inter_preimage_eq_mul`, take `T := S.sup (·.2.1) + 1`, embed
  with `a ↦ (a.1, ⟨a.2.1 % T, _⟩, a.2.2)` (total; the identity on `S` by `Nat.mod_eq_of_lt`), apply the window statement to `S.image e`
  with `sets := fun a' => sets (a'.1, ↑a'.2.1, a'.2.2)`, and transport with `Finset.set_biInter_finset_image`, `Finset.prod_image`,
  `Set.iInter₂_congr`, `Finset.prod_congr`. Write the tuples explicitly rather than through a `let r := …` (a `let`-bound function
  applied is not syntactically the tuple, so `rw` will not see through it). `Finset.image` needs `DecidableEq` of the target: `classical`.
- `orthonormal_iff_ite` + the `(Uᵀ U) i j = if i = j then 1 else 0` entry (as in `norm_orthoCol`) gives `Orthonormal ℝ (orthoCol hQ)`;
  `hu.1 i : ‖u i‖ = 1` and `hu.inner_eq_zero hij` are the two facts consumed downstream.
- `[Finite ι]` (not `Fintype`) is what `iIndepFun_of_covariance_inner` needs for the index; the `unusedFintypeInType` linter flags the
  stronger instance.

### Cross-covariances of estimator entries and weighted statistics (tide `llc-variance`)

- The four-way Wick identity `cov_mul_mul_of_isLinComb` gives `Cov(x_i x_j, x_i' x_j')` as two products of Gram entries, each an
  `if c = c' ∧ i = i' then G else 0`. Do not `split_ifs` on the whole expression inside the sum: factor the delta bookkeeping into a
  standalone real identity (`ite_pair_expand`: `(if i = i' then A else 0) * (if j = j' then B else 0) + … =
  ((if i = i' ∧ j = j' then 1 else 0) + (if i = j' ∧ j = i' then 1 else 0)) * (A * B)`), proven by `split_ifs <;> (simp_all; try ring)`
  (contradictory branches close by `simp_all`; the linter rejects `simp_all <;> ring` when a branch leaves one goal). Case on the chain index
  first (`by_cases hc : a.1 = a'.1; simp only [hc, true_and, if_true]`), then apply the identity.
- A weighted sum of estimator entries `∑ᵢ wᵢ Yᵢ`: get its variance from `variance_sum_eq_sum_cov univ (fun i ω => w i * Y i ω) … 1`
  (then `simp only [one_mul, one_pow] at hvar`), and reduce each `Cov(wᵢ Yᵢ, wⱼ Yⱼ)` to `wᵢ wⱼ Cov(Yᵢ, Yⱼ)` by rewriting the product
  function with a `funext; ring` equation, `integral_const_mul` three times, and a `ring`-proved refactoring `have`; then the general
  cross-covariance theorem and `by_cases hij : i = j` (`subst; simp only [and_self, if_true, ← sq]; ring` / `simp [hij]`).
  `Finset.sum_ite_eq` (with `Finset.mem_univ, if_true`) then collapses the double sum and `Finset.mul_sum` pulls the constant.
- Integrability of a product of two pooled estimators: rewrite both as sums over `univ ×ˢ range N` (`Finset.sum_product`), combine with
  `mul_mul_mul_comm, Finset.sum_mul_sum, ← sq`, and discharge each four-fold product by `integrable_mul_mul_mul_of_memLp_four`.
- Squared AR(1) Gram kernel: `(s₂ (ρ^d - ρ^{k+l}))² ≤ s₂² (ρ²)^d` via `mul_pow, ← pow_mul, mul_comm 2, pow_mul` and
  `pow_le_pow_left₀ h0 h1 2`; the Toeplitz envelope `toeplitz_sum_le` is then applied to `ρ²` (`0 ≤ ρ² < 1` by `positivity`/`nlinarith`).
  No sign hypothesis on `s₂` is needed for the squared kernel — the linter flags it if you keep it.
- Triple-sum reindexing `∑ c, ∑ k, ∑ i = ∑ i, ∑ c, ∑ k`: `rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]; exact Finset.sum_comm`.
  State the instance explicitly (a `key` with the concrete summand) rather than a higher-order pattern for `rw`.
- `field_simp` closes `a * b / c = …` goals outright when the denominators' nonzero facts are in context; a trailing `ring` then errors
  "no goals" — re-check every `field_simp; ring` after the fact. For `1 - h p/2` denominators give `2 - h * p ≠ 0` **and** `2 - p * h ≠ 0`.
- A theorem with no measure in its statement must live outside the `variable {P : Measure Ω} [IsProbabilityMeasure P]` section (the
  `unusedSectionVars` linter flags `[MeasurableSpace Ω]`); `omit [DecidableEq ι] in` goes *before* the docstring, and the proof then opens
  with `classical` if it calls a `DecidableEq`-typed lemma.

### Spectral functions of `tH + γI` (tide `localised-llc-bounds`)

- Conjugating an affine function of a symmetric matrix into the eigenbasis: `simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
  Matrix.smul_mul, Matrix.mul_one, orthoOf_transpose_mul_mul hH, orthoOf_transpose_mul hH]` turns `Uᵀ (t•H + γ•1) U` into
  `t • diagonal λ + γ • 1`; finish with `ext i j; by_cases hij : i = j` and `simp`.
- The inverse of a conjugated diagonal: exhibit it. `Matrix.inv_eq_left_inv` with the candidate `U * diagonal (1/a) * Uᵀ`; reassociate the
  product to expose `Uᵀ M U` (`simp only [Matrix.mul_assoc, hUU', Matrix.mul_one]` where `hUU' : U * Uᵀ = 1`), rewrite it by the conjugation
  lemma, then `Matrix.mul_assoc U`, `diagonal_mul_diagonal`, a `funext` identity `1/a i * a i = 1` (`one_div_mul_cancel`), `diagonal_one`.
  To then read off `Uᵀ M⁻¹ U`: `simp only [← Matrix.mul_assoc]` fully left-associates, then `rw [hUU, Matrix.one_mul, Matrix.mul_assoc, hUU,
  Matrix.mul_one]`.
- `∑ᵢⱼ Aᵢⱼ Bᵢⱼ = trace (Aᵀ B)`: `simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]; rw [Finset.sum_comm]`.
  `t • diagonal λ = diagonal (fun i => t * λ i)` is `← diagonal_smul` followed by `rfl`.
- Real-variable limits at `atTop`: `tendsto_atTop_add_const_left _ _ tendsto_id : Tendsto (fun γ => c + γ) atTop atTop`, then
  `(tendsto_inv_atTop_zero.comp hden).const_mul c` and `simpa [div_eq_mul_inv, Function.comp_def]`; sums with `tendsto_finsetSum`
  (`tendsto_finset_sum` is deprecated).
- `add_le_add_left h a` here produces `b + a ≤ c + a`, not `a + b ≤ a + c`; when the goal is `1 + x ≤ 1 + y`, derive the core inequality
  with a `have` and finish with `linarith` rather than guessing the side.
- Strict sum bounds: `Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty` (needs `[Nonempty ι]`), `Finset.sum_pos … Finset.univ_nonempty`;
  `div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b`.
### Bias–variance assembly and error budgets (tide `llc-mse`)

- Statements of the form `∫ ω, (X ω - a) ^ 2 ∂P ≤ RHS` where `X` is a defined statistic: annotate the integrand `((X ω - a) ^ 2 : ℝ)`.
  Without it the binop elaborator can pick `ℕ` for the integrand's expected type (`HPow ℝ ℕ ℕ`, `NormedAddCommGroup ℕ` failures at
  the `∑` inside) even though every leaf is real; the `=` versions never needed it because the RHS integrals fixed the type.
- Rewriting with an equation whose two sides print identically but fails (`rw` "did not find an occurrence"): use
  `(h_eq …).trans_le ?_` (`Eq.trans_le`) instead of `rw [h_eq]` — unification up to defeq succeeds where syntactic matching fails.
- Per-chain independence from the joint family: `have h := iIndepFun.precomp (Prod.mk_right_injective c) hind; exact h`. Do not write
  `hind.precomp …` against the expected type `iIndepFun (ξ c) P`: the unifier then solves `?f ∘ ?g = ξ c` with `g = id` and complains that
  `Prod.mk_right_injective c` should be `Function.Injective fun i ↦ i`. (`Prod.mk.inj_left` does not exist here; `Prod.mk_right_injective`
  is the name.)
- `ring` cannot prove `a / (N * B * q) = 1 / N * (a / (B * q))` when `B, q` are polynomials in other atoms: it normalises `N * B * q` into
  one polynomial and inverts it as a single atom. Use `rw [one_div_mul_eq_div, div_div]; congr 1; ring` (or `field_simp` with the
  nonzero facts in context).
- `div_le_div_iff` / `div_le_div_iff_of_pos` are not in this Mathlib; the positive-denominator form is `div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d)`.
- `√(a + b²) ≤ √a + b` (`a, b ≥ 0`): `rw [Real.sqrt_le_left (by positivity)]; nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a, mul_nonneg …]`.
  Compose an MSE bound into an RMS bound with `Real.sqrt_le_sqrt` then this lemma; `add_assoc` first so the bound reads `√env + (infl + short)`.
- Theorems mixing a probability-measure section with pure algebra (spectral sums, `Fintype.card`) go in their own `section` with only
  `{ι} [Fintype ι]`; keep `[DecidableEq ι]` out unless an `if` appears in the statement (`unusedDecidableInType`).

### The ULA law for a shifted precision in another matrix's eigenbasis (tide `ula-localised`)

- `Uᵀ (P * P) U = (Uᵀ P U)²` needs `U Uᵀ = 1` inserted: state the reassociated form as a `have` proved by `simp only [Matrix.mul_assoc]`,
  then `rw [hUU', Matrix.mul_one]`. With `Uᵀ P U = diagonal a` in hand, `Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul`
  distribute the conjugation over `P − (h/2) • (P * P)`, and `← diagonal_smul, diagonal_sub` (forward, to combine) give
  `diagonal (a − (h/2) a²)`.
- `ulaCov P h = (P − (h/2) • (P * P))⁻¹` conjugates by the same exhibit-the-inverse pattern as `(tH + γI)⁻¹`; write the denominator
  nonvanishing as `a − (h/2)a² = a (1 − h a/2)` (`ring`) and use `mul_ne_zero`.
- Reciprocal comparisons: `one_div_le_one_div_of_le (hpos : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a` (there is no `one_div_le_one_div_iff`);
  `mul_le_of_le_one_right (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a`; `le_div_self (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) : a ≤ a / b`.
- Comparing two sums termwise after `le_div_iff₀`: `Finset.mul_sum, Finset.mul_sum, Finset.sum_mul` then `Finset.sum_le_sum`; inside, isolate
  the core inequality `x / q * Q ≤ x` (`div_mul_eq_mul_div, div_le_iff₀`) as a `have` and finish with a two-line `calc` (`ring` to reassociate,
  `mul_le_mul_of_nonneg_left`). A bare `refine mul_le_mul_of_nonneg_right ?_ (by norm_num)` leaves an unassignable `0 ≤ ?m`.
- `h > 0` is not needed for the conjugation and trace identities (only `h aᵢ < 2` and `aᵢ > 0`); it is needed for the ordering statements
  (`0 ≤ h aᵢ`). The unused-variable linter flags the superfluous hypothesis.
### Separable tensors on `Fin d` and diagonal algebra (tide `separable-oneloop`)

- Contractions of a separable tensor (`if i = j ∧ j = k then α i else 0`) against a diagonal matrix: work entrywise (`ext i j`,
  `simp only [def, Matrix.of_apply, diagonal_apply]`), kill each summation index with
  `rw [Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]` (the off-index hypothesis comes as `k ≠ i`; the `if` reads
  `i = k`, hence `Ne.symm`), then `by_cases hij : i = j` with `subst`/`simp`. Four nested sums (the bubble) are four such rewrites.
- `diagonal_add : diagonal d₁ + diagonal d₂ = diagonal (d₁ + d₂)` and `diagonal_smul : diagonal (r • d) = r • diagonal d` point in
  opposite directions: to *collapse* a sum of scaled diagonals write `simp only [← diagonal_smul, diagonal_add]` — `← diagonal_add`
  instead *splits* a diagonal whose entries are sums (it will happily rewrite the right-hand side of your goal), after which `congr 1`
  pairs the wrong summands.
- `(t • diagonal λ)⁻¹`: `Matrix.inv_eq_right_inv`, rewrite `t • diagonal λ = diagonal (fun i => t * λ i)` by `← diagonal_smul; rfl`,
  `diagonal_mul_diagonal`, a `funext` identity via `mul_one_div_cancel`, `diagonal_one`.
- After `congr 1; funext i` on `diagonal f = diagonal g` the goal is already the real identity; a `simp only [Pi.add_apply]` there makes
  no progress (error). Use `simp only [Pi.smul_apply, smul_eq_mul]` only when a `•` is present.
- Positivity of a quadratic `g u² + 4αu + 12λ` under a discriminant hypothesis: multiply by `g`, complete the square
  (`g·q = (g u + 2α)² + (12λg − 4α²)`, by `ring`), `nlinarith [sq_nonneg _]`, and divide back with `pos_of_mul_pos_right h hg.le`.
  `λ > 0` is not needed once `g > 0` and `α² < 3λg` are given — the linter will tell you.
### Toeplitz sums and running means of the AR(1) chain (tide `autocorrelation-time`)

- Weighted geometric sums `∑_{m<N} (N − m − 1) ρ^{m+1}` whose summand mentions `N`: induct on `N`, `Finset.sum_range_succ`, then rewrite
  the old summands with a `∀ m ∈ range n, …` identity (`push_cast; ring`) and `Finset.sum_add_distrib`; the new geometric piece is
  `simp_rw [pow_succ]; rw [← Finset.sum_mul, geom_sum_eq hρ n]`. Close with `push_cast; field_simp; ring`.
- `field_simp` sometimes closes the goal and sometimes leaves a polynomial identity — the two `field_simp; ring` sites in one file went
  opposite ways. Check each one; a stray `ring` errors with "no goals", a missing one leaves the goal open.
- `field_simp` needs `h ≠ 0` and `p ≠ 0` separately, not `h * p ≠ 0` (`left_ne_zero_of_mul`, `right_ne_zero_of_mul`).
- A single chain through a `Fin C`-family lemma: instantiate `C := 1`, `fun _ : Fin 1 => η`, discharge `c = c'` by `Subsingleton.elim` and
  `simpa` the `if (0 : Fin 1) = 0 ∧ …` away.
- Zero-start chains have mean zero: induction with `integral_add (….integrable one_le_two).const_mul ρ) …` (the constant is an explicit
  argument of `Integrable.const_mul`).
- `L² · L²` is integrable: `(hf : MemLp f 2 P).integrable_mul (hg : MemLp g 2 P)`.
- `simp_rw [pow_add]` rewrites every `ρ ^ (a + b)`, including `ρ ^ (b + 1)` into `ρ ^ b * ρ ^ 1`; give the first arguments,
  `pow_add ρ (b + 1)`, to split only `ρ ^ (b + 1 + k)`. `geom_sum_le_one_div` states `≤ 1 / (1 - ρ)`; when the goal has
  `ρ ^ n / (1 - ρ)` rewrite it with `div_eq_mul_one_div` before `mul_le_mul_of_nonneg_left`.
- Limits along `ℕ`: `tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop : (N : ℝ)⁻¹ → 0`, `tendsto_pow_atTop_nhds_zero_of_lt_one`,
  `tendsto_const_div_atTop_nhds_zero_nat`, `squeeze_zero`; transfer an identity that needs `N ≠ 0` with
  `.congr' (eventually_atTop.mpr ⟨1, fun N hN => (heq N (by omega)).symm⟩)`.
- `ulaChain` needs `[DecidableEq ι]`; a section that mentions it without the instance fails with "failed to synthesize DecidableEq ι".

### Reversibility of the MH kernel (tide `mh-reversible`)

- Rectangle masses of `π ⊗ K`: restrict the outer integral (`∫⁻ x in A, …`) and reuse the invariance proof verbatim — `lintegral_add_left`,
  the `e1` rewrite of `π(x)·(∫⁻_B w)/Z` into `Z⁻¹ ∫⁻_B flux`, `lintegral_const_mul' _ _ hZinv` — all work on `μ.restrict A` unchanged; the
  Dirac part becomes `lintegral_indicator hB` then `Measure.restrict_restrict hB : (μ.restrict A).restrict B = μ.restrict (B ∩ A)` and
  `Set.inter_comm`.
- Tonelli on restricted measures: `lintegral_lintegral_swap` takes `⦃f⦄` strict-implicit and `[SFinite μ]`; inside `rw` the measures stay
  metavariables and the instance search gets stuck (`SFinite ?m`). State the swapped equation as a typed `have` and supply
  `(μ := μ.restrict A) (ν := μ.restrict B)` **and** `hFm.aemeasurable (μ := (μ.restrict A).prod (μ.restrict B))`, then `rw [hswap]`.
- `K(x, univ) = 1`: `simp only [mhKernelSet, Measure.restrict_univ, Set.indicator_univ]` then
  `exact add_tsub_cancel_of_le (mhAcceptMass_le_one hq hZ hZ0 hZtop x)` (the unfolded integral is defeq to `mhAcceptMass`).
- Restriction through a density: `restrict_withDensity hA : (μ.withDensity f).restrict A = (μ.restrict A).withDensity f` lives in the
  `MeasureTheory` namespace, not `Measure`.
- The step-size hypothesis `0 < h` is not needed for the MALA/pMALA reversibility instances (only for their Markov/probability statements):
  drop it or the linter flags it.
### Positive semidefiniteness and section instances (tide `batch-size-rule`)

- `Matrix.PosSemidef` and `posSemidef_sum`, `PosSemidef.smul`, `posSemidef_vecMulVec_self_star` need only `[Finite ι]` (the `Fintype`
  block in `PosDef.lean` starts later); `trace_nonneg` and anything with `Matrix.trace` need `[Fintype ι]`; `minibatchCov`/`ulaCov` need
  `[DecidableEq ι]` too. Put the three groups in three sections, or the `unusedFintypeInType`/`unusedDecidableInType` linters fire.
- A real outer product is PSD via `posSemidef_vecMulVec_self_star v` and `simpa` (`star v = v`). `PosSemidef.smul` takes the explicit
  `0 ≤ c`; prove `0 ≤ 1 − (m : ℝ)/n` with `rw [sub_nonneg, div_le_one hn']; exact_mod_cast hmn`, and `0 ≤ (n : ℝ) − 1` from `2 ≤ n` by
  `exact_mod_cast` + `linarith` before `positivity`.
- Rewriting two-sided bounds into another parametrisation: prove each side's algebraic identity as `e : A = B := by field_simp` (with the
  nonzero facts in context; no `ring` needed) and finish with `⟨e1 ▸ hlo, e2 ▸ hhi⟩`.
- Dropping a factor `0 ≤ 1 − m/n ≤ 1` from a bound: `div_le_div_of_nonneg_right _ (by positivity)` and `nlinarith
  [mul_le_mul_of_nonneg_left hfpc hK0]`; then clear denominators on both the hypothesis and the goal with `div_le_iff₀` and `nlinarith`.
### Weighted Chebyshev and re-weighted averages (tide `llc-sensitivity`)

- The weighted Chebyshev identity `∑ᵢⱼ vᵢvⱼ(rᵢ − rⱼ)(fᵢ − fⱼ) = 2((∑ v r f)(∑ v) − (∑ v r)(∑ v f))`: expand the summand by a
  `∀ i j, … = a i * b j - …` identity (`ring`), then `simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
  ← Finset.sum_mul]` and `ring`. Prove the identity as its own lemma and derive the inequality from a *covariance-condition* hypothesis
  `0 ≤ ∑∑ …`; the `Monovary`/`Antivary` versions are corollaries (`Antivary f r` is `Monovary (fun i => -f i) r`, then `mul_neg,
  Finset.sum_neg_distrib, neg_mul` and `linarith`).
- `Monovary f g : ∀ ⦃i j⦄, g i < g j → f i ≤ f j` (Mathlib, `Order/Monotone/Monovary`); the pairwise sign fact
  `0 ≤ (r i − r j)(f i − f j)` is `rcases lt_trichotomy` with `mul_nonneg_of_nonpos_of_nonpos` / `mul_nonneg`.
- Instantiating `weighted_mean_le_of_monovary` and then normalising the weights: `simp only [e1, e3, one_mul, one_div_mul_eq_div,
  Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at key` — write the per-term normalisations `e1 : 1/p * f = f/p`
  (`one_div_mul_eq_div`) and `e3 : 1/(p q) * p = 1/q` (`field_simp`) as `∀ i` facts. An `e2` for the three-factor product is never reached
  because simp fires `e3` first; the leftover `1/q * f` is `one_div_mul_eq_div`.
- `(½ ∑ a)/(½ ∑ b) = (∑ a)/(∑ b)`: `mul_div_mul_left _ _ (by norm_num : (1/2 : ℝ) ≠ 0)`.
- Traces of conjugated matrices: `rw [← trace_diagonal d, ← hconj, Matrix.trace_mul_cycle, hUU', Matrix.one_mul]` turns `tr M` into
  `tr (Uᵀ M U) = ∑ dᵢ` in one line once `hconj : Uᵀ M U = diagonal d` is available; when only the diagonal *entries* are known
  (`minibatchCov_conj_diag`), `unfold Matrix.trace Matrix.diag` and `Finset.sum_congr`.
- Frobenius norms do not obey the same comparison: a `1/p²`-weighted RMS is bounded by Chebyshev only by the uniform RMS, not the uniform
  mean (GPT counterexample `p = (1, 1.1)`, `h = 1.8`). Keep Frobenius claims out of trace theorems.

### Cauchy–Schwarz envelopes and abbreviations under binders (tide `frobenius-free`)

- `set a := fun i => … with ha` does **not** abbreviate occurrences under a `∑ i, …` binder (the summand `a i` mentions the bound variable, so
  `set` cannot abstract it); a subsequent `simp_rw [hterm]` written in terms of `a i` then "makes no progress", and the elaborator can emit a
  spurious "function expected" error. Write the per-term identity with the explicit expressions, and pass the abbreviation only as the
  argument of the abstract lemma (`sum_sum_ite_mul_le (fun i => …) (fun i j => …) …`); `calc`/`le_trans` match up to β.
- `sq_sum_le_card_mul_sum_sq (s := univ) (f := a) : (∑ a)² ≤ #univ * ∑ a²`, then `Finset.card_univ`; the double sum
  `∑ᵢⱼ (τ aᵢaⱼ + τ·[i=j] aᵢaⱼ)` collapses with a per-row `have` (`Finset.sum_add_distrib, ← Finset.mul_sum ×3, Finset.sum_ite_eq`) and
  `← Finset.sum_mul, sq` for `(∑ a)²`.
- `add_le_add_left h c : c + a ≤ c + b`?? No — in this Mathlib `add_le_add_left h a : b + a ≤ c + a` adds on the *right* and
  `add_le_add_right h a : a + b ≤ a + c` adds on the *left*; when the goal has the changing summand first, use `add_le_add_left`.
- `√(X / Y) = √X / √Y` is `Real.sqrt_div (hx : 0 ≤ X) Y`; the nonnegativity of an integral of a sum of squares is
  `integral_nonneg fun ω => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _`.
### Conjugating pooled estimators and Frobenius sums (tide `frobenius-bridge`)

- The outer-product identity `vecMulVec (Uᵀ *ᵥ x) (Uᵀ *ᵥ x) = Uᵀ * vecMulVec x x * U`: `ext i j; simp only [vecMulVec_apply, mulVec,
  dotProduct, Matrix.mul_apply, transpose_apply]; rw [Finset.sum_mul_sum, Finset.sum_comm]`, then `Finset.sum_mul` and `ring` per term.
  Use it, not a bare four-index sum shuffle, to conjugate a pooled second-moment matrix: define the raw estimator as a matrix
  (`(1/(CN)) • ∑ ∑ vecMulVec x x`) and push the conjugation through with `Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul`,
  reading entries with `Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul`.
- `EuclideanSpace` vectors are `WithLp 2 (ι → ℝ)`: the coordinate function is `v.ofLp`, and `⟨orthoCol hQ i, v⟩ = ((orthoOf hQ)ᵀ *ᵥ v.ofLp) i`
  after `EuclideanSpace.inner_eq_star_dotProduct, star_trivial`, `orthoCol, WithLp.ofLp_toLp, mulVec, dotProduct, transpose_apply` and a
  per-term `ring`.
- Orthogonal invariance of `∑ᵢⱼ Aᵢⱼ²`: go through `tr(AᵀA)` (`sum_mul_apply_eq_trace` with `sq`), reassociate the transposes
  (`transpose_mul, transpose_transpose`, `simp only [Matrix.mul_assoc]`, insert `U * Uᵀ = 1`), then `Matrix.trace_mul_cycle`. Only `U Uᵀ = 1`
  is needed; to use it with `U` and `Uᵀ` swapped, apply to `Uᵀ` and rewrite `transpose_transpose`.
- `pooledSecondMoment` needs no `Fintype`/`DecidableEq`/`MeasurableSpace`; `orthoCol`/`orthoOf` need `DecidableEq`; a lemma with no `P` in
  its statement must `omit [IsProbabilityMeasure P]`, one with no measure at all `omit [MeasurableSpace Ω]`.
- Integrability of raw entries: express them as finite linear combinations of the eigen entries (`pooledRaw_apply_eq_sum`) and use
  `integrable_finsetSum`/`.const_mul`/`.mul_const`; then `integral_finsetSum`, `integral_mul_const`, `integral_const_mul` commute the
  expectation. Never try to prove `L⁴` of the raw coordinates directly.

### Deterministic-target Frobenius identities and Matrix-valued estimators (tide `frobenius-target-raw`)

- `rw [integral_sum_sq_sub_eq _ _ h1 h2]` fails with "motive is not type correct … function expected `pooledRaw … ω a`" when `S i j ω`
  is an entry of a `Matrix`-valued estimator: the motive needs `Matrix ι ι ℝ` unfolded to a function type. State the identity once for a
  generic `S : ι → ι → Ω → ℝ` (`integral_sum_sq_sub_eq_centred`) and apply it with `refine (… _ _ h1 h2).trans ?_`; `_ _` are solved from
  `h1 : ∀ a a', Integrable (fun ω => pooledRaw … ω a a') P` by higher-order pattern unification, and `congr 1` then closes the centred term
  by `rfl` (no `beta_reduce` needed).
- `((U * diagonal (fun i => f i - t i) * Uᵀ) a a')` inside a `have` statement fails to elaborate ("Function expected … ?m") because the
  lambda's type is only fixed after the product; bind the matrix first with `set D : Matrix ι ι ℝ := diagonal (fun i => …) with hD` and
  write `(U * D * Uᵀ) a a'`. Finish with `rw [hc, hD, sum_sq_diagonal]`.
- Bias against a target `T = U diag(t) Uᵀ`: `∫ raw a a' − T a a' = (U * diagonal (s − t) * Uᵀ) a a'` by
  `rw [hmean, ← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]` after turning the matrix mean identity into an entry
  identity with `congrFun (congrFun hmean a) a'` and `rw [Matrix.of_apply] at this`.
- `Uᵀ A U = D` to `A = U D Uᵀ`: `rw [← hconj]; simp only [← Matrix.mul_assoc]; rw [hUU', Matrix.one_mul, Matrix.mul_assoc, hUU', Matrix.mul_one]`
  with `hUU' : U * Uᵀ = 1` (`ulaCov_eq_conj_diagonal`, `inv_eq_conj_diagonal`).
- `pow_le_pow_left` is gone; use `pow_le_pow_left₀ (ha : 0 ≤ a) (hab : a ≤ b) n`. `memLp_finset_sum` is deprecated for `memLp_finsetSum`.
- Geometric sums with a shifted exponent: rewrite each term `ρ ^ (2 * (b + 1 + k)) = ρ ^ (2 * (b + 1)) * (ρ ^ 2) ^ k` (`← pow_mul, ← pow_add`,
  `congr 1; ring`), then `← Finset.mul_sum, geom_sum_eq hρ, ← pow_mul` and `field_simp; ring` with `ρ ^ 2 - 1 ≠ 0` and `1 - ρ ^ 2 ≠ 0` both in
  context.
- `ula_variance_eq` (`2h/(1 − (1 − hp)²) = 1/(p(1 − hp/2))`) already exists in `ULAEigen.lean`; don't redeclare it.
- `lean-state check` times out (120 s) on a 380-line file whose imports were only just restored from the artifact cache; `lake build
  Laplace.Sampler.<Module>` (≈1 min once the import closure is cached) is the reliable per-file diagnostic in a fresh worktree.
### Spectrum-free envelopes and monotone factors (tide `burnin-envelope`)

- A per-direction term that is a product of monotone factors (here `2ρ^{2b}/(1−ρ)·(ρ/(1+ρ))²`): prove the factorisation as an equation
  (`field_simp; ring` after rewriting `1 − ρ² = (1−ρ)(1+ρ)`), prove each factor monotone (`pow_le_pow_left₀`, `div_le_div_of_nonneg_left`
  for the reciprocal — note `1 − ρ' ≤ 1 − ρ` reverses — and `div_le_div_iff₀` + `nlinarith` for `ρ/(1+ρ)`), and combine with nested
  `mul_le_mul` and `positivity` side goals. The unfactored denominator `(1−ρ²)(1+ρ)/2` is *not* monotone; do not try to bound it directly.
- Products of two factors that peak on *different* directions (autocorrelation on the flattest, step factor on the stiffest): bound each
  by its own maximum and multiply (`mul_le_mul hτ hstep …`) — a valid, if loose, spectrum-free statement. The `1/x²` factor's nonnegativity
  is `div_nonneg` with an explicit `0 < 1 − r²` from `nlinarith`; `positivity` cannot see the sign of `1 − (…)²`.
- Hypotheses that only guard denominators may be redundant: `excess_mono` needs no `0 ≤ x` (both denominators are positive from `x ≤ x' < 1`),
  and `burnin_term_eq` needs `−1 < ρ`, not `0 ≤ ρ`. The unused-variable linter finds these; supply the nonzero facts as *terms*
  (`(sub_pos.mpr h1).ne'`, `(neg_lt_iff_pos_add.mp h0).ne'` after `rw [add_comm]`) when a `linarith` would hide the reference.
- `pmin ≤ pmax` does not follow from `∀ i, pmin ≤ p i ≤ pmax` when `ι` may be empty; take it as a hypothesis in the algebraic lemmas and
  derive it from `[Nonempty ι]` (`Classical.arbitrary ι`) where the instance is available.
- Square-root algebra `2√X/d = √Y/q`: go through `√((2/d)²) · √X = √((2/d)² X)` with `Real.sqrt_sq` and `(Real.sqrt_mul (hx : 0 ≤ a) _).symm`
  — give `Real.sqrt_mul` its first argument with a type ascription, otherwise `rw` splits the wrong square root — and a `field_simp`
  identity between the radicands.
### Relative chart arc (RelativeChartLeading, RelativeChartFamily)

- A stuck `IsFiniteMeasureOnCompacts ?μ` (from `integrableOn_const`, `IsCompact.measure_lt_top`,
  `Continuous.integrable_of_hasCompactSupport`) means nothing fixed the measure: pass
  `(μ := (volume : Measure (ℝ × EuclidD n)))` explicitly.
- `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with `(s := Set.univ) Filter.univ_mem` when the
  bound is global; the derivative-bound binder order is `∀ᵐ y, ∀ s ∈ univ, ‖F' s y‖ ≤ bound y`.
- A sum of `if p i then f i else 0` over `univ`: `Finset.sum_ite, Finset.sum_const_zero, add_zero`
  turns it into the sum over `univ.filter p`; combine with `tendsto_finsetSum` for termwise limits.
- `HasCompactSupport fun y ↦ χ (0, y)` from `HasCompactSupport χ`: `IsCompact.of_isClosed_subset`
  of `Prod.snd '' tsupport χ` with `closure_minimal`.

### Monotone bias terms and intermediate-value arguments (tide `stepsize-tradeoff`)

- Monotonicity of a rational-in-`h` bias term without calculus: prove the *termwise* inequality after `div_le_div_iff₀`, splitting
  `x ^ (2m) = x ^ (2m−1) * x` (`rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * m)]`) so that `mul_le_mul` combines a power
  inequality (`pow_le_pow_left₀`) with a linear one (`nlinarith`). Then lift to the sum with `Finset.sum_le_sum` and
  `mul_le_mul_of_nonneg_left`.
- `ring` treats `(p * (1 − u/2))⁻¹` as an atom and will not split it into `p⁻¹ * (1 − u/2)⁻¹`: rewrite with `← one_div_mul_one_div`
  (`1 / a * (1 / b) = 1 / (a * b)`) first, then `simp only [Finset.mul_sum]` and per-term `ring`.
- Sign change ⇒ zero: put the sign-carrying numerator in its own polynomial `def` (`balanceGap`), prove `Continuous` with
  `(continuous_mul_const p).sub (continuous_const.mul (… (continuous_finsetSum _ fun k _ => by fun_prop)))`, and use
  `intermediate_value_Ioo (hab) hf.continuousOn h0 : Ioo (f a) (f b) ⊆ f '' Ioo a b` — the membership `0 ∈ Ioo (f 0) (f b)` is two `norm_num`
  goals after rewriting the endpoint values. Uniqueness: `StrictMonoOn.injOn` with `Set.Ioo_subset_Icc_self`. `StrictMonoOn f s` unfolds to
  `∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b → f a < f b`, so `intro h hh h' hh' hlt` is the whole setup.
- `∃! h, h ∈ s ∧ P h ∧ Q h ∧ R h`: `refine ⟨h₀, ⟨hmem, ?_, ?_, ?_⟩, fun h ⟨hmem', hz', _, _⟩ => ?_⟩`.
- Endpoint values of the zero-start factor: at `h = 0`, `simp [zeroStartFactor, hN']` with `hN' : (N:ℝ) ≠ 0` (the sum of `1` over
  `range N` is `N`); at `h = 1/p`, `simp only [zeroStartFactor, one_div_mul_cancel hp.ne', sub_self]` then
  `Finset.sum_eq_zero fun k _ => zero_pow (by omega)`.
- Sign transfer through a positive denominator: `div_neg_of_neg_of_pos`, `div_pos`, and `div_eq_zero_iff` (then discharge the
  denominator case with `absurd … (mul_pos …).ne'`).
- Deprecations in this Mathlib: `continuous_mul_right → continuous_mul_const`, `continuous_finset_sum → continuous_finsetSum`.
- The unused-variable linter fires on hypotheses that `linarith`/`nlinarith` did not need (`0 ≤ h` when `h ≤ h'` and `0 ≤ h'` suffice);
  drop them from the statement rather than underscore them.

### Eigenvector quadratic forms and single-direction perturbations (tide `direction-readings`)

- `Π` is a reserved token (dependent-function binder); never name a matrix `Π`. Use `M`.
- Eigenvector algebra with `mulVec`: `P⁻¹ *ᵥ s = p⁻¹ • s` from `P *ᵥ s = p • s` via
  `calc P⁻¹ *ᵥ s = p⁻¹ • (P⁻¹ *ᵥ (P *ᵥ s))` (`rw [hs, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hp, one_smul]`) and
  `Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP.det_pos.ne'), Matrix.one_mulVec`. The row version
  `s ᵥ* P⁻¹` is `← Matrix.mulVec_transpose, Matrix.transpose_nonsing_inv, hPt`.
- `Matrix.dotProduct_mulVec : v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w` rewrites the *first* `⬝ᵥ … *ᵥ` it meets, which may be on the other side of the
  equation; isolate the intended instance in a `have h3 : s ⬝ᵥ (P⁻¹ *ᵥ (M *ᵥ s)) = …` and rewrite with `h3`.
- Expanding `(A + B * M * C) *ᵥ s`: `Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec` (twice), then `Matrix.mulVec_smul`,
  `dotProduct_smul`, `smul_eq_mul`, and `ring` handles `p⁻¹ * (p⁻¹ * x) = x / p ^ 2`.
- A unit column of `orthoOf`: `(orthoCol hQ i).ofLp ⬝ᵥ (orthoCol hQ i).ofLp = 1` is the `(i, i)` entry of `orthoOf_transpose_mul`:
  `congrFun (congrFun … i) i`, `rw [Matrix.mul_apply, Matrix.one_apply_eq] at h`, `simpa [orthoCol, dotProduct, transpose_apply] using h`.
- `tr(P U D Uᵀ) = ∑ pᵢ dᵢ`: `rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc,
  orthoOf_transpose_mul_mul hP.1, diagonal_mul_diagonal, trace_diagonal]`.
- `Pi.single i₀ a i` needs its codomain: write `(Pi.single i₀ a : ι → ℝ) i` in statements (needs `[DecidableEq ι]`); sums over it
  collapse with `Finset.sum_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)` then `simp`.
- `Finset.single_le_sum (f := fun i => …) (fun i _ => by positivity) (Finset.mem_univ i₀)` for `f i₀ ≤ ∑ f`;
  `Finset.sum_mul_sq_le_sq_mul_sq _ _ _` is Cauchy–Schwarz `(∑ f g)² ≤ (∑ f²)(∑ g²)`; `Finset.sum_sq_le_sq_sum_of_nonneg` gives
  `∑ f² ≤ (∑ f)²` for nonnegative `f`.
- `positivity` cannot use `pmin ≤ p i` to see `0 < p i`; give `(one_div_pos.mpr (lt_of_lt_of_le hpmin (hmin i))).le` explicitly.
- `field_simp` closed every ratio identity of this file on its own (`(½ (p a))/(d/2) = a p / d`, `a²/(1/pmin)² = (a pmin)²`); a trailing `ring`
  errors with "No goals".

### Separable Gibbs measures and moment-route limits (tide `separable-exact`)

- `integral_fintype_prod_volume_eq_prod (f := fun i x => …)` (`∫ ∏ᵢ fᵢ(wᵢ) = ∏ᵢ ∫ fᵢ`) has no integrability hypothesis, so the
  factorisation of the Gibbs expectation of a product observable, `(∏ Nᵢ)/(∏ Zᵢ) = ∏ (Nᵢ/Zᵢ)` (`Finset.prod_div_distrib`), holds with no
  hypotheses at all; only the *coordinate* reduction `⟨φ(wᵢ₀)⟩ = ⟨φ⟩_{ℓᵢ₀}` needs `Zᵢ ≠ 0` for the spectators (`div_self`). Derive coordinate
  and pair statements from the product one with `fun i x => if i = i₀ then φ x else 1` (`Finset.prod_ite_eq'` on the observable side,
  `Finset.prod_eq_single` on the expectation side) and `if k = i ∨ k = j then x else 1` with `Finset.prod_eq_mul i j hij`.
- An `if` used only inside a proof still needs `Decidable`: start the proof with `classical` rather than adding `[DecidableEq ι]` to the
  statement (the linter flags the unused instance). Theorems whose *statement* has `if i = j` keep `[DecidableEq ι]` explicitly.
- `Integrable.congr`/`integral_congr_ae` goals against `h.add h'` are stated with Pi addition `(f + g) x`; add `Pi.add_apply` to the
  `simp only` before `ring`. For `← integral_add` the integrability witnesses must be `have`s with explicit lambda types, otherwise the
  `(f + g) a` pattern does not match the beta-reduced integrand. Cleanest: prove the numerator identity `∫ ℓ e = ∫ (c₂ x²e + c₃ x³e) + c₄ x⁴e`
  by `integral_congr_ae` + `ring`, then `rw [hnum, integral_add h23 …, integral_add …, integral_const_mul ×3]` forwards and finish with `ring`.
- `0 < ∫ exp(−tℓ)`: `MeasureTheory.integral_exp_pos (hf : Integrable (fun x => rexp (f x)))` after `unfold partitionFunction`.
- `xᵐ e^{−tℓ}` integrable from `|x|ᵐ e^{−tℓ}` (`integrable_abs_pow_mul_exp_neg_t_anharmonic`) via `.mono'` with continuity
  (`unfold anharmonicPotential; fun_prop`) and `rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`.
- Limits: `t²f → c ⇒ tf → 0` is `tendsto_inv_atTop_zero.mul h` then `congr'` with `field_simp` (needs `t ≠ 0` in context). From an explicit rate
  `|t²M − c − C/t| ≤ K/(t√t)` to `t²M → c`: `tendsto_iff_norm_sub_tendsto_zero`, `squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _)`
  (not `squeeze_zero_norm'`, which double-wraps the norm), bound `(|C| + K)/t` via `tendsto_const_nhds.div_atTop tendsto_id`,
  `abs_sub_abs_le_abs_sub`, `Real.one_le_sqrt`, `le_mul_of_one_le_right`.
- `Integrable.fintype_prod (f := fun j x => …) hf` gives integrability of `∏ⱼ fⱼ(wⱼ)` on `ι → ℝ`; pick `fⱼ = (if j = i then ℓⱼ else 1) · e^{−tℓⱼ}`
  to cover one coordinate energy times the whole Boltzmann factor.
- `field_simp` closed the ratio identities of this file except one with literal zeros (`lam/2 * (1/lam) + α/6 * 0 + … = 1/2`), which needed a
  trailing `ring`; check each.

### Frame changes of Gibbs measures (tide `gibbs-rotation`)

- `(1 : Matrix ι ι ℝ)` needs `[DecidableEq ι]`; a section whose statements contain `Qᵀ * Q = 1` must carry it in `variable`, and the lemmas
  that don't mention `1` (`affineFrame_apply`, continuity facts) take `omit [DecidableEq ι] in`.
- `|det Q| = 1` from `Qᵀ Q = 1`: `congrArg Matrix.det hQ`, `rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this` gives
  `det * det = 1`; then `rw [← Real.sqrt_sq_eq_abs, sq, h, Real.sqrt_one]`.
- Change of variables for `w ↦ Qᵀ(w − c)`: `integral_sub_right_eq_self (fun w => g (Qᵀ *ᵥ w)) c` (Lebesgue on `ι → ℝ` is add-right-invariant,
  instance found automatically) then `integral_comp_mulVec Qᵀ hdet g hg : ∫ g = |Qᵀ.det| * ∫ g (Qᵀ *ᵥ v)` — rewriting with it replaces the
  *right-hand* `∫ g` of the goal, after which `det_transpose, abs_det_of_orthogonal, one_mul` close it.
- Frame-independence of `gibbsExpectation`/`gibbsCov`: the identities are between totalised integrals, so only `AEStronglyMeasurable` of the
  weighted integrands is needed (`(by fun_prop : Continuous fun u => φ u * Real.exp (-(t * L u))).aestronglyMeasurable` in the continuity
  wrappers). Coordinate observables are `continuous_apply i`.
- `Filter.Tendsto.congr' … (Eventually.of_forall fun t => ?_)` leaves the goal with an unreduced `(fun t => …) t`; `rw` cannot see through it,
  `simp only [h]` beta-reduces first and closes the goal.
- A def built from a `noncomputable` def (`rotatedAnharmonic := rotated Q c (separableAnharmonic …)`) must itself be `noncomputable def`.
- `simp only [separableAnharmonic, separablePotential]` flags `separablePotential` unused when the occurrence is unapplied
  (`Continuous (separablePotential ℓ)`); `continuous_finsetSum _ fun i _ => ?_` unifies through the definition anyway.

### Bilinearity of Gibbs moments and ambient coordinates (tide `ambient-moments`)

- `Integrable.add` and `Integrable.const_mul` state their conclusions with Pi arithmetic (`(f + g) w`, `fun x => c * f x`); a `.congr
  (Eventually.of_forall fun w => by simp only [Pi.add_apply]; ring)` brings them to the shape a later lemma expects. Always state the
  intermediate integrability facts as `have h : Integrable (fun w => <exact shape>) := …congr …` — an anonymous `.congr` inside a bigger term
  leaves its target as an unresolved metavariable (`?m j i w`).
- `integrable_finsetSum _ fun i _ => …` does not infer the `Finset`; write `integrable_finsetSum Finset.univ fun i _ => …`.
- Products of sums: `simp only [Finset.sum_mul, Finset.mul_sum]` normalises `(∑ f)(∑ g) e` to `∑ ∑ f g e` but may leave the two summation
  orders swapped; finish with `exact Finset.sum_comm`.
- `Q * Qᵀ = 1` from `Qᵀ * Q = 1`: the generic `mul_eq_one_comm.mp hQ` (Dedekind-finite monoid instance for matrices); there is no
  `Matrix.mul_eq_one_comm` in this Mathlib.
- A `rw` with a bilinear covariance lemma whose observables were left as `_` picks them up from the *first* integrability argument; if the goal
  has `Cov[a + φ, b + ψ]` and the lemma was instantiated with `ψ` from `hψ : Integrable (ψ e)`, the pattern will not be found. State both
  observables, or use a two-sided lemma (`gibbsCov_const_add_both`).
- The `Fintype` sum `∑ k, u k ^ (Pi.single i 1 : ι → ℕ) k = u i` is `Finset.prod_eq_single i (fun k _ hk => by simp [hk]) (by simp)` then
  `simp`; `Pi.single i 1 + Pi.single j 1` covers `u i * u j` including `i = j` (`Pi.add_apply, pow_add, Finset.prod_mul_distrib`). Under a
  `.congr` the goal is a beta-redex: `change (∏ k, u k ^ (Pi.single i 1 + Pi.single j 1 : ι → ℕ) k) * _ = _` before `rw`.
- `show` that changes the goal is linted; use `change`.
- Lemmas from another namespace (`Laplace.Sampler.sum_sq_conj`, `sum_sq_diagonal`) need the full name inside `Laplace.Multi`.
- `field_simp` closed the final Frobenius ratio identity and the per-term `hnum`/`hden` identities on its own; the trailing `ring`s errored.
### Combining explicit rate bounds (tide `var-order2-rate`)

- Rates of the form `∃ K T, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t}, T ≤ t → |…| ≤ K/(t√t)` combine with `refine ⟨K₂ + …, max T₁ T₂, by positivity,
  le_max_of_le_left hT₁, fun {t} ht => ?_⟩`; recover `1 ≤ t` via `hT₁.trans ((le_max_left _ _).trans ht)` and the two component bounds via
  `h₂ ((le_max_right _ _).trans ht)`.
- A difference of products against a square of a rate: `(tM)² − m₀² = (tM − m₀)(tM + m₀)`, `|tM + m₀| ≤ |tM − m₀| + 2|m₀|` (write
  `tM + m₀ = (tM − m₀) + 2m₀` with `ring_nf` inside the `calc`, then `abs_add_le`, `abs_mul`, `abs_two`), and `K₁/t ≤ K₁` from `div_le_self`.
  Downgrade `1/t²` to `1/(t√t)` with `div_le_div_of_nonneg_left … (mul_le_mul_of_nonneg_left hst htpos.le)` where `hst : √t ≤ t` comes from
  `Real.sqrt_le_sqrt (by nlinarith)` and `Real.sqrt_sq`.
- To eliminate `Real.sqrt lam` from a coefficient identity: `set s := Real.sqrt lam with hsdef; clear_value s; subst hs` with
  `hs : s ^ 2 = lam` (after `Real.sq_sqrt`), then `field_simp; ring` in the variable `s`.
- `div_div : a / b / c = a / (b * c)` aligns `C/t` with a bound stated as `…/(lam * t)`.
- `Matrix` transpose notation `ᵀ` is scoped: a file that states `Qᵀ * Q = 1` must `open Matrix`; otherwise "unexpected token 'ᵀ'".
- `abs_sub (a b) : |a − b| ≤ |a| + |b|` (the triangle inequality for a difference) — note the name.

### Dominated convergence for the rescaled moment integrals (tide `moments-all-orders`)

- `tendsto_integral_filter_of_dominated_convergence (bound) hF_meas h_bound bound_integrable h_lim` on `atTop : Filter ℝ` works with
  `filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht` for the two eventual hypotheses; the bound is `|u| ^ n * exp (-(c₀ * u ^ 2))`
  from `rescaled_boltzmann_decay` (the seabed's `t`-uniform Gaussian domination of the *whole* Boltzmann factor) and
  `integrable_abs_pow_mul_exp_neg_mul_sq`. Measurability: `Continuous.aestronglyMeasurable` after `unfold rescaledPerturbation cubicScale
  quarticScale; fun_prop` with `0 < Real.sqrt t` in context.
- Pointwise limits through `exp`: `Filter.Tendsto.neg` produces `𝓝 (-0)`; `rw [neg_zero] at h0` *before* composing with
  `Real.continuous_exp.tendsto 0`, then `rw [Real.exp_zero]`.
- `Real.tendsto_sqrt_atTop` exists; `tendsto_const_nhds.div_atTop` gives `c/√t → 0` and `c/t → 0`; `Tendsto.const_mul_atTop hr` scales a
  divergent function.
- `√(λt)^n ⟨xⁿ⟩ = J_n/J_0`: unfold `gibbsExpectation partitionFunction J_n`, `simp only [pow_zero, one_mul, zero_add, pow_one] at h0 ⊢`
  (to match `I_n_J_n_relation` at `n = 0`), then `rw [← hn, ← h0, pow_succ]; field_simp` with `Z ≠ 0` (`integral_exp_pos`) and
  `√(λt) ≠ 0` in context.
- `Nat.doubleFactorial` numerals: `norm_num [Nat.doubleFactorial] at h` evaluates `(2 * 3 - 1)‼` to `15`.
- `Filter.Tendsto.div hf hg (hb : b ≠ 0)` produces a Pi-division function; `congr'` against `fun t => f t / g t` is accepted by defeq.

### Covariances of monomials and the one-dimensional covK (tide `covK-anharmonic`)

- `Tendsto.congr' (Eventually.of_forall fun t => ?_)` leaves `(fun t => …) t` beta-redexes on the right; `rw` cannot instantiate a
  metavariable with the bound `t`, so rewrite with `simp only [lemma, show (2 + 2 : ℕ) = 4 from rfl]` and finish with `ring`. The same
  applies to pointwise goals under `Integrable.congr`: `simp only [pow_add]`, `simp only [pow_one]; ring`, not `rw`.
- `gibbsCov L t (fun x => x ^ m) (fun x => x ^ n) = ⟨x^(m+n)⟩ − ⟨x^m⟩⟨x^n⟩`: `unfold gibbsCov; rw [funext-identity for x^m * x^n]`; the
  literal `m + n` must then be normalised (`show (3 + 2 : ℕ) = 5 from rfl`) before `ring` can match `⟨x^5⟩` from the moment lemmas.
- Products of moments: `t²⟨x³⟩⟨x²⟩ = (t²⟨x³⟩)·⟨x²⟩` with `⟨x²⟩ → 0` from `t⟨x²⟩ → 1/λ` via `tendsto_zero_of_tendsto_pow_mul`; the pair
  `(3, 1)` has total degree four and needs the refined `t²⟨x³⟩ → −5α/(2λ³)`, not a degree count.
- The 1D bilinearity lemmas (`Laplace.gibbsCov_add_left/right`, `gibbsCov_smul_left/right`) want integrability in exactly the shapes
  `φ e`, `φ ψ e` (left) / `ψ e`, `φ ψ e` (right); build them from `Laplace.Multi.integrable_pow_mul_exp_neg_t_anharmonic k` with
  `.const_mul` and `.congr (… by ring)`. To expand the energy observable use
  `have e1 : (fun x => L x) = fun x => (a x² + b x³) + c x⁴ := by funext x; simp only [hL, anharmonicPotential]` (already closed, no
  `ring`) and `calc … := by rw [← e1]` — eta unifies `fun x => L x` with `L`.
- `field_simp` sometimes leaves a goal with literal zeros (`(6 + lam*alpha*0)*24 + … = 6*24`) that needs `ring`, and sometimes closes the
  goal (then `ring` errors "no goals"); check each occurrence.

### Separable covK, off-diagonal probes and the full quadratic probe (tide `covK-separable`)

- Coordinate independence under `separablePotential ℓ` needs no integrability: `gibbsExpectation_prod_separable` with the observable
  `fun m x => if m = i then f x else if m = j then g x else 1` and `Finset.prod_eq_mul i j hij` (two coordinates) or
  `Finset.mul_prod_erase … i` followed by `prod_eq_mul j k` (three coordinates). The repeated-coordinate case of
  `Cov_L[f(uᵢ), g(uⱼ)]` is handled by combining `f·g` on the single coordinate, not by encoding repeats in the product.
- `gibbsCov_coord_fun_separable` returns `if i = j then … else 0`; use `Finset.sum_eq_single i (fun k _ hk => if_neg hk) …` (for
  `if k = i`) or `Finset.sum_eq_add i j hij` (two survivors) to collapse the coordinate sum.
- Rewriting `Laplace.gibbsCov … (fun x => x ^ 1)` against a goal containing `fun x => x` fails (`pow_one` is not applied inside the
  pattern): instantiate the lemma at `m = 1`, `simp only [pow_one] at h`, then `rw [h]`.
- Mixed monomials `uₖ^a uᵢ uⱼ e^{−tL}`: `integrable_monomial_separableAnharmonic (Pi.single k a + Pi.single i 1 + Pi.single j 1)` and
  `change (∏ n, u n ^ (… : ι → ℕ) n) * _ = _; simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pow_single_pow, pow_one]`.
- A finite sum of coordinate energies against a general observable: `integrable_finsetSum Finset.univ` then
  `simp only [separableAnharmonic, separablePotential, Finset.sum_mul]` closes the pointwise goal (unfolding inside the exponential is
  harmless because both sides unfold identically).
- Double sums over `ι` are best flattened to `∑ p : ι × ι` before `gibbsCov_finsetSum_left`: `congr 1; exact
  (Fintype.sum_prod_type' fun a c => …).symm` (explicit function, `rw` cannot match the higher-order pattern); go back with
  `rw [Fintype.sum_prod_type]` and `simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Annotate
  `(Finset.univ : Finset (ι × ι))` when the index type is not otherwise determined.
- State `tendsto_finsetSum … |>.add …` with an explicit beta-reduced `Tendsto (fun t => ∑ …) …` type; otherwise the `congr'` goal
  carries `(fun t => …) t` redexes that `ring` treats as atoms.

### Fourth-order remainder, parity, and `t⁻²` moment rates (tide `order3-parity`)

- The quartic-order layer mirrors `IntegralRemainder2` but is simpler: `|s_t|⁴` is even, so `(x + y)⁴ ≤ 8(x⁴ + y⁴)` (proved by
  `nlinarith [mul_nonneg (sq_nonneg (x - y)) h7]` with `h7 : 0 ≤ 7x² + 10xy + 7y²`) plus `u¹⁶/t⁴ ≤ u¹⁶/t²` gives the envelope
  `8(A⁴ + B⁴)(u¹² + u¹⁶)/t²` with no odd absolute powers to absorb. `abs_expRemainder_le_max 4` needs
  `(Nat.factorial 4 : ℝ) = 24` by `norm_num [Nat.factorial]`; `expRemainder 4 s` unfolds with
  `simp only [expRemainder, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; push_cast; ring`.
- `J_n_asymptotic_order3` avoids a ten-term integrand identity: split `J_n = ∫ f·P₃ + ∫ f·(e^{-s} − P₃)` and `∫ f·P₃ = ∫ f·P₂ − ∫ f·s³/6`
  with `rw [← integral_add h₁ h₂]; congr 1; funext u; ring` (lambda-typed integrability, never `Integrable.sub`'s Pi form), then reuse
  `quadratised_integral_decomposition` and a four-term `cubed_integral_decomposition`. Integrability of `f·P₂` comes for free from
  `integrable_J_n`, the remainder's integrability (`integrable_remainder4`, from `Integrable.mono'` and `fun_prop`) and the cubed part.
- Parity corollaries: state them for `n = 2 * k` / `2 * k + 1`; odd Gaussian moments are `integral_pow_mul_exp_neg_sq_odd (k + j)` after
  `rwa [show 2 * (k + j) + 1 = 2 * k + m by ring] at h'`; exponents such as `2 * k + 1 + 3` must be renormalised with
  `rw [show 2 * k + 1 + 3 = 2 * k + 4 by ring] at h` before `simpa only [mul_zero, zero_sub, sub_zero, add_zero]`. With literal indices
  (`J_n … 0`, `2`, `3`) the seabed's `exact` trick works: `∫ u ^ (2 + 3) …` is defeq to `∫ u ^ (2 * 2 + 1) …`.
- `rw [← h]` fails with "did not find pattern" when `h : … = J_n … 3 t` and the goal shows a `set` variable `J3`: `kabstract` filters
  candidate subterms by head symbol before trying defeq, so a let-variable never matches a constant-headed pattern. Obtain `h` *before*
  the `set` (which then folds `h` too), or `rw [← hJ3] at h`.
- Conversely `rw [abs_div]` *does* see through `set p := a / c` and rewrites `|p|` to `|a| / |c|`; pass explicit arguments
  (`abs_div q t`) to pin the occurrence.
- The two ratio lemmas (`ratio_rate_order2`, `ratio_rate_order1`) replace the inline `1/t` cancellation of `MomentSecondOrder`: prove
  `X/Y − p − q/t = (e_X − (p + q/t)e_Y − qd/t²)/Y` by `rw [hp, hq]; field_simp; ring`, bound the numerator with `abs_sub`/`abs_add_le`,
  and divide by `c/2 ≤ Y` via `div_le_div_of_nonneg_left`. Downstream, `rw [hpc, hq'] at hratio` rewrites the constant too, so the
  `refine ⟨K, …⟩` constant must be written in the rewritten form (`|(1 : ℝ)|`, `|c₂|`, …).
- `√λ` in a coefficient identity: `set s := Real.sqrt lam; have hs : lam = s ^ 2 := (Real.sq_sqrt hlam.le).symm; clear_value s; subst hs`
  at the top of the proof makes everything rational in `s` (`Real.sqrt (s ^ 2 * t) = s * √t` by `Real.sqrt_mul, Real.sqrt_sq`). For
  `√t` identities use `linear_combination e * Real.mul_self_sqrt ht.le` and read `e` off the residual `ring` prints.
- `gcongr` on `K/(t√t)/t ≤ K/t²` produces the wrong side goal (`K/(t√t) ≤ K`); prove such steps by hand: `rw [div_div]` then
  `div_le_div_of_nonneg_left hK (by positivity) (by calc t ^ 2 = t * 1 * t := by ring; _ ≤ t * √t * t := by gcongr)`.
- `field_simp` closes the `2 / c * N / t ^ 2 = (N / t ^ 2) / (c / 2)`-type goals outright (a trailing `ring` errors "no goals").

### Tensor contractions of the rotated oscillator and matrix-form E7 (tide `e7-matrix`)

- Every one-loop contraction of the rotated tensors `Tᵢⱼₖ = ∑ₗ αₗ Qᵢₗ Qⱼₗ Qₖₗ`, `Q4 = ∑ₗ γₗ Q⊗⁴` against `S = Q diag(s) Qᵀ` reduces to
  `contract_conj_diagonal : ∑ₖₘ Qₖₚ Sₖₘ Qₘ_q = if p = q then s p else 0`, proved as the `(p, q)` entry of `Qᵀ S Q = diag s` (`set S`
  first so `Matrix.mul_apply` does not unfold `S`, then `Finset.sum_comm`). Prove the contractions for arbitrary `s` and substitute
  `s = 1/(λt)` only in `oneLoopCov_rot`.
- A contraction lemma stated with `M : Fin d → Fin d → ℝ` cannot be `rw`-applied to a `Matrix`-valued `S k l` ("target is not type
  correct under `implicit` transparency … function expected"): `Matrix` is not unfolded when unifying `?M k l`. Instantiate by hand,
  `have h := rotQ_contract Q gamma i j (fun k l => (Q * diagonal s * Qᵀ) k l); rw [h]` (the inferred type is beta-reduced).
- Reordering nested sums: `sum_comm3 (f) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c` (two `Finset.sum_comm`s) and then
  `rw [sum_comm3]` (higher-order pattern `?f a b c` unifies). Never `simp only [Finset.mul_sum, Finset.sum_mul]` on a *product of
  two sums*: `mul_sum` also fires on `(∑ m, a m) * (∑ n, b n)` (as `b * ∑`) and the resulting nesting order is unpredictable, so the
  sides no longer line up under `Finset.sum_congr`. Distribute by hand instead: `rw [Finset.sum_mul_sum]` for `(∑)(∑)`, and for a
  scalar times a nested sum state the pointwise `Finset.mul_sum` as a `have e : ∀ k l, c * ∑ q, F = ∑ q, c * F` and `simp_rw [e]`.
- `rw [conj_smul]` rewrites all instances with the same scalar and diagonal at once: `bubble_rot` and `tadpoleLine_rot` give
  syntactically identical matrices, so `(t²/2) • X + (t²/2) • X` needs one `conj_smul`, not two.
- `(Q * diagonal (fun i => …) * Qᵀ) j k` in a `have` statement can fail with "function expected … has type ?m": the `HMul` instance is
  still pending when the application is elaborated. Ascribe `(… : Matrix (Fin d) (Fin d) ℝ) j k`.
- The multi-dimensional `gibbsCov (separableAnharmonic …) t (fun u => u i) (fun u => u i)` and the one-dimensional
  `Laplace.gibbsCov (anharmonicPotential (lam i) …) t id id` are equal by `gibbsCov_separableAnharmonic … i i` with `if_pos rfl`;
  convert the scalar rate hypothesis with `rw [← hVe] at e` before using it against a `set V`.
- `(t • (Q * diagonal lam * Qᵀ))⁻¹`: `Matrix.inv_eq_right_inv`, then `Matrix.smul_mul`, `conj_mul_conj`, `diagonal_mul_diagonal`,
  `conj_smul` (which is `← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul`) and `diagonal_one`.
- `Filter.eventually_atTop.mp (hlim.eventually (lt_mem_nhds (half_lt_self hpos)))` turns `Tendsto f atTop (𝓝 L)` with `0 < L` into
  `∃ T, ∀ t ≥ T, L/2 < f t`; then `div_le_iff₀` and `nlinarith` give the `c/t²` lower bound.

### eq:mean and eq:covK in matrix form (tide `e2-matrix`)

- Vector transport under an orthogonal `Q`: `(Q diag s Qᵀ) *ᵥ (Q *ᵥ v) = Q *ᵥ (s * v)` is `Matrix.mulVec_mulVec`, `Matrix.mul_assoc`,
  `hQ`, `Matrix.mul_one`, `← Matrix.mulVec_mulVec` and `Matrix.mulVec_diagonal`; `(Q v) ⬝ᵥ (Q w) = v ⬝ᵥ w` is `Matrix.dotProduct_mulVec`,
  `← Matrix.vecMul_transpose`, `Matrix.vecMul_vecMul`, `hQ`, `Matrix.vecMul_one`; `b ⬝ᵥ (Q v) = (Qᵀ b) ⬝ᵥ v` is
  `Matrix.dotProduct_mulVec` + `Matrix.mulVec_transpose`. Rewrite `S *ᵥ b` into `Q *ᵥ (…)` *before* `S` is unfolded, and unfold
  `Matrix.mulVec, dotProduct` into sums only at the very end.
- `tr(HSBS)`: `Matrix.trace_mul_cycle` (`trace (A * B * C) = trace (C * A * B)`) moves the last `S` to the front so the seabed's
  `SHS = Q diag(1/(λt²)) Qᵀ` identity applies; a second `trace_mul_cycle` and `simp only [Matrix.trace, Matrix.diag_apply,
  Matrix.mul_diagonal]` finish. Order the rewrites `trace_HSBS_rot, SHS_rot, smul_conj_diagonal_inv` (the `S H S` pattern must be
  matched while `S` still reads `(t • H)⁻¹`).
- `w − c = Q *ᵥ affineFrame Q c w` by `unfold affineFrame; rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]`; substitute it on the
  left only (`conv_lhs => rw [hwc]`) since the right-hand side also mentions `w − c` through `affineFrame`.
- Combining `½∑A + ½∑B − (t/2)∑C − (t/2)∑D` into one sum: `Finset.mul_sum` four times, then `← Finset.sum_add_distrib` *before* the two
  `← Finset.sum_sub_distrib` (the subtraction pattern needs a plain sum on its left), then `Finset.sum_div` and a per-index `field_simp`.
- `mul_sub` inside `Tendsto.congr'` goals picks the first product-of-difference it sees (here on the wrong side); state the needed
  `(Q *ᵥ (fun i => m i / t)) j = (∑ i, Q j i * m i) / t` as a `have` and let `field_simp` close the scalar identity.
- `field_simp` closed every coefficient identity of this file outright; a trailing `ring` is an error ("no goals").
- A duplicate definition in the same namespace (`Laplace.Multi.meanShift` already lived in `HessianRoute`) passes the *module* build and
  fails only at the root `lake build` ("import … failed, environment already contains …"). Before defining a note-level functional,
  `grep -rn "def <name>" Laplace/` and reuse the existing one (its shape may differ: `HessianRoute.meanShift` keeps the `t •` inside).

### All-orders sharp moments (tide `moments-sharp`)

- Shifted Gaussian moments: wrap `integral_pow_mul_exp_neg_sq_half` once as `gaussian_moment_shift k j : m (2k + 2j) = (2k + 2j − 1)‼ √(2π)`
  and specialise with `rwa [show 2 * k + 2 * 2 = 2 * k + 4 by ring, show 2 * k + 4 - 1 = 2 * k + 3 by omega] at h'`; `omega` is the
  tool for the truncated `− 1`. Keep `(2k+3)‼`, `(2k+5)‼` opaque casts; `norm_num [Nat.doubleFactorial]` evaluates them at literal `k`.
- General-`k` bridges: `sqrt_pow_mul_moment_eq … (2 * k)` then `rw [pow_mul, Real.sq_sqrt …, mul_pow] at hmom` gives
  `lam ^ k * t ^ k * E = J_{2k}/J₀`; for odd `2k+1` substitute `lam = s ^ 2` (`set s := Real.sqrt lam; … clear_value s; subst hs`),
  rewrite `√(s² t) = s √t`, and close the bridge with `conv_lhs => rw [← hsq2]` (`hsq2 : √t ^ 2 = t`) followed by `ring`, which
  handles the symbolic exponents `(√t ^ 2) ^ (k + 1) = √t * √t ^ (2k + 1)` and `s ^ 3 * s ^ (2k + 1) = (s ^ 2) ^ (k + 2)`.
- After `rw [hDc, hCk'] at hratio` the `refine ⟨K, …⟩` constant must be written in the rewritten form (`|D|`, `|Ck|`, `|Ck * (c * q₀)|`).
- `squeeze_zero'` needs its bound function pinned: `have hK0 : Tendsto (fun t : ℝ => K / t) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id` first, then `squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hK0` after
  `rw [tendsto_iff_norm_sub_tendsto_zero]`.
- `field_simp` closes some `√t`-cancellation goals and leaves others (`(√t J + …) * t * 6 = …`) for `ring`; check each.

### eq:covK with a rate (tide `covK-rate`)

- Rates compose pointwise: `rate_mul` (`|XY − ab| ≤ (K|b| + K'|a| + KK')/t` from `XY − ab = (X−a)b + a(Y−b) + (X−a)(Y−b)` and
  `t⁻² ≤ t⁻¹`), `rate_bounded` (`|X| ≤ |a| + K`), `bounded_div`. Package all normalised moments once with a *common* threshold
  (`Z_rates`: `T := T₁ + … + T₆`, each `Tᵢ ≤ t` by `linarith`) and then the six pair covariances (`pair_cov_rates`); downstream theorems
  destructure the package instead of juggling six thresholds.
- `simpa [Nat.doubleFactorial] using h` converts the general-`k` moment theorems at literal `k` (`t ^ 1 → t`, `x ^ (2 * 1) → x ^ 2`,
  `(2 * 3 − 1)‼ → 15`, `1 / lam → lam⁻¹` on both sides); the odd constant then reads `alpha * 105 / (6 * lam ^ 4)` — state the packaged
  bound in that literal form rather than the simplified fraction.
- `t² Cov[xᵐ, xⁿ]` in normalised moments: `rw [gibbsCov_pow_pow …, eq_div_iff htne]; simp only [show (3 + 2 : ℕ) = 5 from rfl, ← hM5, …]; ring`
  (`ring` will not cancel a `/ t` by itself; `eq_div_iff` first). For `x ^ 1` first `simp only [pow_one, show (2 + 1 : ℕ) = 3 from rfl] at h`.
- `rw [abs_mul, abs_mul, abs_mul]` on a three-term sum picks up the wrong products (`|t ^ 2 * C|` inside a summand); give the first
  argument, `abs_mul (lam / 2)`, `abs_mul (alpha / 6)`, `abs_mul (gamma / 24)`.
- `positivity` cannot see `0 ≤ K p` for a `choose`-obtained family; write `Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (hK p)`.
- Pulling `t²` into a sum of sums for a rate: prove `∑ p, t² * (c p * X p) = ∑ p, c p * (t² * X p)` by `Finset.sum_congr … ring` first,
  then `simp only [mul_sub, Finset.sum_sub_distrib]` and `ring` on the four sum-atoms; `← Finset.sum_sub_distrib` does not fire on
  `(∑ + ∑) − (∑ + ∑)`.
- The tide-49 constant `-alpha i / (2 * lam i ^ 2)` is `(-alpha i) / …`; a hypothesis in `+ alpha i / …` form needs `rw [neg_div,
  sub_neg_eq_add]` on the goal before `exact`.
- A full `lake build` can carry a warning from *another* session's freshly landed file (here `Laplace/Multi/RelativeChartFamily.lean:4`);
  the landing loop ignores warnings, so filter the finish script's warning check to the files of the tide.

### Taylor identity and coordinate derivatives of the rotated oscillator (tide `tensor-identification`)

- `set u := … with hu` variables are *transparent to `rw`*: `kabstract` unfolds let-values, so `Finset.sum_mul_sum` matched `u p * u p`
  through the abbreviation and rewrote inside every summand. After `set`, `clear_value u` and keep `hup : ∀ p, ∑ i, Q i p * v i = u p`
  (`by rw [hu]`) for the two or three places where the definition is needed. A "typeclass instance problem is stuck" on a following
  `Finset.sum_congr` is the symptom of such an unintended rewrite.
- Never `simp only [Finset.mul_sum]` on goals containing products of two sums: `mul_sum` also fires on `(∑ …) * (∑ …)`. Distribute the
  scalar with a per-index `have e : ∀ i, c * ∑ p, F = ∑ p, c * F`, `simp_rw [e]`, then `Finset.sum_comm`/`sum_comm3`.
- One-variable chain rule along a coordinate line: `HasDerivAt (fun s => ∑ l, g l (a l + s * b l)) (∑ l, gp l * b l) 0` from
  `((hasDerivAt_id' (x := 0)).mul_const (b l)).const_add (a l)`, `HasDerivAt.comp (0 : ℝ)`, `HasDerivAt.sum` and
  `.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Finset.sum_apply])` (the sum lemma produces the Pi-sum of functions).
  `affineFrame Q c (w + s • Pi.single k 1) = fun l => affineFrame Q c w l + s * Q k l` via `add_sub_right_comm, Matrix.mulVec_add,
  Matrix.mulVec_smul, Matrix.mulVec_single_one` and `rfl` for `Qᵀ.col k l = Q k l`.
- Explicit polynomial derivatives: build `HasDerivAt` with `(hasDerivAt_pow n x).const_mul c`, `hasDerivAt_id' (x := x)`,
  `hasDerivAt_const x c`, `.add`, then `rw [e]` where `e` states the target value in the raw form `c * ((n : ℝ) * x ^ (n - 1))`
  (`simp only [def]; norm_num; ring`) and `exact h` (the function unfolds by defeq).
- Nested `partialD`: compute each level for *all* `w` as `fun w => ∑ l, A l * g l (affineFrame Q c w l)` (rewrite the previous level into
  this shape with `funext w; rw [prev]; exact Finset.sum_congr rfl fun l _ => by ring`), then apply the one-step lemma; evaluate at the
  centre only at the end (`affineFrame_center`, `simp`).

### The energy to two loops (tide `llc-two-loop`)

- Splitting a sum of differences on *one side only*: `rw [Finset.sum_sub_distrib]` rewrites the first match, which may be a coefficient
  sum `∑ (a − b)` on the *other* side. Use `conv_rhs => rw [Finset.sum_sub_distrib, …, Finset.sum_const, Finset.card_univ,
  nsmul_eq_mul, ← Finset.sum_div]` and finish with `ring` on identical sum-atoms.
- `field_simp` then `ring` on an identity containing `∑ i, (5α²/(24λ³) − γ/(8λ²))` fails: `field_simp` rewrites *inside* the summand
  on one side. `set C := ∑ …; clear_value C` first, so the sum is an atom.
- Frobenius pairing in the eigenframe: `∑ᵢⱼ Aᵢⱼ Bᵢⱼ = (Aᵀ * B).trace` by `simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
  transpose_apply]; exact Finset.sum_comm`; then `conj_mul_conj`, `diagonal_mul_diagonal`, `Matrix.trace_mul_cycle`, `hQ`,
  `Matrix.one_mul`, `trace_diagonal`. Symmetry of `Q diag a Qᵀ`: `rw [transpose_mul, transpose_mul, transpose_transpose,
  diagonal_transpose, Matrix.mul_assoc]`.
- Concrete tensors on `Fin 2` via `![![![0, 1], ![1, 0]], ![![1, 0], ![0, 0]]]`: `simp [defs, Fin.sum_univ_two, Matrix.one_apply,
  Matrix.mulVec, dotProduct]` then `ring` evaluates six-fold sums (64 terms) without trouble.
- `energy_anharmonic_order1_rate_sharp` and `anharmonicPotential` live in `Laplace.Multi`/`Laplace.OneD`: `open … Laplace.OneD` is
  needed for the bare name `anharmonicPotential`.

### Rosenbrock: the series terminates (tide `rosenbrock-terminating`)

- Exact Rosenbrock expectations of polynomials of `z`-degree above four: `gibbsExpectation_valley_poly'` (any `Fin n → Fin m`
  coefficient matrix, a verbatim copy of the `Fin 5` proof) with `harmonicMoment_vec7` (`⟨z⁶⟩ = 15/(λt)³` from
  `gibbsExpectation_harmonic_pow_even … 3` and `norm_num [Nat.doubleFactorial]`). Generate the coefficient table with sympy
  (`sp.Poly(expr, z, u).terms()`), paste as `![![…], …]`, and close the identity `φ p = ∑ᵢⱼ cᵢⱼ zⁱ uʲ` by
  `simp only [defs, Fin.sum_univ_seven, Fin.sum_univ_five, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; simp; ring`
  (35 symbolic coefficients, seconds).
- `(H * S * B * S).trace` with concrete `2 × 2` `H`, `S` and symbolic `B`: plain `simp` stops at `vecMul` forms
  (`(![t⁻¹, 0] ᵥ* (B * !![…])) 0`); use `simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.mulVec,
  dotProduct, Fin.sum_univ_two, defs, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
  Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]` then `field_simp; ring`.
- `field_simp` closes some of the `12a/t³`-type identities and not others (`dumbbell` needed `ring`, `figureEight` did not); the
  "No goals" error line points at the theorem *after* the one whose `ring` is redundant when several are adjacent — check line
  numbers against the file, not against the last edit.
- Namespace clash: `Laplace.TwoD.gibbsExpectation`/`gibbsCov` (on `ℝ × ℝ`) versus `Laplace.Multi.gibbsExpectation` (on `ι → ℝ`)
  when working in `Laplace.Multi` with `open Laplace.TwoD`; write `Laplace.TwoD.gibbsExpectation` explicitly in statements.

### Frame covariance of the tensor formulas (tide `frame-covariance`)

- Six-index contractions (the bubble) are best handled at the *matrix* level: `frob X Y := (Xᵀ * Y).trace` with
  `frob_apply : frob X Y = ∑ᵢⱼ Xᵢⱼ Yᵢⱼ`, bilinearity by `simp only [frob, Matrix.transpose_sum, Matrix.transpose_smul,
  Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]`, the slice
  `slice T i := of fun k l => T i k l`, `slice (rotateT Q T) i = ∑ a, Q i a • (Q * slice T a * Qᵀ)` (one index proof), and
  `bubble T S i j = frob (slice T i) (S * slice T j * Sᵀ)` (one index proof). The rotated bubble is then
  `simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, frob_sum_left, frob_sum_right, frob_smul_left,
  frob_smul_right]`, the conjugation identity, `frob_conj`, then `Finset.mul_sum`, `Finset.sum_comm`, `ring`.
- `(t • (Q * H * Qᵀ))⁻¹ = Q * (t • H)⁻¹ * Qᵀ` unconditionally: `rw [← Matrix.smul_mul, ← Matrix.mul_smul]` (note the direction:
  `Matrix.smul_mul : a • M * N = a • (M * N)`), `Matrix.mul_inv_rev` twice, `Matrix.inv_eq_left_inv hQ : Q⁻¹ = Qᵀ`,
  `Matrix.inv_eq_right_inv hQ : (Qᵀ)⁻¹ = Q`.
- `Q * S * Qᵀ *ᵥ v` parses as `Q * S * (Qᵀ *ᵥ v)` (`*ᵥ` binds tighter than `*`): parenthesise `(Q * S * Qᵀ) *ᵥ v`.
- `Matrix.mul_assoc` bare in `rw` picks the first associable product (it re-associated the trace factor instead of the intended
  `… * Qᵀ * Q`); give the left factor: `Matrix.mul_assoc (Q * S)`. For `Qᵀ * Q` cancellations inside `mulVec` chains prefer
  `simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one]` (it also closes the goal).
- `(Q *ᵥ w) j = ∑ b, Q j b * w b` is `rfl`; `Matrix.sum_mulVec`, `Matrix.smul_mulVec` (not `smul_mulVec_assoc`) distribute sums
  and scalars through `*ᵥ`.
- After `rw [hS]` has replaced `(t • H')⁻¹` everywhere, a lemma stated in terms of `(t • H')⁻¹` (like `conj_SHS`) no longer matches;
  order the rewrites, or state the helper in the post-rewrite form.
- Diagonal tensors as `if`s: put the *innermost* summation index's condition outermost, `diagT α a b c := if c = a then (if b = a
  then α a else 0) else 0`, so `simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]` collapses the sums
  from the inside out (with the other order `Finset.sum_ite_eq'` never fires).
### The rotated tensors as Fréchet derivatives (tide `frechet-bridge`)

- Directional derivative along `eᵢ` = Fréchet derivative on `eᵢ`: `HasFDerivAt.comp_hasDerivAt (l := f) (f := fun s => w + s • eᵢ)
  (x := 0)` with the line's `HasDerivAt` from `((hasDerivAt_id' (x := 0)).smul_const eᵢ).const_add w` (`simpa`) and the base
  point aligned by `rw [hw]` (`hw : w + (0 : ℝ) • eᵢ = w`, `simp`); finish with `.deriv`.
- One rung of the `partialD`/`iteratedFDeriv` ladder: `fderiv_continuousMultilinear_apply_const_apply (hdiff x) m eᵢ` turns
  `fderiv (fun y => iteratedFDeriv n f y m) x eᵢ` into `fderiv (iteratedFDeriv n f) x eᵢ m`, and `iteratedFDeriv_succ_apply_left`
  (reversed) with `Fin.cons_zero`, `Fin.tail_cons` gives `iteratedFDeriv (n+1) f x (Fin.cons eᵢ m)`. Differentiability of
  `iteratedFDeriv n f` from `hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)` for `hf : ContDiff ℝ (n+1) f`.
  `![a, b] = Fin.cons a ![b]` definitionally, so the tower theorems state `![…]` and `exact` the rung lemma.
- Smoothness of polynomial potentials: `contDiff_apply ℝ ℝ i` (both type arguments explicit), `ContDiff.sum fun i _ => …` (not
  `contDiff_finset_sum`), `contDiff_pi.2` for vector-valued maps; `Matrix.mulVec` has no `fun_prop` theorems, so rewrite
  `affineFrame Q c = fun w i => ∑ j, Qᵀ i j * (w j - c j)` first. `unfold separablePotential` on a `∑` exposes `Multiset.map`
  junk; use `change ContDiff ℝ n fun w => ∑ i, …` instead.
- `fderiv f c = 0` from vanishing coordinate derivatives: `ext v`, `hv : v = ∑ k, v k • Pi.single k 1` (`funext j; simp
  [Finset.sum_apply, Pi.single_apply]`), `rw [hv, map_sum]`, `simp only [map_smul, _root_.zero_apply]`
  (`ContinuousLinearMap.zero_apply` is deprecated), `Finset.sum_eq_zero`, then `← partialD_eq_fderiv`.
- Finish-script hygiene: `sed 's#Laplace.Multi.X#…#g'` also rewrites the *path* `Laplace/Multi/X` (dots match slashes), which
  broke tide 57's `git add`; write file paths in the finish script by hand.

### `a² < 3` keeps the minimum unique (tide `unique-minimum`)

- Sign facts about a polynomial with parameters: prove a *denominator-cleared square identity* by `ring` (`24γ q(x) = (γx + 2α)² +
  4(3λγ − α²)`, `2γ ℓ''(x) = (γx + α)² + (2λγ − α²)`), then `nlinarith [sq_nonneg …]` for the sign of the product, then cancel the
  positive factor with `(mul_pos_iff_of_pos_left (by positivity)).mp` or `nonneg_of_mul_nonneg_right h (by positivity)`. One big
  `nlinarith` on the quartic is unreliable.
- Mathlib's quadratic formula: `discrim a b c := b^2 − 4*a*c`; `quadratic_eq_zero_iff (ha : a ≠ 0) (h : discrim a b c = s * s) x :
  a * (x * x) + b * x + c = 0 ↔ x = (-b + s)/(2a) ∨ x = (-b − s)/(2a)` and `discrim_eq_sq_of_quadratic_eq_zero (h : a * (x * x) + b
  * x + c = 0) : discrim a b c = (2ax + b)^2` — both want the shape `a * (x * x)`, not `a * x * x`; factor `ℓ'` as
  `x * (γ/6 * (x * x) + α/2 * x + λ)` accordingly. `s = √D` with `Real.mul_self_sqrt hD0 : √D * √D = D`.
- `Function.ne_iff : f ≠ g ↔ ∃ a, f a ≠ g a` turns `affineFrame Q c w ≠ 0` into a coordinate witness for `Finset.sum_pos'`.
- Positive definiteness of `Q * diagonal lam * Qᵀ`: `Matrix.PosDef.conjTranspose_mul_mul_same (PosDef.diagonal hlam) hinj` with
  `hinj : Function.Injective Qᵀ.mulVec` (from `Q * Qᵀ = 1`), then `rwa [Matrix.conjTranspose_eq_transpose_of_trivial,
  Matrix.transpose_transpose] at this`.

### The localised anharmonic mean (tide `localised-mean-1d`)

- Bounded reweighting of a Gibbs measure: `⟨x⟩_loc = ⟨xφ⟩_t/⟨φ⟩_t` with `φ = exp(g x₀ x − (g/2)x²) ≤ e^{g x₀²/2}`; integrability of
  `x^m φ e^{−tℓ}` is `Integrable.bdd_mul (c := …) hcont.aestronglyMeasurable (Eventually.of_forall …)` (the bound is an
  `∀ᵐ`, not an `∃ C`), followed by `.congr` with `change … = _` (not `show`, which the style linter rejects) and `ring`.
- `|e^y − 1 − y| ≤ (e^M + 2) y²` for all `y ≤ M`: split on `|y| ≤ 1` (`Real.abs_exp_sub_one_sub_id_le`) versus `|y| > 1`
  (`|y| ≤ y²`, then `abs_sub`, `abs_add_le`, `nlinarith`).
- Odd absolute moments from even ones: Young with a free weight `|x|³ ≤ (ε x² + x⁴/ε)/2` (`key : 2ε|x|³ ≤ ε²x² + x⁴` via
  `(ε|x| − x²)² ≥ 0` and `sq_abs`), then `ε = 1/√t` gives `⟨|x|³⟩ ≤ K/(t√t)`. Clear `√t` with `hsq : √t ^ 2 = t`
  (`Real.sq_sqrt`) and `linear_combination (C * t) * hsq` after `div_eq_div_iff`; `rw [← hss]` on `√t * √t = t` also rewrites
  the `t` inside `√t` and leaves `√(√t^2)` junk.
- `positivity` proves `0 ≤ x ^ (2 * k)` only after `rw [pow_mul]`; literal even exponents are fine.
- `evenMoment_anharmonic_rate … 1` normalises with `simpa [Nat.doubleFactorial] using h ht` (`t ^ 1`, `x ^ (2 * 1)`,
  `↑(2 * 1 − 1)‼` all disappear; the target may then carry `lam⁻¹`, which `simpa` also normalises).
- Section variables and `omit`: `omit hlam hgamma hdisc in` must precede the docstring, not sit between it and `theorem`; a
  lemma so omitted is called without those arguments.
- `abs_mul` in `rw` picks the first product it sees (`|g * x₀|` splits into `|g| * |x₀|`): give the factors, `abs_mul (g * x₀)`,
  `abs_mul t`. Likewise `abs_sub_comm 1 D`. `gcongr` often closes the resulting goals by `assumption` — a trailing `· exact` then
  errors with "No goals".
- Ratio-of-expectations rate: for `D → 1` with `|D − 1| ≤ K_D/t`, take `T ≥ 2K_D` so `D ≥ 1/2` (`abs_le.mp`), write
  `t N/D − c = ((tN − c) + c(1 − D))/D` (`field_simp; ring` with `hDne : D ≠ 0` in context), then `div_le_iff₀` and one `gcongr`
  against `1/2 ≤ D`.
### The temperature derivative in `d` dimensions (tide `covK-derivative-multi`)

- The dominated-differentiation proof of `d/ds ∫ψe^{−sL} = −∫Lψe^{−sL}` is dimension-free: state it for `L ψ : (ι → ℝ) → ℝ`
  continuous with `L ≥ 0`, bound `‖L ψ e^{−(t/2)L}‖` (`Integrable.norm` of the given integrability), region `Set.Ioi (t/2)`, and
  `Integrable (ψ e^{−tL})` from `Integrable.mono' hint0.norm hmeas (Eventually.of_forall hbound)` with `hmeas` and `hbound` stated as
  separate `have`s (inline they hit "typeclass instance problem is stuck").
- Inside the `?_` bullets of a big `refine`/`have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le …` term, give
  `norm_nonneg (L u * ψ u)` and `norm_mul (L u * ψ u)` their arguments: bare `_` elaborates before the goal is known, and a bare
  `rw [norm_mul, norm_mul]` splits `‖L u * ψ u‖` on one side only.
- `gibbsExpectation_add_of_integrable` and `gibbsExpectation_const_mul` (AmbientMoments) take `L t` *explicitly*; use
  `(L := …) (t := …)` named arguments before the `_ _ h1 h2`. `integrable_finsetSum` needs its `Finset` given (`Finset.univ`), or the
  `congr` side goal keeps a metavariable finset.
- `∑ i, ∑ j, f i j = ∑ p : ι × ι, f p.1 p.2` is `← Fintype.sum_prod_type'` (the primed lemma is stated left-to-right as the product
  sum). Annotate `fun (p : ι × ι) _ => …` in `HasDerivAt.sum (u := Finset.univ)` or `p.1` fails to elaborate.
- `integrable_exp_separableAnharmonic` already exists (AmbientMoments); grep before naming.
### The localised resolvent and eq:covK with `γ` (tide `covK-derivative-loc`)

- Differentiating `S(s) = (sH + γ1)⁻¹` needs no matrix norm: the resolvent identity `S(s) − S(t) = −(s − t) • (S(s) H S(t))`
  (algebra with `Matrix.nonsing_inv_mul`/`mul_nonsing_inv`, association by `simp only [Matrix.mul_sub, Matrix.sub_mul,
  Matrix.mul_assoc]`), continuity of `S` through `Matrix.inv_def` + `Ring.inverse_eq_inv'` with `Continuous.matrix_det`,
  `Continuous.matrix_adjugate`, `ContinuousAt.inv₀` (`isUnit_iff_ne_zero`), eventual invertibility from `ContinuousAt.eventually_ne`,
  and the entrywise derivative by `hasDerivAt_iff_tendsto_slope`, `slope_def_field`, `filter_upwards [self_mem_nhdsWithin,
  nhdsWithin_le_nhds hev]`, `Tendsto.congr'` and `ContinuousAt.tendsto.mono_left nhdsWithin_le_nhds`. Entry continuity of a matrix
  product: `((continuous_apply j).comp (continuous_apply i)).comp ((continuous_id.matrix_mul continuous_const).matrix_mul
  continuous_const)`.
- `HasDerivAt.sum` yields a Pi-sum of functions; fix the function with `(h.congr_of_eventuallyEq (Eventually.of_forall fun s => by
  simp [defs, Finset.sum_apply, Pi.mul_apply]))` and the value with `.congr_deriv`. Apply `const_mul` *before* `congr_of_eventuallyEq`
  when the target function is not syntactically a product (`b ⬝ᵥ meanShiftLoc s`), otherwise unification fails.
- Assemble scalar derivatives with matrix-form values (`−(B * R).trace`, `b ⬝ᵥ (R *ᵥ C)`) and prove the sum identities separately
  (`meanShift_deriv_sum`: `rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]; exact
  Finset.sum_congr rfl fun k _ => by ring`), so the final step is `simp only [def]; ring` on atoms. Unfolding `Matrix.mul_apply`
  globally expands the products inside the atoms on one side only.
- `set R := … with hR` variables are *not* substituted into later-unfolded definitions; `rw [← hDv, ← hR, ← hC, ← hS]` in that order
  (longest expressions first) or, better, avoid `set` and keep the full expressions.
- Symmetry transport: `(locS γ H s)ᵀ = locS γ H s` from `Hᵀ = H` via `Matrix.transpose_nonsing_inv` and `congr 1; simp [locPrec,
  Matrix.transpose_add, Matrix.transpose_smul, hH]`; `(S *ᵥ b) ⬝ᵥ v = b ⬝ᵥ (S *ᵥ v)` by `rw [dotProduct_mulVec_eq, hS]`;
  `tr(H S B S) = tr(B S H S)` by re-associating to `(H*S)*(B*S)` and `Matrix.trace_mul_comm`.
### E1/E5 numbers (tide `e1-numbers`)

- Numerical corollaries with decimal literals (`1.5`, `1.9`) are `norm_num` one-liners; interval bounds like
  `|½(4/3 + 1/(1 − 1/(4κ))) − 7/6| ≤ 10⁻⁴` for `κ ≥ 2500` go through `div_le_div_iff₀`/`le_div_iff₀` for the two bounds on the
  flat factor and `abs_le` + `nlinarith` (with the bounds as hypotheses).
- `ula_llc` with `Fin 2` eigenvalues given by `hp0 : eigenvalues 0 = p`, `hp1 : eigenvalues 1 = p/κ`: discharge the `∀ i, h * pᵢ < 2`
  side condition by `fin_cases i <;> simp [hp0, hp1, hhp, hhpκ]` and expand with `Fin.sum_univ_two`.
### eq:covK as a temperature derivative (tide `covK-derivative`)

- `convert h using 1` on `HasDerivAt` goals splits into *instance* goals (`Real.instAddCommGroup = Real.normedAddCommGroup.
  toAddCommGroup`, `Semiring.toModule = …`) whenever the derivative was built by the field API (`hasDerivAt_inv`, `HasDerivAt.exp`)
  and the target states the derivative over the normed group; use `h.congr_deriv (by ring)` / `refine h.congr_deriv ?_` (and
  `HasDerivAt.congr_of_eventuallyEq` for the function), never `convert`.
- `HasDerivAt.div` produces the *function* `f / g` (Pi division); `refine h.congr_deriv ?_` still unifies with `fun s => f s / g s`.
- `field_simp` rewrites *inside integrals* (`exp (-(t * ℓ x))` became `exp (-(ℓ x * t))` on one side only, so `ring` saw two atoms).
  `set N := ∫ … with hN; …; clear_value N Z LN LZ` before `field_simp` keeps the integrals opaque.
- `(fun s => x ^ k * exp (-(s * c)))` has derivative `(((hasDerivAt_id' (x := s)).mul_const c).neg.exp).const_mul (x ^ k)`; its
  stated value carries `(-fun y => y * c) s`, so `congr_deriv (by simp only [Pi.neg_apply]; ring)`.
- Dominated differentiation in the temperature: `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := …) (F' := …)
  (bound := …) (x₀ := t) (s := Set.Ioi (t / 2)) (Ioi_mem_nhds …)`, then `hF_meas` by `Eventually.of_forall` + continuity
  `.aestronglyMeasurable`, `hF_int` from `integrable_pow_mul_exp_neg_t_anharmonic`, the bound via `Real.exp_le_exp` with `ℓ ≥ 0`
  (`anharmonicPotential_nonneg`) and `ℓ ≤ λ/2|x|² + |α|/6|x|³ + γ/24|x|⁴`; the result's second component has `∫ -(…)`, so
  `rw [integral_neg] at key` first. `Laplace.OneD.integrable_abs_pow_mul_exp_neg_t_anharmonic` (namespace!) supplies the bound's
  integrability.
- `smul_inv_of_isUnit : (s • H)⁻¹ = s⁻¹ • H⁻¹` by `Matrix.inv_eq_right_inv` and `Matrix.mul_nonsing_inv H hH`; then
  `simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, contractT_smul,
  smul_dotProduct, dotProduct_smul, smul_eq_mul, Matrix.mul_nonsing_inv H hH, Matrix.nonsing_inv_mul H hH, Matrix.one_mul]` reduces
  every `(t • H)⁻¹` expression to scalars times `H⁻¹`-constants.

### The localised mean in `d` dimensions (tide `localised-mean-multi`)

- Orthogonal frame change preserves sums of squares: `(Qᵀ *ᵥ v) ⬝ᵥ (Qᵀ *ᵥ v) = v ⬝ᵥ v` by
  `rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hQQ, one_mulVec]` with `hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ`,
  then `simpa [dotProduct, sq]` for the `∑ (…)^2` form. `affineFrame Q c w − affineFrame Q c w₀ = Qᵀ *ᵥ (w − w₀)` is
  `rw [← Pi.sub_apply …, ← mulVec_sub, sub_sub_sub_cancel_right]`.
- A `t`-dependent potential `L + (g/(2t))|w − w₀|²` keeps the seabed's `gibbsExpectation L t` API usable for the localised measure
  `e^{−tL − (g/2)|w−w₀|²}`; `congr 1` on `exp` then `field_simp; ring` (with `t ≠ 0`) for the identification. When the potential
  is a lambda, unfold `gibbsExpectation` with `simp only [...]` (beta-reduces) rather than `unfold`, and rewrite pointwise with
  `simp only [lemma]` — `rw` does not see through the `(fun x => …) x` redexes.
- Integrability under a nonnegative extra term in the exponent: `Integrable.mono' hint.norm hmeas (Eventually.of_forall …)` with
  `Real.exp_le_exp.mpr` and `nlinarith [mul_nonneg ht.le h0]`; measurability from continuity via
  `Continuous.aestronglyMeasurable (by fun_prop)` with the potential's continuity as a named hypothesis in context (give `(L := …)
  (φ := …)` explicitly so the expected type is known before `fun_prop` runs).
- Section-variable hygiene: put `[DecidableEq ι]` on the theorems that need `1 : Matrix ι ι ℝ` rather than in `variable`; otherwise
  every matrix-free lemma gets an `unusedSectionVars`/`unusedDecidableInType` warning that the finish script treats as fatal.
- Resolvent on E2's tensors: `locPrec g (Q D Qᵀ) t = Q diag(tλ + g) Qᵀ` via `← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul`
  (then `rfl` for `t • lam = fun i => t * lam i`), `← smul_one_eq_diagonal`, `← Matrix.add_mul, ← Matrix.mul_add, diagonal_add`;
  then `Matrix.inv_eq_right_inv` with `conj_mul_conj hQ, diagonal_mul_diagonal` and `diagonal_one`. `meanShiftLoc_rot` is
  `meanShift_rot` with `1/(tλᵢ + g)` in place of `1/(λᵢt)`.
- Finite sums of rates: `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_sum`, `Finset.sum_div`; threshold `1 + ∑ Tᵢ` with
  `Finset.single_le_sum`. `(Q *ᵥ x) j` opens with `simp only [Matrix.mulVec, dotProduct]`; combine with `mul_sub,
  Finset.sum_sub_distrib` and `ring`.

### eq:mean's `O(S²)` remainder on the localised measure (tide `localised-mean-sharp`)

- Taylor remainders of `exp` on an interval: `Real.exp_bound (hx : |x| ≤ 1) (hn : 0 < n) : |exp x − ∑ m ∈ range n, x^m/m!| ≤
  |x|^n * ((n+1)/(n!·n))`; rewrite the sum with `simp [Finset.sum_range_succ, Nat.factorial]; ring` *as a separate equation*
  and bound the constant with `norm_num [Nat.factorial]` — do not `norm_num at h`, it reshapes the polynomial. For `|x| > 1` bound
  every lower power by `|x|^n` (`one_le_pow₀`, `nlinarith`). Result: `|e^y − 1 − y − y²/2| ≤ (e^M + 3)|y|³` for all `y ≤ M`.
- Odd absolute powers without `t`: `|x|⁵ ≤ (x⁴ + x⁶)/2`, `|x|⁷ ≤ (x⁶ + x⁸)/2` from `sq_nonneg (|x|^2 − |x|^3)`,
  `sq_nonneg (|x|^3 − |x|^4)`; rewrite even powers as `|x|^n` first (`rw [← abs_pow, abs_of_nonneg (by positivity)]`) so the final
  `nlinarith` sees one atom. Keep the signed odd moment (`oddMoment_anharmonic_rate`) for `⟨x³⟩`; converting `|X + a| ≤ K/t` to
  `rate_bounded`'s `|X − (−a)|` is `rw [sub_neg_eq_add]`.
- `abs_mul` in `rw` is greedy in *both* directions: `abs_mul t` also splits `|t * M₃|` inside another factor — give both
  arguments, `abs_mul t (N − …)`. `add_le_add_right` has the summand on the left in this Mathlib; use
  `add_le_add h le_rfl` for `A + D ≤ B + D`.
- `oddMoment_anharmonic_rate … 1` carries `t ^ (1 + 1)`, `x ^ (2 * 1 + 1)`, `(2 * 1 + 3)‼`: normalise with
  `simp only [show (2 * 1 + 1 : ℕ) = 3 from rfl, show (1 + 1 : ℕ) = 2 from rfl, show (2 * 1 + 3 : ℕ) = 5 from rfl] at h`
  (rules with the *full* literal expression as LHS; a rule for `2 * 1` alone would pre-empt them) and leave `((5 : ℕ)‼ : ℝ)`
  symbolic in the constant.
- Many thresholds: `T := T₁ + … + T₈` with every `Tᵢ ≥ 1` makes each `Tᵢ ≤ t` a one-line `linarith`, cheaper than nested `max`.

### eq:cov with the localiser (tide `localised-cov`)

- `open scoped Nat` turns `φ` into Euler's totient: a named argument `(φ := …)` then fails to parse ("unexpected token ':='")
  and the error blames a `ℕ → ℕ`. Do not open `Nat` in files that name observables `φ`; `Nat.doubleFactorial` as a simp lemma
  needs no notation.
- Constant names are global in `Laplace.Multi`: `locC₂` already existed (tide 65); grep before naming (`locQ₄/locQ₆/locQ₈` here).
- Ratio of integrals with a common constant: prove `∫ f·e^{−tL_loc} = c * ∫ f φ e^{−tℓ}` by `rw [← integral_const_mul]` and
  `integral_congr_ae` (pointwise `simp only [e x]; ring` — `rw` misses the `(fun x => …) x` redexes), then
  `mul_div_mul_left _ _ hc.ne'` and `div_div_div_cancel_right₀ hZ'` with `hZ'` stated as the *unfolded* integral `≠ 0`.
  `simp only [gibbsExpectation, partitionFunction, e]` is too eager here (it also cancels the constant), leaving a goal the
  planned `rw` chain no longer matches.
- Even-remainder bookkeeping: convert `x^{2k}` to `|x|^{2k}` first, then a three-step `calc … := by ring`, `gcongr` (with the
  Young inequalities `|x|⁵ ≤ (|x|⁴ + |x|⁶)/2` in context), `by rw [hE]; unfold …; ring` — `nlinarith` on the nested products
  `|x|² * (E * (4 * (…)))` fails because linarith does not normalise products of atoms.
- Variance of a ratio: `t·Var = tN₂/D − (tN₁)²/(tD²)`; `div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a/b ≤ c/d ↔ a*d ≤ c*b`,
  then a `calc` through `(|c| + K₁)² · t · (4D²)` with `1 ≤ 4D²` from `D ≥ ½` (`nlinarith`). `|tN₁| ≤ |c| + K₁` is
  `rate_bounded`.
- Entries of `Q * diagonal d * Qᵀ`: `rw [Matrix.mul_apply]` *once* (outer product), then `simp only [Matrix.mul_diagonal,
  Matrix.transpose_apply]`; a bare `simp only [Matrix.mul_apply, …]` expands the inner product first and `mul_diagonal` never fires.

### E3's localised LLC (tide `localised-llc`)

- The seabed's first-order weight expansion is `|φ − 1 − g x₀ x| ≤ C₁x² + C₂x⁴` (linear part of `y` only), so `x³φ − x³ − g x₀x⁴ =
  x³(φ − 1 − g x₀ x)` exactly — no `−(g/2)x⁵` term (that appears only if one expands in `y`). Check which expansion a lemma
  states before writing the algebraic identity.
- Section `variable (hlam …)` + `include` attaches the hypotheses to *every* declaration mentioning `lam`, including a `rfl`
  lemma such as `anharmonicPotential lam alpha gamma = fun x => …`; `rw` with it then spawns `0 < lam` side goals. Mark such
  lemmas `omit hlam hgamma hdisc in`, and call omitted lemmas without those arguments.
- `abs_of_nonneg (by positivity)` inside `rw [...]` elaborates the `positivity` goal with a metavariable target and fails; give
  the type ascription `(by positivity : (0 : ℝ) ≤ e)`. `positivity` cannot see through `∀ i, 0 < lam i` for a summand: prove
  `0 ≤ ∑ i, …` with `Finset.sum_nonneg fun i _ => by have := hlam i; positivity` and feed it as a hypothesis.
- `⟨c * f⟩ = c⟨f⟩` in one dimension had no lemma: `unfold gibbsExpectation; simp only [mul_assoc]; rw [integral_const_mul,
  mul_div_assoc]` (`gibbsExpectation_const_mul₁`).
- Trace of `Q D₁ Qᵀ · Q D₂ Qᵀ`: `conj_mul_conj hQ, diagonal_mul_diagonal, Matrix.trace_mul_cycle, hQ, Matrix.one_mul,
  Matrix.trace_diagonal`; `t • (Q D Qᵀ) = Q (t • D) Qᵀ` via `← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul` and `rfl`.
- `gcongr with i; exact h i` over a `Finset.sum` can hand you the positivity side goal first; `mul_le_mul_of_nonneg_left
  (Finset.sum_le_sum fun i _ => h i) (by norm_num)` is deterministic.

### Integration by parts for the Gibbs measure (tide `gibbs-ibp`)

- `integral_eq_zero_of_hasDerivAt_of_integrable (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf' : Integrable f') (hf : Integrable f) :
  ∫ f' = 0` — no boundary terms or `Tendsto` proofs needed for `x^k e^{−tℓ}`: both integrabilities are the seabed's
  polynomial-moment theorem. Stein identities then come from `integral_sub`, `integral_const_mul`, `sub_eq_zero` and
  `simp only [gibbsExpectation]; rw [← mul_div_assoc, ← mul_div_assoc, h]`.
- `HasDerivAt.neg` produces the Pi-negated function `(-f) x`; restate the result with a `have h0 : HasDerivAt (fun y => -(t * ℓ y))
  … := (…).neg` (defeq) before composing with `.exp`, otherwise the `exp` shape never matches. `hasDerivAt_pow n x` carries
  `↑n * x ^ (n - 1)`: normalise with `simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]` then `ring`.
- `ring` does handle `x ^ (k + 1) * (… x ^ 3) = … x ^ (k + 4)` with a variable exponent plus numerals; no `pow_add` needed.
- Truncated `k − 1` at `k = 0` is harmless: the term is `↑0 * …`; `simp only [Nat.cast_zero, zero_mul]` then `mul_eq_zero`.
- `gibbsExpectation_coord_rotatedAnharmonic` lands on the *multi-d* coordinate expectation `gibbsExpectation (separableAnharmonic …)
  t (fun u => u i)`; convert to 1D with `gibbsExpectation_coord_separableAnharmonic … i (fun x => x)` stated via a `have hcoord :
  ∀ i, … = …` (defeq ascription absorbs the `(fun x => x) (u i)` redex) and `simp only [hcoord]`.
- `cubicScale lam alpha ^ 2 = alpha²/(36 lam³)`: `rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hlam.le]` then `field_simp; ring`.

### eq:covK to second order (tide `covK-order2`)

- The Stein–covariance reduction: `ℓ = ½xℓ' − (α/12)x³ − (γ/24)x⁴` (pointwise, `ring`) and `ibp_anharmonic` at `k = n + 1` and
  `k = 1` give the exact `t²Cov[ℓ, xⁿ] = (n/2)·t⟨xⁿ⟩ − (α/12)t²Cov[x³, xⁿ] − (γ/24)t²Cov[x⁴, xⁿ]`; prove the two expectation
  identities with `rw [← gibbs_lin3 …]; congr 1; funext x; unfold …; ring` (never `rw` a lemma that rewrites the *potential*
  `anharmonicPotential lam alpha gamma` itself — it is also the measure), then `Laplace.OneD.gibbsCov_pow_pow`/`_pow_id`,
  `simp only [_root_.Laplace.gibbsCov]`, substitute `X = 3M₂/t` and `field_simp; ring`.
- Instantiating a rate `h : ∀ {t}, T ≤ t → …` inside `have e := h (by linarith)` leaves `t` a metavariable and `linarith` fails on
  `T ≤ ?t`; write `h (t := t) (by linarith)` or a named `hTt : T ≤ t`.
- `gibbs_lin3` with an `x * ℓ'` term: the integrability lemma is stated for `x ^ 1 * ℓ'`; convert with
  `.congr (Eventually.of_forall fun x => by simp only [pow_one])` before `rw [← gibbs_lin3 hi1 …]`.
- Pair covariances to `O(1/t)` with `O(t⁻²)` remainder: write `t²(M_{m+n} − M_mM_n) = (t^{a}M_{m+n} − (t^{b}M_m)(t^{c}M_n))/t`
  (`field_simp`), `Laplace.OneD.rate_mul` for the product, and the one-line `sub_div_rate`.
- `field_simp` frequently closes `e : … = …/t` goals outright; a following `ring` then errors "No goals" — check each after the
  first `lean-state check`.

### The localised mean to second order (tide `localised-mean-coeff`)

- Taylor remainders of `exp` to any order: `|e^y − ∑_{m<n} y^m/m!| ≤ (e^M + n)|y|^n` for `y ≤ M`, `n ≥ 2` (`Real.exp_bound` on
  `|y| ≤ 1`, and for `|y| > 1` every lower power is `≤ |y|^n` with `1/m! ≤ 1`); the constant `(n+1)/(n!·n) ≤ 2` is one
  `div_le_iff₀; push_cast; nlinarith`. `(p + q)^n ≤ 2^n(p^n + q^n)` via `p + q ≤ 2 max p q`.
- Polynomial identities in the localised exponent `y = ax − bx²`: state the truncated sum as `∑ m ∈ Finset.range n, y^m/m!`, then
  `simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; push_cast; ring` against explicit coefficient defs; the
  `Finset.range 5` truncation gives a degree-9 identity, `range 4` a degree-6 one. Keep *signed* odd monomials `x³, x⁵` exact and
  bound their expectations by the signed leading rates; only the Taylor remainder is bounded through absolute powers.
- Long rate proofs time out (`whnf`/`isDefEq` at 200000 heartbeats) when the residual identity and the triangle bookkeeping are done
  on the `gibbsExpectation` terms directly. Factor them: an algebraic `*_key` lemma over abstract reals (`unfold; field_simp; ring`),
  an `*_assembly` lemma over abstract reals taking the moment inputs as hypotheses, and a thin instantiation with the concrete
  expectations passed *explicitly* (underscores for them break elaboration with "failed to synthesize Zero ?m").
- `gcongr` on `a/b ≤ a/c` leaves the side goal `c ≤ b`, not the division inequality: a following `exact div_le_div_of_nonneg_left …`
  mismatches — close it with `nlinarith` or `pow_le_pow_right₀ ht1 (by norm_num)`. `(by nlinarith)` for `t^3 ≤ t^4` is unreliable;
  use `pow_le_pow_right₀`.
- Thresholds inside `refine ⟨K, T, by positivity, by linarith, …⟩` can fail with a metavariable in the goal; prove `h1T : 1 ≤ T`
  beforehand and pass it. Two `variable … include` blocks in one section silently attach the hypotheses to every lemma in between.
### Path sums, fibrewise regrouping and homogeneous radial integrals (patterning: score function, homogeneous Gibbs)

- A sum over index paths `Fin T → ι` of a product is a product of sums: `Fintype.prod_sum (f : ∀ k, κ k → R) : ∏ k, ∑ j, f k j = ∑ x : ∀ k, κ k, ∏ k, f k (x k)`; instantiate `f` explicitly with `fun (_ : Fin T) i => …` and `rw [← h]`. Regroup `∑ k, ω (s k)` by fibre with `Finset.sum_fiberwise univ s (fun k => ω (s k))` then `sum_const`/`nsmul_eq_mul`; the count `#{k | s k = i}` as a real is `∑ k, if s k = i then 1 else 0` by `simp [count]` (`Finset.sum_boole` is simp). Both lemmas come out beta-reduced: a `simp only at h` afterwards fails with "no progress".
- Derivative of `∏ k ∈ u, (1 + ε c k)` at `0`: no `HasDerivAt.finset_prod` on this pin; `Finset.induction_on` with `HasDerivAt.mul` and `classical` (drop `[DecidableEq]` from the statement, the linter flags it).
- `(√s)^k * (√s)^k` with `√s` possibly `0`: `rpow_add_of_nonneg (sqrt_nonneg _) hk.le hk.le`, not `rpow_add` (needs `0 < x`). `(√s)^k = s^(k/2)` via `sqrt_eq_rpow, ← rpow_mul hs`; `(r^2)^(k/2) = r^k` via `← rpow_two, ← rpow_mul hr`. `integral_radial` needs its `G` given explicitly when the integrand is a beta-redex `(fun s => …) (z.1^2 + z.2^2)`, then `beta_reduce`.

### The localised energy to second order (tide `localised-llc-coeff`)

- One shared pointwise expansion serves several moments: prove the `x²φ` envelope once, then `x³φ − (…) = x·(x²φ − (…)) + p₄x⁶`
  and `x⁴φ − (…) = x²·(x²φ − (…)) + p₃x⁶ + p₄x⁷`, with `|x|^{2k+1} ≤ (x^{2k} + x^{2k+2})/2` turning the odd powers even. Only the
  monomials whose *signed* moments are needed (`x⁵`) stay exact; everything of higher degree goes into the even envelope.
- `abs_div` in a `rw` chain is greedy: after `abs_mul` on `|α/6 * (…/t)|` it rewrites `|α/6|` first, leaving `|6|`. Pass the
  dividend explicitly (`abs_div alpha`, `abs_div (t ^ 2 * M₃ - c₃')`) or dispose of the positive factor with `abs_of_pos` before
  calling `abs_div`.
- `Integrable.const_mul` yields `fun x => c * (f x * e x)`; to reshape to `(c * f x) * e x` use `.congr (Eventually.of_forall
  fun x => by dsimp only; ring)` — `simp only [Pi.smul_apply, smul_eq_mul]` is unused (linter) since no `smul` is present.
- `g²/(2λt(tλ + g)) ≤ g²/(2λ²t²)`: `rw [div_div]; apply div_le_div_of_nonneg_left (sq_nonneg g) (by positivity)` and close the
  denominator comparison with `nlinarith [mul_nonneg (mul_nonneg hlam.le ht.le) hg]`; `div_le_div_iff₀` followed by `nlinarith`
  fails on the nested division.
- Before writing a "sharpened" seabed lemma, `grep -rn "theorem <name>"`: `energy_anharmonic_order1_rate_sharp` (K/t²) already
  existed in `VarianceOrder3.lean` although `VarianceOrder2.lean`'s docstring only advertises the `K/(t√t)` version.

### eq:covK to second order on E2 (tide `covK-order2-multi`)

- `-alpha / (2 * lam ^ 2)` parses as `(-alpha) / …`, not `-(alpha / …)`: `sub_neg_eq_add` does not fire on `x - -alpha / c`. Rewrite
  first with `show -alpha / c = -(alpha / c) by ring` (or `neg_div`), then `sub_neg_eq_add`.
- `rw [abs_div, abs_div, abs_of_pos ht0, abs_of_pos ht0]` fails on the second `abs_of_pos`: `rw` rewrites *all* `|t|` at once.
- `set L := … with hL` does not reach terms a later `rw [lemma]` introduces with the unfolded name; `ring` then sees two atoms.
  Follow the `rw` with `← hL` (`rw [lemma, ← hL]`).
- `ring` does not normalise summands: `∑ f` and `∑ g` with `f`, `g` equal only up to `ring` are different atoms. Rewrite the summand
  first (`have e : ∀ i, f i = g i := fun i => by ring; simp only [e]`), pull signs out with `Finset.sum_neg_distrib`, and only then `ring`.
- A product of two `K/t` rates is a `K'/t` rate (`prod_rate`: `|XY − ab| ≤ (K_X(|b| + K_Y) + |a|K_Y)/t`); it needs `0 ≤ K_X` for the
  `gcongr` side goal `0 ≤ K_X / t` — carry nonnegativity of every rate constant.
- Diagonal extraction from a sum over `ι × ι`: `rw [← Finset.univ_product_univ, Finset.sum_product]; simp only [Finset.sum_ite_eq,
  Finset.mem_univ, if_true]` (with `mul_ite, mul_zero` when the `if` sits inside a product).
