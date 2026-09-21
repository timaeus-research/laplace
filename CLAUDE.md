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
