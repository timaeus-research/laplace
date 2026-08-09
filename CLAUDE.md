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

**A `lake build` proves nothing about a file outside the import
closure.** The build gate is vacuous for a new file until
`Laplace.lean` imports it: `lake build` and CI both pass while the
file has arbitrarily many errors (this shipped an uncompiled file in
PR #55). After creating a file, verify BOTH the import line in
`Laplace.lean` AND the presence of the new `.olean` under
`.lake/build/lib/lean/` before reporting a build result. Job-count
deltas are too noisy to serve as the check.
