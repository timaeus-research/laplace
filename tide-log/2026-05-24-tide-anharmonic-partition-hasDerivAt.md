# Tide: anharmonic-partition-hasDerivAt

**Direction (user):** Candidate 5 from `projects/automation/log/2026-05-24-v50-tide-candidates-survey.md`:
laplace: Fill the `partition_hasDerivAt` sorry in `AnharmonicGibbsRegularity`.

**Seabed:** `lean/laplace`, commit `1958076` (post v49 retrospective formatting fix).
**Worktree:** `sri/lean/laplace-tide-anharmonic-partition-hasDerivAt/`, branch `tide/anharmonic-partition-hasDerivAt`.
**Started:** 2026-05-24T09:45:00Z

## Seabed snapshot

The sorry is at `Laplace/OneD/AnharmonicGibbsRegularity.lean:218` (in
the `partition_hasDerivAt` field of
`Threepoint.anharmonic_id_gibbsRegularity`). It is well-documented
with a proof sketch (lines 187–217).

Goal type (after rewriting `partition_h_zero`'s `congr 1; funext;
ring_nf` style normalisation):

```
HasDerivAt (fun h : ℝ => ∫ x : ℝ,
    Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
  (∫ x : ℝ, (-t * x) *
    Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
  0
```

with hypotheses `0 < lam`, `0 < gamma`, `alpha² < 3·lam·gamma`,
`0 < t`.

**Public witnesses already present (lines 45–124 of the same file):**

- `integrable_exp_neg_t_anharmonic` — `Integrable (fun x ↦
  exp(-(t · L_anh(x))))` (the unperturbed case, n=0).
- `integrable_x_mul_exp_neg_t_anharmonic` — `Integrable (fun x ↦ x *
  exp(-(t · L_anh(x))))` (the n=1 case; this is the integrability of
  the RHS integrand `(-t·x) · exp(-(t · L_anh(x)))` modulo the `-t`
  scalar).

**Coercivity input:** `Laplace/OneD/Anharmonic.lean:126`,
`anharmonic_coercive : ∃ c > 0, ∀ x, c · x² ≤ L_anh(x)`.

**Harmonic mirror** (`Laplace/OneD/HarmonicGibbsRegularity.lean:241`)
takes a different proof route: square-completion gives a closed form
`Z(h) = exp(t·h²/(2λ)) · √(2π/(λt))`, and `partition_hasDerivAt`
falls out of differentiating that closed form. The anharmonic
partition function has *no closed form* under linear perturbation, so
this route is closed to us.

**Canonical Mathlib lemma:**
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` in
`Mathlib/Analysis/Calculus/ParametricIntegral.lean:289`. Signature:

```
theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ)
    {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) :
    Integrable (F' x₀) μ ∧
    HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀
```

This is exactly what we need with `x₀ = 0`, `s` a ball around `0`,
`F h x = exp(-(t·(L_anh + h·x)))`, `F' h x = -t·x · exp(-(t·(L_anh +
h·x)))`.

## Candidates v1 (Claude)

The "candidate" here is the **proof strategy**, since the target
statement is already pinned by the existing sorry.

### Candidate A — Direct application of `hasDerivAt_integral_of_dominated_loc_of_deriv_le`

Apply the lemma with:
- `x₀ = 0`, `s = Metric.ball (0 : ℝ) 1` (or any fixed positive radius;
  the proof is uniform in `h` over a bounded interval).
- `F h x = Real.exp (-(t · (anharmonicPotential lam alpha gamma x +
  h · x)))`.
- `F' h x = (-t · x) · Real.exp (-(t · (anharmonicPotential lam alpha
  gamma x + h · x)))`.
- `bound(x) = t · (|x| + 1) · Real.exp (t · |x|) · Real.exp (-(t ·
  anharmonicPotential lam alpha gamma x))`.

  Equivalently, by coercivity `L_anh(x) ≥ c·x²`,
  `bound(x) ≤ t · (|x| + 1) · exp(t · |x|) · exp(-t·c·x²)`,
  and by completing the square `-t·c·x² + t·|x| = -t·c·(|x| -
  1/(2c))² + t/(4c)`,
  `bound(x) ≤ t · (|x| + 1) · exp(t/(4c)) · exp(-t·c·(|x| -
  1/(2c))²)` — a translated Gaussian times a degree-1 polynomial,
  integrable.

  A cleaner concrete dominator: split `-t·c·x² + t·|x| = -t·c·x²/2 +
  (-t·c·x²/2 + t·|x|)` and bound the second half by its maximum
  `t²/(2c)` (achieved at `|x| = 1/c`). Then
  `bound(x) ≤ t · (|x| + 1) · exp(t²/(2c)) · exp(-t·c·x²/2)`,
  which is `const · (|x| + 1) · exp(-(t·c/2)·x²)`, integrable via
  Mathlib's `integrable_abs_pow_mul_exp_neg_mul_sq` summed for `n ∈
  {0, 1}` plus the `n = 0` Gaussian.

- AEStronglyMeasurable: continuity of `(h, x) ↦ exp(-(t·(L_anh + h·x)))`.
- Pointwise derivative: `HasDerivAt.exp` composed with
  `HasDerivAt.const_mul` and the linear function `h ↦ h · x`.

Bound on `|F' h x|` for `h ∈ ball 0 1`:
  `|F' h x| = t · |x| · exp(-(t·(L_anh + h·x)))`
  ≤ `t · |x| · exp(-(t·L_anh)) · exp(t·|h·x|)`
  ≤ `t · |x| · exp(-(t·L_anh)) · exp(t·|x|)` (since `|h| < 1`).
This is dominated by `t · (|x| + 1) · exp(-(t·L_anh)) · exp(t·|x|)`
(adding `+1` is gratuitous but matches the sketch's dominator).

**Rationale.** This is the standard route described in the sorry's
sketch. Minimal infrastructure delta: integrability of the dominator
is the only nontrivial step beyond mechanical lemma application; that
factors through coercivity which is already in
`Laplace/OneD/Anharmonic.lean`.

**Estimated size.** 100–180 lines.

### Candidate B — Use the stronger Lipschitz version (`_of_lip`)

Same lemma family, but the `_of_lip` version takes a Lipschitz bound
on `F` directly rather than a bound on `F'`. This avoids the pointwise
derivative obligation but requires an integrable Lipschitz constant
in `h`.

For us: `‖F h₁ x - F h₂ x‖ ≤ L(x) · |h₁ - h₂|`. The Lipschitz constant
of `h ↦ exp(-t·(L_anh + h·x))` in `h` is `t·|x| · sup_{h∈s}
exp(-t·(L_anh + h·x))`. That's essentially the same bound construction
as Candidate A, so this doesn't save real work, and the
derivative-at-`x₀` hypothesis becomes ae-pointwise rather than
uniform — slightly nicer but a wash.

**Demoted.** Use Candidate A.

## Candidates v1 vote

- Claude: A.

## GPT-5.5 Pro v1

Full response in
`tide-log/gpt_responses/gpt55_partition_hasDerivAt_v1.md`.

Three key takeaways:

1. **Arithmetic correction.** My draft had the max-of-quadratic value
   as `t²/(2c)`. Correct value is `t/(2c)`. Recompute: for
   `f(u) = -tc/2·u² + tu`, `f'(u) = -tc·u + t = 0` at `u = 1/c`; then
   `f(1/c) = -t/(2c) + t/c = t/(2c)`. So the dominator constant is
   `exp(t/(2c))`, not `exp(t²/(2c))`.

2. **Shorter dominator route.** GPT suggests bypassing the Gaussian
   library and using the existing
   `integrable_x_mul_exp_neg_t_anharmonic` at temperature `t/2`:
   ```
   t·|x| ≤ (tc/2)·x² + t/(2c)               [AM-GM]
        ≤ (t/2)·L_anh(x) + t/(2c)            [coercivity, c·x² ≤ L]
   so:
   |F'(h, x)| ≤ t·|x| · exp(-t·L_anh + t·|x|)
             ≤ t·|x| · exp(-(t/2)·L_anh(x)) · exp(t/(2c))
             = t · exp(t/(2c)) · |x| · exp(-(t/2)·L_anh(x))
   ```
   This is the bound to use. Integrability of `|x| · exp(-(t/2)·L_anh(x))`
   is `(integrable_x_mul_exp_neg_t_anharmonic hlam hgamma hdisc
   ht_half_pos).norm` (taking the norm bridges `x` to `|x|` since
   `exp > 0`).

3. **`_of_deriv_le` is the right lemma**; `_of_lip` doesn't save work
   here. Practical tip: `s = Metric.ball 0 1` is fine (gives strict
   `|h| < 1`, which is stronger than the `|h| ≤ 1` needed).

4. **AEStronglyMeasurable**: per-fixed-`h` continuity +
   `Eventually.of_forall` is idiomatic. No "joint continuity" lemma
   needed.

## Candidates v2 (Claude)

Adopted from GPT-5.5 Pro v1: replace Gaussian dominator (Candidate A)
with the in-seabed-only dominator `t · exp(t/(2c)) · |x| · exp(-(t/2)·L_anh(x))`.

**Plan:**

- `s = Metric.ball (0 : ℝ) 1`; extract `|h| < 1` from membership.
- `bound : ℝ → ℝ`, `bound x = t · Real.exp(t/(2c)) · |x| ·
  Real.exp(-((t/2) · anharmonicPotential lam alpha gamma x))`.
- Integrability of `bound`: via
  `(integrable_x_mul_exp_neg_t_anharmonic hlam hgamma hdisc
  ht_half_pos).norm.const_mul (t · Real.exp(t/(2c)))`. (And rewrite
  `‖x · exp(-(t/2)·L)‖ = |x| · exp(-(t/2)·L)` since `exp > 0`.)
- Pointwise bound: chain of `Real.exp_le_exp.mpr` + arithmetic
  (AM-GM at `√(tc/2)·|x|` and `√(t/(2c))` gives `t·|x| ≤ (tc/2)·x² +
  t/(2c)`).
- Pointwise derivative: standard composition `HasDerivAt.exp`,
  `HasDerivAt.neg`, `HasDerivAt.const_mul`, `HasDerivAt.const_add`,
  `hasDerivAt_id`. The derivative at general `h` is `(-t · x) · exp(-(t·(L
  + h·x)))`; at `h = 0` it's `(-t · x) · exp(-(t·L))`, matching the
  RHS integrand.
- AEStronglyMeasurable: `Eventually.of_forall (fun h => (continuity).
  aestronglyMeasurable)`.

**Estimated size:** 100-150 lines (slightly shorter than v1 thanks to
GPT's bound).

## Vote

- Claude: Candidate v2 (Candidate A with GPT's dominator refinement).
- GPT-5.5 Pro: same (the suggestion came from GPT).

Agreed. Proceeding to Step 3.

## Step 3 hand-off

- Worktree: `sri/lean/laplace-tide-anharmonic-partition-hasDerivAt/`.
- File to edit: `Laplace/OneD/AnharmonicGibbsRegularity.lean`.
- Target: replace the `sorry` at line 218 with the dominated-convergence
  proof per Candidate v2.
- Tide-log: this file.

## Numerical check

**Not feasible: structural.** The candidate is a `HasDerivAt`
instance, not a closed-form value. There is nothing to evaluate
numerically. The matching empirical work for the broader arc (FDT
identity `∂_h Cov = -t·κ₃` validated at `(λ,α,γ)=(1,0.5,1), t=100`
in `projects/primer/experiment-log/2026-05-23-experiment-fdt-identity-1d.md`)
already covers the consumer end of this instance — completing this
sorry unblocks the formal anchor for that empirical validation.

(Vote recorded above; this stub kept for ordering compatibility.)

## Result

Closed. `Threepoint.anharmonic_id_gibbsRegularity` is now sorry-free;
`scripts/sorries` reports 0 sorry. The instance is the headline of
the file at `Laplace/OneD/AnharmonicGibbsRegularity.lean:295`.

**Helpers added** (private, before the instance):
- `anharmonic_perturbed_pointwise_hasDerivAt` — pointwise `h`-derivative
  of `exp(-(t · (L_anh(x) + h·x)))`.
- `amgm_t_abs_x` — scalar AM-GM `t · |x| ≤ (tc/2)·x² + t/(2c)`.
- `anharmonic_perturbed_pointwise_bound` — pointwise bound chain
  combining the AM-GM step with coercivity.
- `anharmonic_bound_integrable` — bound function is integrable via
  `integrable_x_mul_exp_neg_t_anharmonic` at half temperature.

**Total addition:** ~160 lines (helpers + filled instance + docstring
clean-up), matching the v2 estimate.

**Observations / surprises:**

- The `field_simp` tactic on an equation with two rational terms
  (`2c · (tc/2 · x² + t/(2c)) = tc²·x² + t`) closed the goal entirely
  on its own; a trailing `ring` then errored with "No goals to be
  solved". The linter from the fresher Mathlib cache (cf. the
  `tide-worktree Mathlib cache drift` memory) is now strict about
  this — dropping the `ring` after `field_simp` was the right fix.
- `(hasDerivAt_id h₀).mul_const x` returns a derivative `1 * x`
  rather than `x`; needed `simpa` to reduce.
- `Topology` was missing from the file's `open` list — added alongside
  `MeasureTheory` to make `𝓝` available.
- `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` is
  *not* in the `MeasureTheory` namespace; it lives at the root after
  the file's `public section` declaration. Call without the prefix.
- `fun_prop` after `unfold anharmonicPotential` resolves the
  AEStronglyMeasurable obligations on `F h` and `F' 0` directly,
  avoiding manual `Continuous.add`/`.mul`/`.comp` chains that
  hit unification issues with the inner sum `(L_anh + h·x)`.

## Retrospective

`retrospectives/2026-05-24-tide-anharmonic-partition-hasDerivAt.tex`
(compiled to PDF; ~250 lines of LaTeX).


