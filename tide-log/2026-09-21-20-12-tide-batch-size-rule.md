# Tide: batch-size-rule

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: E8's rule of thumb in the note's variables and the batch-size / step-size rules.
**Seabed:** laplace, main after `autocorrelation-time` (c03b14e)
**Started:** 2026-09-21 (UTC, see filename)

## Context

E8 of the sanity note: "*The rule of thumb.* For `lr pᵢ ≪ 1` the relative excess of the LLC is `lr t² tr(C_g)/(2d) ≈ lr pmax t tr(S²)/(2 d λmax m)`
… Keeping the excess below `ε` needs `m ≳ lr pmax t tr(S²)/(2 d λmax ε)`, or equivalently a step size shrinking like `1/t²` rather than `1/t`."
The Summary: "the LLC is inflated by about `lr t² tr(C_g)/(2d)`, which at fixed relative step grows linearly in `t`". The seabed has the
first form as a two-sided bound (`minibatch_inflation_normalised`, tide `llc-closures`: the normalised excess lies between
`h t² tr C/(2d)` and `h t² tr C/(2d(1 − h pmax/2))` for any positive semidefinite `C`) and the gradient-noise covariance
`C_g = (1/m)(1 − m/n) S²` (`minibatch_gradient_cov`, tide `minibatch-fpc`). The second form — in `lr pmax`, `t`, `tr S²`, `λmax`, `m` — and the
two rules are not stated.

## Candidates v1 (Claude)

Let `P = tH` with eigenvalues `pᵢ ≤ pmax = t λmax`, `0 < h`, `h pmax < 2`, `1 ≤ m ≤ n`, `2 ≤ n`, `S² = sampleCov g` of the per-sample
gradients, `C_g = (1/m)(1 − m/n) S²`, `excess := (LLC_mb − LLC_ULA)/(d/2)`.

**A. `C_g` is positive semidefinite and `tr C_g = (1/m)(1 − m/n) tr S²`** (`sampleCov_posSemidef`, `minibatchGradCov_posSemidef`,
`trace_minibatchGradCov`).

**B. The rule of thumb in the note's variables** (`minibatch_excess_bounds_note`):
```
(h pmax) t (1 − m/n) tr S² / (2 d λmax m) ≤ excess ≤ (h pmax) t (1 − m/n) tr S² / (2 d λmax m (1 − h pmax/2))
```
so the note's `lr pmax t tr(S²)/(2 d λmax m)` is the excess to within the factors `(1 − m/n)` and `1/(1 − h pmax/2)`; at fixed relative step
`h pmax` the excess grows linearly in `t` and inversely in `m`.

**C. The batch-size rule** (`batch_size_rule`): for `ε > 0`,
```
m ≥ (h pmax) t tr S² / (2 d λmax ε (1 − h pmax/2))  →  excess ≤ ε.
```

**D. The step-size rule** (`step_size_rule`): at fixed `C_g`, `h t² tr C_g ≤ 2 d ε (1 − h pmax/2)  →  excess ≤ ε`: keeping the excess below `ε`
as `t` grows needs `h = O(1/t²)` (against the `h = O(1/t)` that keeps `h pmax` fixed).

Vote intention: A+B+C+D.

## Numerical check

`numcheck35.py` (`n = 7`, `m = 3`, `d = 4`, random per-sample gradients; the batch-mean covariance by enumerating all `C(7,3)` batches;
`P = tH` with `λ = (1, .5, .2, .1)`, `t = 50`, `h pmax = 0.1`; the Lyapunov laws by fixed-point iteration):
```
(1) tr C_g = 0.604965  vs (1/m)(1-m/n) tr S^2 = 0.604965
(2) excess=0.386668 in [0.378103, 0.398003] ok=True; note form lower=0.378103
(3) batch-size rule: need m >= 41.79 for excess <= 0.05; with m=3: excess=0.3867 (rule satisfied: False)
```
The trace identity is exact, the excess sits inside the two-sided bound whose lower end is the note's form, and the batch-size rule is
(correctly) not met at `m = 3`.

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_batch_size_rule_v1.md`. Summary: A–D correct with explicit positivity (`t, λmax, d, h > 0`, `h pmax < 2`, `pmax = t λmax`). Two wording corrections: only the expression *with* the finite-population factor `1 − m/n` is a lower bound (at `m = n` the excess is zero while the note's expression is positive) — present the note's `lr pmax t tr S²/(2 d λmax m)` as the small-`m/n`, small-`h pmax` approximation of a two-sided bound; the batch-size threshold can exceed `n` (then the sufficient condition is infeasible, not false, and misses the exact `m = n` zero-noise case). D is a sufficient condition; the *necessity* of `h = O(t⁻²)` follows from the lower bound; under that scaling `h pmax = O(1/t) → 0` so the ULA discretisation inflation vanishes while the minibatch excess need not. Lean: explicit `0 ≤ c` for PSD smul, denominator positivity from `2 ≤ n`, no inverse-monotonicity lemma needed for C (drop `1 − m/n ≤ 1` and clear denominators). Skip the numerical instances (missing `tr S²/λmax`); the monotonicity remarks concern the bound expressions, whose batch dependence is exactly `1/m − 1/n`.

## Vote
- Claude: A+B+C+D
- GPT-6 Astra: A+B+C+D

Agreed. Proceeding to Step 3.
