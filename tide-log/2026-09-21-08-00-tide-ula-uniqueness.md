# Tide: ula-uniqueness

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." Continuing the Sanity on Sampling programme: after invariance (tide `ula-invariance`), the uniqueness of the invariant law of the ULA chain on a Gaussian target and the convergence of the Gaussian marginals to `N(0, Σ_ULA)`, via characteristic functions.
**Seabed:** laplace, commit a1afc78 (origin/main at tide start; `ula-invariance` being merged in parallel, this branch will merge it before building)
**Started:** 2026-09-21T05:20Z
**Worktree / branch:** learning-theory/lean/laplace-tide-ula-uniqueness, tide/ula-uniqueness
**Retrospective:** skipped by user instruction for this auto run.

## Seabed snapshot

- `Laplace/Sampler/Lyapunov.lean`, `ULA.lean`: covariance recursion, fixed point, finite-time identity, spectral packaging.
- `Laplace/Sampler/GaussianInvariance.lean` (tide `ula-invariance`): Gaussian push-forward, convolution, invariance of `N(0, Σ_ULA)`, finite-time marginal law.
- Mathlib: `charFun` API (`charFun_apply`, `charFun_conv`, `continuous_charFun`, `Measure.ext_of_charFun`), `multivariateGaussian`.

## Candidates v1 (Claude)

Verbatim in `tide-log/gpt_ula_uniqueness_prompt_v1.md`: **U** uniqueness of the invariant probability law (no moment assumption) via iterated characteristic functions and the finite-time identity; **C** convergence of the Gaussian marginals (pointwise charFun, weak convergence via Lévy if available); **C0** the matrix limits `A^n → 0`, `Σ_n → Σ_∞`.

## Numerical check

Not feasible in the usual sense (uniqueness of a measure); the convergence of the covariance iterates was checked numerically in the sampler-laws tide (iteration from a perturbed start returns to `S` to 1.4e-14).

## GPT-6 Astra v1

Verbatim in `tide-log/gpt_ula_uniqueness_v1.md`. Summary: U correct with no moment assumption; separate the abstract uniqueness theorem (hypotheses: `R`, `S` PSD, `covStep A R S = S`, and the decay `∀ t, euclid ((Aᵀ)^n) t → 0`) from its spectral discharge and the ULA corollary; the PSD-ness of the fixed point is a genuine obligation (given for ULA by `ulaCov_posDef`). Preferred proof: the *quotient argument*: with `g = charFun N(0,S)` (nonvanishing) and `B = euclid Aᵀ`, both `μ` and `N(0,S)` invariant give `H t = H (B t)` for `H = charFun μ / g`, hence `H t = H (B^n t) → H 0 = 1` by continuity; no iterated covariance sums needed. Matrix decay via `A^n = U diag(a^n) Uᵀ` (induction), `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`, `tendsto_pi_nhds`, continuity of multiplication (warning: `|a_i| < 1` does not bound the ∞-operator norm, so `linftyOpNormedRing` is not a shortcut). Covariance convergence from `covStep_iterate_sub_fixed` for any `X₀`. Stronger nearby target: pointwise charFun convergence from *any* initial law (same quotient: `charFun μ_n t = g t · H₀(B^n t) → g t`), weak convergence via Lévy if the pin's theorem covers `EuclideanSpace`. Vote: U + C0 (abstract uniqueness by the quotient argument, spectral decay helpers, ULA corollary).

## Integration (Claude)

Accepted: quotient route; abstract theorem with the decay hypothesis; spectral and ULA corollaries; the attraction corollary (pointwise charFun convergence from any initial probability law) included since it is the same argument; weak convergence via `ProbabilityMeasure.tendsto_iff_tendsto_charFun` (present in the pin, `MeasureTheory/Measure/LevyConvergence.lean`) if its hypotheses fit `EuclideanSpace ℝ ι`.

## Vote
- Claude: U + C0 + attraction corollary.
- GPT-6 Astra: U + C0.

Agreed after one round (the attraction corollary is GPT's own "stronger nearby target").
