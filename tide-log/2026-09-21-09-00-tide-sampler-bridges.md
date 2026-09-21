# Tide: sampler-bridges

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." Continuing the Sanity on Sampling programme: bridges from the abstractions of the previous tides to the algorithm as implemented (the ULA update `w ↦ (I-hP) w + √(2h) ξ` with a standard Gaussian `ξ` as a random map on the product space) and to real random variables (the AR(1) finite-chain theorem as an expectation over a probability space).
**Seabed:** laplace, commit d96ad52 (origin/main at tide start; `ula-uniqueness` being merged in parallel)
**Started:** 2026-09-21T05:34Z
**Worktree / branch:** learning-theory/lean/laplace-tide-sampler-bridges, tide/sampler-bridges
**Retrospective:** skipped by user instruction for this auto run.

## Seabed snapshot

- `Laplace/Sampler/GaussianInvariance.lean`, `GaussianUniqueness.lean` (`gaussStep`, invariance, uniqueness, convergence), `AR1.lean` (Gram-matrix AR(1) theorem), `ULA.lean`, `Lyapunov.lean`.
- Mathlib: `stdGaussian`, `multivariateGaussian`, `Measure.conv`, `Measure.map_prod_map`, `Lp`/`MemLp.toLp`, `L2.inner_def`.

## Candidates v1 (Claude)

Verbatim in `tide-log/gpt_sampler_bridges_prompt_v1.md`: **M** the ULA update as a random map (M1 scaling of the standard Gaussian, M2 sampling-map form of `gaussStep`, M3 the law of `A w + √(2h) ξ`); **B** the finite-chain theorem for real `L²` random variables.

## Numerical check

Not applicable (identities of measures / bridges between formulations); the underlying closed forms were checked numerically in the earlier tides.

## GPT-6 Astra v1

Verbatim in `tide-log/gpt_sampler_bridges_v1.md`. Summary: M1–M3 correct (M1 for every real `c`; `CFC.sqrt (c²•1) = |c|•1`, so go through characteristic functions: `charFun_map_smul`, `charFun_stdGaussian`, `charFun_multivariateGaussian`, `Measure.ext_of_charFun`; M2 via a generic `(μ.prod ν).map (fun p => L p.1 + p.2) = (μ.map L) ∗ ν` from `Measure.map_map` + `Measure.map_prod_map` and the definition of `conv`; M3 needs `0 ≤ h` and `Real.sq_sqrt`). B correct: define the chains pointwise, prove `MemLp` inductively, package into `Lp ℝ 2 P` via `MemLp.toLp`, prove two identification lemmas (`inner (toLp f) (toLp g) = ∫ f g`, `‖toLp f‖² = ∫ f²`, not through `Lp.norm_def`), the recurrence in `Lp` by a.e. extensionality, a generic expected-quadratic-statistic lemma for a finite family, then `pooled_sample_variance`; pairwise independence + centring + second moment `v` gives the moment table (`IndepFun.integral_mul_eq_mul_integral`); note `AR1Chain.white` includes index 0 (keep a genuine innovation there). Vote: **B alone** (M as a bounded follow-up).

## Integration (Claude)

B is the main target as voted; M1–M3 are attempted at the end of the same excursion as the bounded follow-up GPT describes, if B lands cleanly (recorded as a micro-divergence, not a disagreement on the target).

## Vote
- Claude: B (with M as stretch).
- GPT-6 Astra: B alone.

Agreed after one round.

## Result

- Commit `dbd40a2` on `tide/sampler-bridges` (base 649efcc). Full `lake build` green; `scripts/sorries`: 0 sorry, 0 axiom, 0 native_decide.
- `Laplace/Sampler/AR1Real.lean` (     166 lines): `inner_toLp_eq_integral`, `norm_toLp_sq_eq_integral`, `toLp_finset_sum`, `realChain` (+ `_zero`, `_succ`), `memLp_realChain`, `toAR1Chain` (the realised chain as an `AR1Chain (Lp ℝ 2 P)`), `integral_pooled_statistic` (generic expected quadratic statistic of a finite family), `expected_pooled_sample_variance` (the note's finite-chain prediction as an expectation), `white_of_indep`.
- `Laplace/Sampler/RandomMap.lean` (      99 lines): `stdGaussian_map_smul` (`c • ξ ~ N(0, c² I)`), `map_add_prod` (sampling-map form of a convolution), `gaussStep_eq_map_prod`, `ula_update_law` (the ULA update `(w, ξ) ↦ A w + √(2h) ξ` on `μ ⊗ N(0, I)` has law `gaussStep`), `ula_update_law_of_indep` (for independent random variables).
- Both the main target B and the stretch M landed. Surprises: none; the L² packaging went through with GPT-6 Astra's recipe (identify inner products through `L2.inner_def`, recurrences by `rfl` after `toLp_add`/`toLp_const_smul`); the only friction was `Measure.map_map` needing its functions passed explicitly.
