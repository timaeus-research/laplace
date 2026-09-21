# Tide: sampling without replacement, the finite population correction behind E8

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." (auto run on the Sanity on Sampling mathematics; this tide derives the two E8 constants: the minibatch gradient-noise covariance `C_g = (1/m)(1 − m/n) S²` and the full law's state-dependent coefficient `(1 − m/n)/(m(n−1))`.)
**Seabed:** laplace, `main` after the `localised-bias` landing; worktree `laplace-tide-minibatch-fpc`, branch `tide/minibatch-fpc`
**Started:** 2026-09-21 (UTC, see file name)

## Context

E8 of the note: SGLD replaces `∇L` by the mean gradient over a minibatch of `m` of the `n` samples drawn *without replacement*; the noise `η` has covariance `C_g = (1/m)(1 − m/n) S²` at `w*`, `S²` the sample covariance of the per-sample gradients (`n − 1` normalisation), and for quadratic per-sample losses the exact second moment obeys the Lyapunov law with the extra term `lr² t² (1 − m/n)/(m(n−1)) ∑ᵢ (Hᵢ − H) Σ (Hᵢ − H)` (the "full law"). The seabed's `FullStep.lean` (tide `fullstep-contraction`) treats the full law abstractly with a coefficient parameter `minibatchCoeff h t m n = h²t²(1 − m/n)/(m·n)`, whose denominator disagrees with the note's `m(n−1)` (the note is right: this is Cochran's finite population correction with the `n − 1` sample variance; numerical check below). Nothing in the seabed derives either constant from the sampling scheme.

## Candidates v1 (Claude)

**A. The finite population correction for bilinear forms of the minibatch mean.** For `a : Fin n → V` (`V` a real vector space), `1 ≤ m ≤ n`, `ā = (1/n) ∑ᵢ aᵢ`, `mean_B a = (1/m) ∑_{i∈B} aᵢ`, and the uniform law on `B ∈ powersetCard m univ` (`C(n,m)` subsets):

1. counting: `#{B : i ∈ B} = C(n−1, m−1)`, `#{B : i, j ∈ B} = C(n−2, m−2)` for `i ≠ j` (Mathlib: `Finset.card_filter_powersetCard_subset`);
2. `∑_B ∑_{i∈B} f i = C(n−1,m−1) ∑ᵢ f i` and `∑_B ∑_{i∈B} ∑_{j∈B} g i j = C(n−1,m−1) ∑ᵢ g i i + C(n−2,m−2) ∑_{i≠j} g i j`;
3. unbiasedness `E_B[mean_B a] = ā`, and for every bilinear `β : V →ₗ V →ₗ W`:
   `E_B[β(mean_B a − ā)(mean_B a − ā)] = ((1 − m/n)/(m(n−1))) ∑ᵢ β(aᵢ − ā)(aᵢ − ā)` (`fpc_bilinear`), equivalently `= (1/m)(1 − m/n) · S²_β` with `S²_β = (1/(n−1)) ∑ᵢ β(aᵢ − ā)(aᵢ − ā)`;
4. E8 instances: `β = vecMulVec` gives `C_g = (1/m)(1 − m/n) S²` for per-sample gradients `gᵢ : ι → ℝ` (`minibatch_gradient_cov`); `β(X, Y) = X * Σ * Y` gives `E_B[(H_B − H) Σ (H_B − H)] = ((1 − m/n)/(m(n−1))) ∑ᵢ (Hᵢ − H) Σ (Hᵢ − H)` (`minibatch_hessian_term`), the full law's state-dependent term;
5. `minibatchCoeff` corrected to `h²t²(1 − m/n)/(m(n−1))` in `FullStep.lean` (its only use is as the coefficient of `stateTerm`; `minibatchCoeff_nonneg` re-proved), so that `e8FullStep` is the note's full law with the derived constant.

Rationale: the two constants the note states without proof, derived once from the sampling scheme, plus a correction to the seabed. Closed forms as stated.

**B. The full second-moment recursion of minibatch SGLD on a quadratic model** (random minibatch independent of the Gaussian noise; `E[w'w'ᵀ] = e8FullStep (E[wwᵀ])`): needs a probability model for the pair (minibatch, noise) and the cross terms; a follow-up once A exists.

**C. Only the scalar case** (`V = ℝ`, `β = (·)(·)`): too small; the bilinear statement costs nothing extra.

Claude's preference: A.

## Numerical check

`scratchpad/numcheck15.py`: `n = 7`, `m = 3`, `d = 2`, random per-sample gradients and symmetric per-sample Hessians, exhaustive enumeration of the 35 subsets: `‖C_g − (1/m)(1 − m/n) S²‖_max = 1e-16`; `‖E_B[(H_B − H̄) Σ (H_B − H̄)] − ((1 − m/n)/(m(n−1))) ∑ᵢ (Hᵢ − H̄) Σ (Hᵢ − H̄)‖_max = 2e-16`; subset counts `15 = C(6,2)`, pair counts `5 = C(5,1)`; the minibatch mean is unbiased to 4e-17. With `m·n` in place of `m(n−1)` the Hessian term would be off by the factor `(n−1)/n = 6/7`.

## GPT-6 Astra v1

Saved verbatim in `gpt_minibatch_fpc_v1.md`. Summary: the bilinear finite population correction is confirmed for `1 ≤ m ≤ n`, `n ≥ 2`
(no symmetry of `β` needed); `minibatchCoeff` must have denominator `m·((n:ℝ) − 1)`. Correction: the pair count `C(n−2, m−2)` is wrong at
`m = 1` under truncated subtraction (Lean gives `C(n−2, 0) = 1`, the count is `0`), so guard it: `if 2 ≤ m then C(n−2,m−2) else 0`; the
off-diagonal sum is over ordered pairs; the key identity for centred `xᵢ` is `∑_{i≠j} β(xᵢ,xⱼ) = −∑ᵢ β(xᵢ,xᵢ)`. Lean: indicator sums and plain
`Finset.sum_comm`, natural-number cross-multiplied binomial identities cast to `ℝ`, `β : V →ₗ[ℝ] V →ₗ[ℝ] W` with `map_sum`; match the seabed's
`stateTerm` with the *transposed* sandwich `X * Σ * Yᵀ`. Edge cases `m = n` and `n = 1` give zero on both sides (document the totalised
division). Votes **A** with the guarded pair count and the transposed sandwich.

## Vote
- Claude: candidate A (guarded pair count, transposed sandwich, `minibatchCoeff` corrected)
- GPT-6 Astra: candidate A (same)

Agreed.

## Result

Committed as `Laplace/Sampler/Minibatch.lean` (a171afd), 322 lines, 0 sorries, `lean-state check` clean; `FullStep.lean`'s
`minibatchCoeff` corrected to `h² t² (1 − m/n) / (m ((n:ℝ) − 1))` (its nonnegativity re-proved; nothing else depended on the value).

Theorems: `batchMean`, `popMean`, `sum_sub_popMean`, `batchMean_sub_popMean`; counting `card_powersetCard_mem` (`C(n−1,m−1)`),
`card_powersetCard_pair` (`C(n−2,m−2)`, `0` at `m = 1`); double counting `sum_eq_sum_ite_mem`, `sum_powersetCard_sum`,
`sum_powersetCard_sum_sum`; binomials `choose_mul_eq_choose_pred`, `choose_mul_eq_choose_pred_pred`, `fpc_coeff`;
`fpc_bilinear₂` (two families), `fpc_bilinear`; E8: `outerBilin`, `sampleCov`, `minibatch_gradient_cov`
(`C_g = (1/m)(1 − m/n) S²`), `sandwichBilin`, `minibatch_hessian_term` (`= ((1−m/n)/(m(n−1))) • stateTerm`), `minibatchCoeff_eq`.

Surprises: the pair count `C(n−2, m−2)` is false at `m = 1` under truncated subtraction (GPT caught it); `simp_rw` with the indicator
lemma loops (its right-hand side is again a `Finset` sum); `Nat.succ_mul_choose_eq` is now `Nat.add_one_mul_choose_eq`. The cross
form `fpc_bilinear₂` costs nothing extra and is what the one-step minibatch recursion (next tide) needs for its `H`–`g` cross terms.
