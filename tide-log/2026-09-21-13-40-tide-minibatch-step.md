# Tide: the exact one-step recursion of minibatch SGLD on linear regression (E8)

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." (auto run on the Sanity on Sampling mathematics; this tide turns E8's "the full law is exact for linear regression" into a theorem about the one-step mean and second-moment recursion.)
**Seabed:** laplace, `tide/minibatch-fpc` at c430f7a (chained; `main` at 7130c7c); worktree `laplace-tide-minibatch-step`, branch `tide/minibatch-step`
**Started:** 2026-09-21 (UTC, see file name)

## Context

E8: SGLD with minibatches of `m` of `n` samples drawn without replacement, `w' = w − h t ∇L_B(w) + √(2h) ξ`. For quadratic per-sample losses
(linear regression) the per-sample gradient is affine, `∇lᵢ(w) = Hᵢ w − gᵢ` with `Hᵢ = xᵢxᵢᵀ` and `gᵢ` the per-sample gradient at the
least-squares point (`∑ᵢ gᵢ = 0`), so `∇L_B(w) = H_B w − g_B` with `H_B`, `g_B` the batch means. The note says the exact second moment then obeys
the Lyapunov law with the state-dependent term ("the full law is exact for this potential"). The seabed has the abstract full step
(`e8FullStep P h t C Hs H m X = fullStep (ulaStep P h) (minibatchNoise h t C) (fun i => Hs i − H) (minibatchCoeff h t m n) X`, tide
`fullstep-contraction`) and, since the previous tide, the finite population correction in bilinear cross form (`fpc_bilinear₂`) and the
E8 constants. Nothing connects the sampler's random update to `e8FullStep`.

## Candidates v1 (Claude)

**A. The one-step recursion, exactly.** With `A = 1 − h t H` (`= ulaStep (t • H) h`), `c = (1 − m/n)/(m(n−1))`, `E_B` the uniform average over
`m`-subsets and `E_ξ` the standard Gaussian expectation on `ι → ℝ` (density `gaussianWeight (matCLM 1)`, entrywise for matrices):

1. `gauss_second_moment_affine`: `E_ξ[(μ + s ξ)(μ + s ξ)ᵀ] = μμᵀ + s² • 1` and `E_ξ[μ + s ξ] = μ` (first moments vanish, second moments are `δᵢⱼ`, from tides `gaussian-moments-posdef`/`localised-bias` with `P = 1`).
2. `minibatch_mean_step`: `E_B E_ξ[w'] = A w` (unbiasedness of the batch mean, `sum_powersetCard_sum`).
3. `minibatch_second_moment_step` (the pointwise identity):
   `E_B E_ξ[w' w'ᵀ] = A (wwᵀ) Aᵀ + 2h • 1 + h²t² c ∑ᵢ vecMulVec ((Hᵢ − H) w − gᵢ) ((Hᵢ − H) w − gᵢ)`,
   because `(H_B − H) w − g_B = mean_B a − ā` for the single family `aᵢ = Hᵢ w − gᵢ`, so one application of `fpc_bilinear` (with `β = vecMulVec`) gives the whole quadratic term, and the linear cross terms `E_B[(H_B − H) w − g_B] = 0` vanish.
4. `minibatch_law_step` (the law form): for a probability measure `μ` on `ι → ℝ` with `∫ w = 0`, `∫ wᵢwⱼ = Σᵢⱼ` and the obvious integrability,
   `∫ E_B E_ξ[w' w'ᵀ] dμ(w) = e8FullStep (t • H) h t C_g Hs H m Σ` with `C_g = c ∑ᵢ gᵢgᵢᵀ` (`minibatch_gradient_cov` at the least-squares point): expanding the quadratic term, the `(Hᵢ − H) w gᵢᵀ` cross terms integrate to `0` and `(Hᵢ − H) wwᵀ (Hᵢ − H)ᵀ` to `(Hᵢ − H) Σ (Hᵢ − H)ᵀ`, i.e. `minibatchCoeff • stateTerm`. Hence a centred stationary law with second moment `Σ` satisfies `Σ = e8FullStep Σ`: the note's full law, constants included, is the exact stationary equation; by `FullStep.lean` its solution is unique and PSD.

Rationale: closes the E8 arc; the only new analysis is bookkeeping (the Gaussian step and the finite average), everything else is landed. Closed forms as stated (numerical check below).

**B. The same with the Gaussian noise handled through Mathlib's `stdGaussian` measure and `multivariateGaussian` (tides `ula-invariance`/`sampler-bridges` style random maps)** — cleaner probabilistically but mixes the density world (`fpc`, `gaussianWeight`) with the measure world; more bridging, same content.

**C. Only 1–3** (pointwise identity, no law form): leaves the connection to `e8FullStep` implicit. Too timid.

Claude's preference: A.

## Numerical check

`scratchpad/numcheck16.py`: linear regression `n = 6`, `m = 2`, `d = 2`, `h = 0.05`, `t = 3`, residuals projected so that `∑ᵢ xᵢεᵢ = 0`;
exhaustive average over the 15 batches, Gaussian step analytically. `‖E[w'w'ᵀ] − pred‖_max = 1.3e-15` with `pred` the expanded form
`A wwᵀ Aᵀ + 2hI + h²t²(C_g + c∑(Hᵢ−H)wwᵀ(Hᵢ−H)ᵀ − cross − crossᵀ)`, `cross = c ∑ᵢ (Hᵢ − H) w gᵢᵀ` (the signs of the cross terms are as in the
single-family form of A.3); `‖E[w'] − A w‖ = 2e-16`; the cross finite population correction to 2e-17.

## GPT-6 Astra v1

Saved verbatim in `gpt_minibatch_step_v1.md`. Summary: A.1–A.4 correct (`n ≥ 2`, `1 ≤ m ≤ n`, `h ≥ 0`, `H = popMean Hs`, `∑ gᵢ = 0`; fresh
uniform batches, Gaussian noise independent of batch and state); the single-family application of `fpc_bilinear` is "exactly right"; with
`rᵢ = Dᵢw − gᵢ` the conditional second moment is `AwwᵀAᵀ + 2hI + h²t²c ∑ rᵢrᵢᵀ`, the cross terms `−Dᵢwgᵢᵀ − gᵢwᵀDᵢᵀ` vanish under a centred
law, and the match with `e8FullStep` is exact given `ulaStep P h = 1 − h•P` and `minibatchNoise = 2h•1 + h²t²•C` (both confirmed in
`ULA.lean`); `fullLinear` uses `A * X * Aᵀ`. Convention note: `gᵢ` is minus the per-sample gradient at `w*` (covariance unchanged).
Lean: entrywise scalar integrals, prove integrability of constants/coordinates/products before distributing, one reusable entry lemma for
`(A X Aᵀ)ᵢⱼ = ∑ₖ∑ₗ Aᵢₖ Xₖₗ Aⱼₗ`, `Real.sq_sqrt` for `s = √(2h)`; define the vector expectation separately. Strengthening adopted: the joint
affine recursion `q' = Aq`, `M' = e8FullStep M − h²t²c ∑ᵢ (Dᵢ q gᵢᵀ + gᵢ qᵀ Dᵢᵀ)` for a law with mean `q` and raw second moment `M`; the
centred subspace is invariant, which is why second moments close. Uniqueness of the stationary second moment stays conditional on
`FullStep.lean`'s contraction hypotheses (not claimed as uniqueness of the stationary law). Votes **A** with the joint recursion.

## Vote
- Claude: candidate A (with the joint mean/second-moment recursion)
- GPT-6 Astra: candidate A (same)

Agreed.

## Result

Committed as `Laplace/Sampler/MinibatchStep.lean` (f582f62), 521 lines, 0 sorries, `lean-state check` clean.

Theorems: Gaussian step `stdExp`, `stdExp_const`, `stdExp_coord`, `stdExp_coord_mul`, `stdExp_affine`, `stdExp_affine_mul`,
`stdExpVec`, `stdExpMat`, `stdExpVec_affine`, `stdExpMat_affine`; batch averages `batchAvg`, `batchAvg_const`, `batchAvg_add`,
`batchAvg_sub`, `batchAvg_smul`, `batchAvg_batchMean` (unbiasedness), `batchAvg_batchMean_sub`; the step `minibatchGrad`, `sgldStep`,
`popMean_affine`, `ulaStep_mulVec`, `sgld_mean_step`, `residual_eq`, `vecMulVec_mulVec_mulVec`, `sgld_second_moment_step`;
law form `mul_mul_transpose_apply`, `vecMulVec_mulVec_left_apply`, `vecMulVec_mulVec_right_apply`, `vecMulVec_residual`, the entry
integrability/integral lemmas, `sgld_law_step` (joint mean/second-moment form), `sgld_law_step_centred`, `sgld_step_law_centred`
(`= e8FullStep`).

Surprises: the single-family trick made the second-moment step a one-line use of `fpc_bilinear`; the only friction was `abel` versus
`module` for smul-distributed expansions and the usual lambda-typed integrability facts for `integral_add`. With this the E8 arc is
closed at the level of the recursion: the note's full law with its constants is the exact stationary equation on linear regression.
