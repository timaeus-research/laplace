# Tide: llc-closures

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"; "Continue with what you think best, don't stop"). Chosen: the LLC-side closures of the Sanity on Sampling note: the minibatch LLC inflation in the eigenbasis (E8, conclusion item 2, "inflated by about lr t^2 tr(C_g)/(2d)"), the burn-in-only bias of the loss-based LLC running mean (E4, "the LLC is far cheaper than the covariance"), and the `20 kappa` corollary of the finite-chain shortfall bound.
**Seabed:** laplace, commit 39b1312 (branch off main)
**Started:** 2026-09-21-15-51 UTC

## Context

The seabed has the minibatch Lyapunov law in the eigenbasis (`minibatchCov_conj_diag`: the ULA variance times `1 + h t^2 c_i/2`, `c_i = (U^T C U)_ii`),
the ULA LLC `ula_llc = 1/2 sum_i 1/(1 - h p_i/2)` with `trace_mul_ulaCov` as the trace-in-the-eigenbasis template, the transient
`llc_ula_trajectory` at the measure level, the eigenvector columns `orthoCol` (`mulVec_orthoCol`, `norm_orthoCol`), the projected chain
`inner_ulaChain_eq_realChain` with the Gram table `norm_x_sq` (`|x_k|^2 = s2 (1 - rho^{2k})`), and from `direction-closures` the shortfall bound
`stationary_sub_pooledSampleVariance_le` with the `(1+rho)/((1-rho) C N)` term.

## Candidates v1 (Claude)

**A. The minibatch LLC in the eigenbasis (E8).** With `P = t H` positive definite, `0 < h`, `h p_i < 2`, and `C` positive semidefinite, let
`Sigma_mb = lyapunovVia U (1 - h p) (2h I + h^2 t^2 C)` (the unique fixed point of the minibatch covariance step, `minibatch_fixed_iff`). Then
`(t/2) tr(H Sigma_mb) = 1/2 sum_i (1 + h t^2 c_i/2)/(1 - h p_i/2)` with `c_i = (U^T C U)_ii >= 0`, so the inflation over the ULA LLC is
`(h t^2/4) sum_i c_i/(1 - h p_i/2)`, and since `sum_i c_i = tr C`,
`(h t^2/4) tr C <= LLC_mb - LLC_ULA <= (h t^2/4) tr C/(1 - h p_max/2)`. Relative to `d/2`: between `h t^2 tr C/(2d)` and
`h t^2 tr C/(2d (1 - h p_max/2))`, the note's "inflated by about `lr t^2 tr(C_g)/(2d)`" with a two-sided error.

**B. The burn-in-only bias of the loss-based LLC running mean (E4).** For the ULA chain `x_k` from the mode with independent standard
Gaussian noise (`ulaChain`), `<x, H x> = sum_i lambda_i <u_i, x>^2` in the eigenbasis (`u_i = orthoCol`), and `E <u_i, x_k>^2 = s2_i (1 - rho_i^{2k})`
with `rho_i = 1 - h p_i`, `s2_i = 2h/(1 - rho_i^2)`, so `t E[1/2 <x_k, H x_k>] = 1/2 sum_i (1 - rho_i^{2k})/(1 - h p_i/2)` and the expected pooled
running mean over `C` chains and draws `b+1..b+N` is
`1/2 sum_i (1 - rho_i^{2(b+1)} (1 - rho_i^{2N})/(N (1 - rho_i^2)))/(1 - h p_i/2)`; its shortfall from the ULA LLC is
`1/2 sum_i rho_i^{2(b+1)} (1 - rho_i^{2N})/(N (1 - rho_i^2) (1 - h p_i/2)) <= 1/2 sum_i rho_i^{2(b+1)}/(N (1 - rho_i^2)(1 - h p_i/2))`: burn-in
only, no `1/(CN)` autocorrelation term, because the loss-based estimator subtracts no sample mean.

**C. The `20 kappa` corollary.** In `stationary_sub_pooledSampleVariance_le`/`expected_pooled_sample_variance_ula_shortfall`, along the flattest
direction `p_min = p_max/kappa` with `h p_max = 1/10`: `2/(h p_min C N) = 20 kappa/(C N)`; so `CN = 20 kappa M` pooled draws make the
autocorrelation term of the relative shortfall at most `1/M`.

Proposed: A + B + C in one module `Laplace/Sampler/LLCClosures.lean` (~400 lines).

## Numerical check

`numcheck21.py` (`d = 4`, `t = 50`, `h = 0.1/p_max`, random PD `H`, PSD `C`): A. the Lyapunov fixed point iterated to convergence gives
`LLC_mb = 8.210708` against the eigenbasis formula `8.210708`; inflation `6.155` in `[6.017, 6.333]`; normalised inflation `3.078` against
`h t^2 tr C/(2d) = 3.008`. B. Monte Carlo of the pooled loss-based LLC running mean of the ULA chain from the mode (`b = 5`, `N = 40`, `C = 3`,
20000 replicas): `1.6497` against the predicted `1.6485`; ULA LLC `2.0557`; shortfall `0.407 <= 0.468`. C. `2/(h p_min C N) = 20 kappa/(CN)`
to machine precision.

## GPT-6 Astra v1

Saved verbatim in `gpt_llc_closures_v1.md`. Summary: A correct with the noise convention `2h I + h^2 t^2 C_g` (`C_g` before the `t`
scaling); prove the exact identity without PSD and use PSD only in the inequality layer; the `d/2`-normalised bounds are inflation
normalised by the continuous-target LLC, not `Delta/LLC_ULA`, and the total inflation above `d/2` also contains the ULA discretisation
bias. B correct: `s2_i p_i = 1/(1 - h p_i/2)`; the pooled expectation needs no independence across chains, only marginals; "burn-in only"
is relative to the ULA stationary LLC. C correct; the exact factor is `(1+rho)/(1-rho) = 20 kappa - 1`, so `20 kappa` is slightly
conservative; state the budget as `CN >= 20 kappa M`; it controls the autocorrelation contribution only. Lean: matrix route for the
quadratic form (no `OrthonormalBasis`), on `iota -> R` first then a thin Euclidean wrapper; diagonalise `P` and convert to `t/2 <x,Hx>` at
the boundary; for B use the Omega-level projection/AR(1) infrastructure (no marginal-law bridge exists), with the geometric sum as a pure
algebra lemma; 400 lines is optimistic. Addition: the remainder bound `0 <= Delta - L0 <= L0 (h p_max/2)/(1 - h p_max/2)`,
`L0 = (h t^2/4) tr C`, which makes "about" precise. **Vote: A+B+C.**

## Vote
- Claude: A+B+C with the remainder bound
- GPT-6 Astra: A+B+C

Agreed.
