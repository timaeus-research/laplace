# Tide: frobenius-law

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"; "Continue with what you think best, don't stop"). Chosen: the E4 whole-covariance law of the Sanity on Sampling note ("the covariance error follows `sqrt(d/(CN))` with a prefactor set by the autocorrelation times"), as a theorem about the pooled uncentred second-moment matrix of chains whose innovations form a `FourthMomentTable` across chains, times and eigendirections; the Gaussian discharge of that hypothesis for the ULA chain is the next tide.
**Seabed:** laplace, commit f9a634e (branch tide/wick4, chained)
**Started:** 2026-09-21-17-16 UTC

## Context

`wick4` gives `cov_mul_mul_of_isLinComb : E[(XY)(ZW)] - E[XY]E[ZW] = E[XZ]E[YW] + E[XW]E[YZ]` for linear combinations `X, Y, Z, W` over a
finite index set of a `FourthMomentTable g P v` (independent innovations, `L^4`, moments `(0, v, 0, 3v^2)`), and
`integral_four_of_isLinComb`. `estimator-variance` gives `IsLinComb` closure lemmas, `isLinComb_realChain`, `integral_realChain_mul_realChain`
(the Gram table `E[x^c_k x^{c'}_l] = δ_{cc'} s2 (ρ^{|k-l|} - ρ^{k+l})` for realised chains with white innovations), `pooled_second_moment_variance`
(the diagonal case). `direction-closures` gives `toeplitz_sum_le`, `sum_sum_pow_dist`. Mathlib: `iIndepFun.hasGaussianLaw_pi`,
`HasGaussianLaw.iIndepFun_of_covariance_inner`, `covarianceBilin_stdGaussian` (for the follow-up).

## Candidates v1 (Claude)

Setting: directions `i : ι` (finite), chains `c : Fin C`, innovations `η c k i : Ω → R` (`k : ℕ`), realised chains
`x c i := realChain (ρ i) (η c · i)`, the pooled uncentred second-moment matrix over draws `b+1..b+N`:
`Σ̂ i j ω = (1/(CN)) ∑_c ∑_{k<N} x c i (b+1+k) ω * x c j (b+1+k) ω`.

**A (assumption-light layer). The Frobenius decomposition.** For finitely many integrable-square random variables `S_ij` with means `m_ij`
and any targets `Σ_ij`: `E ∑_ij (S_ij - Σ_ij)^2 = ∑_ij Var(S_ij) + ∑_ij (m_ij - Σ_ij)^2` (with `Var S = E S^2 - (E S)^2`). Pure algebra plus linearity.

**B (the process layer). Per-entry variance under a four-moment table across chains, times and directions.** Hypothesis: the family
`(c, k, i) ↦ η c k i` (on `Fin C × ℕ × ι`) is a `FourthMomentTable` with variance `v`, hence white across all three indices
(`∫ η c k i η c' l j = δ δ δ v`). Then the Gram table is `∫ x c i k * x c' j l = δ_{cc'} δ_{ij} s2_i (ρ_i^{|k-l|} - ρ_i^{k+l})`, `s2_i = v/(1 - ρ_i^2)`
(same direction: `integral_realChain_mul_realChain`; different directions: orthogonal innovations ⇒ orthogonal chains), every window value is a
linear combination of the family, and `cov_mul_mul_of_isLinComb` gives
`Var(Σ̂ i j) = (1/(CN)^2) ∑_{c,c'} ∑_{k,l<N} [E(x_{cki} x_{c'li}) E(x_{ckj} x_{c'lj}) + E(x_{cki} x_{c'lj}) E(x_{ckj} x_{c'li})]
= (1 + δ_ij)/(C N^2) ∑_{k,l<N} G_i(k,l) G_j(k,l)`, `G_i(k,l) = s2_i (ρ_i^{|k-l|} - ρ_i^{k+l})` (shifted by `b+1`).

**C (E4). The whole-covariance law.** `E ∑_ij (Σ̂ i j - E Σ̂ i j)^2 = (1/(C N^2)) ∑_ij (1 + δ_ij) ∑_{k,l<N} G_i(k,l) G_j(k,l)` (exact, zero start), and the
stationary envelope for `0 ≤ ρ_i < 1`: `≤ (1/(CN)) ∑_ij (1 + δ_ij) s2_i s2_j (1 + ρ_i ρ_j)/(1 - ρ_i ρ_j)` (`toeplitz_sum_le` at `ρ_i ρ_j`): the
autocorrelation time of the *products*; relative to `|Σ_∞|_F^2 = ∑_i s2_i^2` this is the `sqrt(d/(CN))` law with the prefactor
`(∑_ij (1+δ_ij) s2_i s2_j τ(ρ_i ρ_j))/(d ∑_i s2_i^2)`; for equal directions `(d+1) τ(ρ^2)/(CN)`.

**D (follow-up, next tide).** The Gaussian discharge: for the ULA chain with independent standard Gaussian noise `ξ_{c,k}` and the orthonormal
eigenvectors `u_i = orthoCol i`, the family `√(2h) <u_i, ξ_{c,k}>` on a finite time window is a `FourthMomentTable` with `v = 2h`
(cross-direction independence from `HasGaussianLaw.iIndepFun_of_covariance_inner` + `covarianceBilin_stdGaussian`; cross-time from `hind`).

Proposed: A + B + C (conditional on the four-moment hypothesis, clearly labelled), one module `Laplace/Sampler/FrobeniusLaw.lean` (~500 lines).

## Numerical check

`numcheck25.py` (`d = 3`, `C = 2`, `N = 60`, `b = 10`, `h p_max = 0.3`, 6000 replicas of the pooled uncentred second-moment matrix of AR(1)
chains from zero in eigen-coordinates): `E|Σ̂ - E Σ̂|_F^2` Monte Carlo `16.746` against the exact zero-start formula
`∑_ij (1+δ_ij)/(C N^2) ∑_{k,l} G_i G_j = 16.417` (ratio 1.02); per-entry variance ratios MC/prediction between 0.995 and 1.026; the stationary
envelope `22.22 ≥ 16.42`.

## GPT-6 Astra v1

Saved verbatim in `gpt_frobenius_law_v1.md`. Summary: B and C correct with explicit hypotheses (`C, N > 0`, `0 ≤ ρ_i < 1`, `v ≥ 0`); the Wick
reduction gives `Cov(x_{cki} x_{ckj}, x_{c'li} x_{c'lj}) = 1_{c=c'} (1 + 1_{i=j}) G_i(k,l) G_j(k,l)` — the first pairing survives for every
pair of directions, the second only on the diagonal, cross-chain covariances vanish even on the diagonal because Wick subtracts the product
of means, and cross-direction orthogonality does not kill off-diagonal entries; the exponents must use the actual chain times
`b+1+k` (do not drop the burn-in shift); the envelope `(1/(CN)) ∑ (1+δ) s2_i s2_j τ(ρ_i ρ_j)` is right and "stationary envelope" is a good
name; the relative form is a bound on the *squared* relative error, its square root the RMS prefactor, `(d+1) τ(ρ^2)/(CN)` for equal
directions, an upper bound for finite zero-start windows. Prove both the centred exact law (core) and the stationary-target version with
the explicit diagonal zero-start bias `∑_i s2_i^2 a_i^2`, `a_i = (1/N) ∑_k ρ_i^{2(b+1+k)}`; wording: "sampling fluctuation follows the
square-root law, with an explicit initialisation-bias correction"; discretisation bias against a continuous target is a separate term.
Lean: architecture (b) with three layers (finite estimator algebra + Wick; Gram-kernel specialisation with `if i = j then 2 else 1`;
`realChain` instance), window-indexed values, explicit integrals rather than the `variance` API, pointwise covariance simplification by
`by_cases` before summing, cancel `C`, `N` last; the cross-direction Gram theorem is the substantive concrete addition. D plan confirmed
(finite window, `iIndepFun.hasGaussianLaw_pi`, CLM of projections, covariances by orthonormality/independence,
`iIndepFun_of_covariance_inner`, then scale by `√(2h)` with `0 ≤ h` and discharge the moments and `L^4`). **Vote: A+B+C** (conditional on
the four-moment hypothesis; centred exact law + stationary envelope as the core; explicit zero-start bias as the stationary-target
corollary; `sqrt(d/(CN))` as a relative RMS upper bound).

## Vote
- Claude: A+B+C with the stationary-target corollary (D next tide)
- GPT-6 Astra: A+B+C

Agreed.
