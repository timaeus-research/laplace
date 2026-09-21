# Tide: estimator-variance

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"; "Continue with what you think best, don't stop"). Chosen: E4 of the Sanity on Sampling note, the variance of the directional variance / LLC estimator along an eigendirection: the Gaussian fourth-moment (Isserlis) identity for the AR(1)/ULA chain, `Var(1/N sum x_k^2) <= 2 sigma^4 (1+rho^2)/(N (1-rho^2))`, and the ULA realisation `<= 2 sigma^4/(h p C N)`.
**Seabed:** laplace, commit 39b1312 (branch tide/direction-closures, chained)
**Started:** 2026-09-21-14-42 UTC

## Context

The note's E4 ("chains, draws and dimension") says the Monte Carlo error of the pooled covariance follows `sqrt(d/(CN))` "with a prefactor set by the
autocorrelation times", and that the LLC is far cheaper than the covariance. The seabed has the second-order structure of the ULA chain along an
eigendirection (`AR1Chain` in a Hilbert space, realised in `L^2(Omega)` by `realChain`/`ulaChain`, `expected_pooled_sample_variance_ula`) and, from
the `direction-closures` tide, the Toeplitz bound `toeplitz_sum_le` and the shortfall bound. Nothing in the seabed is fourth-order on the sampler side;
the Gaussian Wick/Isserlis machinery of `GaussianWickPosDef` is for densities on `iota -> R`, not for chains.

## Candidates v1 (Claude)

**A (main). The estimator-variance law along an eigendirection.**
- A1 (abstract Isserlis family). For a finite family `f_a` (`a in s`) of square-integrable centred variables with
  `E[f_a^2 f_b^2] = E[f_a^2] E[f_b^2] + 2 E[f_a f_b]^2` for all `a, b` (the Gaussian fourth-moment identity),
  `Var(q sum_a f_a^2) = 2 q^2 sum_{a,b} E[f_a f_b]^2`.
- A2 (AR(1) window). For `AR1Chain E rho v` with `0 <= rho < 1`, `sigma^2 = v/(1-rho^2)`, `<x_k, x_l> = sigma^2 (rho^{|k-l|} - rho^{k+l})`
  so `0 <= <x_k,x_l> <= sigma^2 rho^{|k-l|}`, hence `sum_{k,l in window} <x_k,x_l>^2 <= sigma^4 T_N(rho^2) <= sigma^4 N (1+rho^2)/(1-rho^2)`
  (`toeplitz_sum_le` at `rho^2`). Different chains are orthogonal (`inner_x_x_of_orthogonal`), so for the pooled uncentred second-moment estimator
  `S = (1/(CN)) sum_c sum_{i<N} (x^c_{b+1+i})^2`: `Var S = (2/(C^2 N^2)) sum_c sum_{k,l} <x^c_k,x^c_l>^2 <= 2 sigma^4 (1+rho^2)/(C N (1-rho^2))`.
- A3 (discharging the Isserlis hypothesis). For independent centred `g_a` with `E g_a^2 = 1`, `E g_a^3 = 0`, `E g_a^4 = 3`, and
  `X = sum a_i g_i`, `Y = sum b_i g_i` (finite sums): `E[X^2 Y^2] = |a|^2 |b|^2 + 2 <a,b>^2`. Proof by induction on the index Finset: adding
  an independent `g`, `E[(X+ag)^2 (Y+bg)^2] = E[X^2Y^2] + b^2 E X^2 + 4ab E[XY] + a^2 E Y^2 + 3a^2b^2`. The realised chain `realChain rho eta`
  with iid innovations `eta_a = sqrt(v) g_a` is such a linear combination (`x_eq_sum`), so its window satisfies A1's hypothesis.
- A4 (ULA). Along a unit eigenvector (`Q u = p u`, `rho = 1 - hp`, `0 < hp <= 1`): `(1+rho^2)/(1-rho^2) <= 1/(hp)`
  (equivalent to `(hp)^2 <= hp`), so `Var S <= 2 sigma^4/(h p C N)` with `sigma^2 = 2h/(1-(1-hp)^2)`; i.e. the relative standard error of a
  directional variance is at most `sqrt(2/(h p C N)) = sqrt(tau_flat/(CN))`, the "prefactor set by the autocorrelation time".
- A5 (needed for A4 from A3). The projected innovations `sqrt(2h) <u, xi_a>` for `xi_a ~ stdGaussian (EuclideanSpace R iota)` iid: need
  `E <u,xi>^3 = 0` and `E <u,xi>^4 = 3 |u|^4`. Route unclear in Mathlib (Sep 2026 pin): via `IsGaussian`/`HasGaussianLaw` + `gaussianReal` moments, or
  via the coordinates being iid `gaussianReal 0 1` under `Measure.pi` and A3 itself with `a = b = u`.

**B (cheap companion). Burn-in-only bias of the loss-based LLC running mean.** On the quadratic potential the running mean of `t K` over draws
`b+1..b+N` has expectation `(1/2) sum_i p_i sigma_i^2 (1 - rho_i^{2(b+1)} (1-rho_i^{2N})/(N (1-rho_i^2)))`; the shortfall from the ULA LLC has no
`1/(CN)` term (no mean subtraction), which is why "the LLC is far cheaper than the covariance". Plus the `20 kappa` corollary of the
`direction-closures` bound: with `h p_max = 1/10`, the flattest direction's relative shortfall term is `2/(h p_min C N) = 20 kappa/(CN)`.

**C (follow-up, not this tide).** The full Frobenius law `E |Sigma_hat - Sigma|_F^2 = sum_{ij} sigma_i^2 sigma_j^2 T_N(rho_i rho_j)/N^2 + sum_i sigma_i^4 T_N(rho_i^2)/N^2`
needs independence across eigendirections of the same Gaussian noise; too much new infrastructure.

## Numerical check

`numcheck20.py`: Monte Carlo variance of the pooled uncentred second moment against the exact zero-start formula
`2 s2^2/(C N^2) sum_{i,j<N} (rho^{|i-j|} - rho^{2(b+1)+i+j})^2` and the bound `2 s2^2 (1+rho^2)/(C N (1-rho^2))`:
`rho=0.9, N=200, C=2, b=20`: MC 1.2809, exact 1.2875, bound 1.3194; `rho=0.5, N=50, C=1, b=0`: MC 0.1171, exact 0.1158, bound 0.1185;
`rho=0.98, N=400, C=4, b=40`: MC 36.91, exact 36.12, bound 39.46. Isserlis for linear combinations of 5 iid Gaussians: 9.074 (MC) vs 9.055.
`(1+rho^2)/(1-rho^2) <= 1/(hp)` at `hp = 0.05, 0.3, 0.9, 1`.

## GPT-6 Astra v1

Saved verbatim in `gpt_estimator_variance_v1.md`. Summary: A1–A4 correct (factor 2 right; `<x_k,x_l> = s2 rho^{l-k}(1-rho^{2k})` in `[0, s2 rho^{l-k}]`;
`(1+rho^2)/(1-rho^2) <= 1/(hp)` iff `(hp)^2 <= hp`, indeed `1/t - (1+(1-t)^2)/(1-(1-t)^2) = (1-t)/(2-t)`). Qualifications: square-integrability
is not enough, take `MemLp (f a) 4 P` as the public hypothesis and package the product-integrability facts; the Wick identity must hold
across the whole pooled family (orthogonality alone does not make squares uncorrelated); the bound is relative to the stationary
variance `s2`, is a variance (not MSE) bound, and `S` is the pooled *uncentred* second moment, not the sample variance; do not
advertise the directional theorem as the full LLC variance law. A3: Finset induction is sound; use the *pair* `(X, Y)` when composing
with the block independence (separate independence of `X` and `Y` from `g_n` does not give independence of `XY`); a four-index Wick
table is the fallback. A5: prefer 1-D Gaussian transport (`stdGaussian` pushed forward by a continuous linear functional is
`gaussianReal 0 |u|^2`) over rebuilding coordinate independence; if the API fails, a theorem with explicit projected fourth-moment
hypotheses is a legitimate endpoint but must be labelled as conditional. Include the exact zero-start formula. Ladder: (1) abstract
family identity, (2) AR(1) squared-inner bound, (3) pooled theorem under a window Wick hypothesis, (4) ULA algebra, (5) independent-
innovation fourth-moment theorem applied to `realChain`, (6) Gaussian discharge. Leave C out; B only if cheap. **Vote: A.**

## Vote
- Claude: candidate A (ladder (1)–(6), with the Gaussian discharge attempted in this tide)
- GPT-6 Astra: candidate A

Agreed.

## Result

Committed as `468ecb7` on `tide/estimator-variance` (`Laplace/Sampler/EstimatorVariance.lean`, 711 lines; full `lake build` and
`scripts/sorries` clean: 0 sorry, 0 axiom, 0 native_decide).

Theorems: `holderTriple_four_four_two`, `memLp_two_mul_of_memLp_four`, `integrable_mul_mul_mul_of_memLp_four`,
`integrable_sq_mul_sq_of_memLp_four`, `integrable_mul_of_memLp_four`, `integrable_sq_of_memLp_four`; `IsserlisFamily`,
`variance_sum_sq_of_isserlis`; `memLp_realChain_of_memLp`, `integral_realChain_mul_realChain`, `pooled_second_moment_variance`,
`pooled_second_moment_variance_le`; `IsLinComb` (+ `zero`, `add`, `const_mul`, `of_mem`), `measurable_of_isLinComb`,
`memLp_of_isLinComb`, `FourthMomentTable`, `indepFun_pair_of_isLinComb`, `integral_mul_pow_of_isLinComb`, `integral_linComb_mul`,
`integral_linComb_sq_mul_sq`, `FourthMomentTable.white`, `isserlisFamily_of_isLinComb`, `isLinComb_realChain`;
`integral_pow_gaussianReal_zero_one`, `integral_pow_three_gaussianReal`, `integral_pow_four_gaussianReal`,
`map_innerSL_eq_gaussianReal`, `integral_inner_pow_of_stdGaussian`, `memLp_four_inner_of_stdGaussian`; `fourthMomentTable_projNoise`,
`ula_second_moment_variance`, `ula_second_moment_variance_le`.

Surprises: the Isserlis induction is cleanest with the terms grouped by powers of the new innovation as products of exactly four
`L^4` factors (one Hölder helper covers every integrability side goal) and with the `(X, Y)` pair independent of `g_n` (GPT's point);
the Gaussian discharge went through Mathlib's `HasGaussianLaw` in ~30 lines once `variance_map` was given its measure explicitly. The
only real friction was syntactic: `Finset.sum_coe_sort` is not a higher-order pattern for `simp`, and `Measurable.comp` terms carry a
`∘` that `integral_map`/`memLp_map_measure_iff` patterns will not match.
