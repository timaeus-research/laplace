# Tide: ula-invariance

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." Continuing the Sanity on Sampling programme in the laplace seabed: the probabilistic statement behind the ULA law, that `N(0, Σ_ULA)` is invariant under one ULA step on a Gaussian target (the law of `A X + √(2h) ξ` for `X ~ N(0, Σ)` is `N(0, A Σ Aᵀ + 2h I)`).
**Seabed:** laplace, commit 2f9576e (origin/main at tide start; the tide `sanity-chain-forms` is being merged in parallel)
**Started:** 2026-09-21T05:08Z
**Worktree / branch:** learning-theory/lean/laplace-tide-ula-invariance, tide/ula-invariance
**Retrospective:** skipped by user instruction for this auto run.

## Seabed snapshot

- `Laplace/Sampler/Lyapunov.lean`, `Laplace/Sampler/ULA.lean`: the covariance recursion and its fixed point (`ulaCov_fixed`, `ulaCov_posDef`), spectral packaging.
- Nothing probabilistic in the seabed. Mathlib: `multivariateGaussian` on `EuclideanSpace ℝ ι`, `IsGaussian` with `isGaussian_map`, `isGaussian_conv`, `IsGaussian.ext`, `covarianceBilin_map`, `charFun_conv`, `Matrix.toEuclideanCLM`.

## Candidates v1 (Claude)

Verbatim in `tide-log/gpt_ula_invariance_prompt_v1.md`: **A** Gaussian invariance of the ULA step (A1 law of `A X + √(2h) ξ`, A2 push-forward of a centred Gaussian by a matrix, A3 invariance of `N(0, Σ_ULA)`, A4 optional Markov-kernel/bind form); **B** (stretch) the L² instantiation of the AR(1) chain theorem.

## Numerical check

Not feasible in the usual sense (an identity of measures); the covariance identity `A Σ_ULA A + 2h I = Σ_ULA` behind A3 was checked numerically in the sampler-laws tide (fixed-point residual 2.4e-15).

## GPT-6 Astra v1

Verbatim in `tide-log/gpt_ula_invariance_v1.md`. Summary: A1–A3 correct; generalise the noise to an arbitrary PSD `R` (`(N(0,Σ).map L_A) ∗ N(0,R) = N(0, AΣAᵀ + R)`, no hypothesis on `A`; `0 ≤ h` suffices for `R = (2h)•1`); keep the PSD hypotheses explicit because `multivariateGaussian` degenerates to a Dirac mass off the PSD cone; route: A2 (push-forward) by `IsGaussian.ext` with `integral_id_map`, `covarianceBilin_map`, `covarianceBilin_multivariateGaussian`, the adjoint identity from `map_star` of the star-algebra equivalence `toEuclideanCLM`; the convolution of centred Gaussians by `Measure.ext_of_charFun` + `charFun_conv` + `charFun_multivariateGaussian`; separate the probabilistic invariance statement (hypotheses: PSD, `0 ≤ h`, the fixed-point equation) from its spectral discharge (`ulaCov_posDef`, `ulaCov_fixed`); defer the kernel/bind form and the L² bridge; stretch target: the finite-time Gaussian marginal law `μ_n = N(0, Σ_n)` by induction, and the non-centred generalisation `(N(m,Σ).map L_A) ∗ N(b,R) = N(L_A m + b, AΣAᵀ + R)`. Vote: A2 + general-R A1 + A3, finite-time marginal law as the sole stretch.

## Integration (Claude)

Accepted: general PSD `R` and general means from the start (the same proofs), the invariance theorem in two layers, the finite-time marginal law `(step)^[n] (N(m₀, Σ₀)) = N(A^n m₀, (covStep A R)^[n] Σ₀)` as the stretch. Kernel/bind form and the L² bridge deferred (recorded as follow-ups).

## Vote
- Claude: A (push-forward, convolution, invariance) + finite-time marginal law.
- GPT-6 Astra: the same.

Agreed after one round.

## Result

- Commit `c743ce6` on `tide/ula-invariance` (base 2f9576e), merged with upstream in `73d002f`. Full `lake build` green; `scripts/sorries`: 0 sorry, 0 axiom, 0 native_decide.
- `Laplace/Sampler/GaussianInvariance.lean` (     172 lines): `euclid` (= `toEuclideanCLM`), `euclid_adjoint`, `euclid_pow`, `euclid_mul`, `dotProduct_conj_mulVec`, `posSemidef_conj`, `covStep_posSemidef`, `covStep_iterate_posSemidef`, `multivariateGaussian_map_euclid` (`N(m,S).map A = N(Am, ASAᵀ)`), `multivariateGaussian_conv` (`N(m,S) ∗ N(b,R) = N(m+b, S+R)`), `multivariateGaussian_map_conv`, `invariant_of_covStep_fixed`, `ulaCov_invariant`, `gaussStep`, `gaussStep_iterate` (finite-time marginal law), `gaussStep_iterate_zero`.
- Surprises: none mathematical; the whole module went through in three check rounds. Mathlib's API was exactly sufficient (`IsGaussian.ext`, `covarianceBilin_map`, `charFun_conv`, `Measure.ext_of_charFun`); the only friction was `Σ` being a reserved token and `ContinuousLinearMap.mul_apply` being deprecated.
