# Tide: gaussian-quadratic

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." Continuing the Sanity on Sampling programme: Gaussian quadratic expectations in measure form, `E_{N(m,S)}[⟨x, Hx⟩] = tr(HS) + mᵀHm`, and hence the sampler's ULA-corrected LLC as an expectation under the invariant law `N(0, Σ_ULA)` versus `d/2` under the Gibbs law.
**Seabed:** laplace, commit f09c739 (origin/main at tide start; `ula-eigendirection` being merged in parallel)
**Started:** 2026-09-21T06:07Z
**Worktree / branch:** learning-theory/lean/laplace-tide-gaussian-quadratic, tide/gaussian-quadratic
**Retrospective:** skipped by user instruction for this auto run.

## Seabed snapshot

- `Laplace/Sampler/ULA.lean` (`trace_mul_ulaCov`, `ula_llc`), `GaussianInvariance.lean`/`GaussianUniqueness.lean` (the invariant law), `Laplace/Multi/GaussianLLC.lean` (integral form with the seabed's hypothesis package).
- Mathlib: `covarianceBilin_multivariateGaussian`, `integral_id_multivariateGaussian`, `IsGaussian.memLp_two_id`.

## Candidates v1 (Claude)

Verbatim in `tide-log/gpt_gaussian_quadratic_prompt_v1.md`: **Q** Gaussian quadratic expectations (Q1 centred, Q2 with mean, Q3 the sampler's LLC under `N(0, Σ_ULA)` vs `d/2` under `N(0, P⁻¹)`, Q4 the coordinate second moments).

## Numerical check

The identity `E[⟨x,Hx⟩] = tr(HS)` was checked by Monte Carlo in the sampler-laws tide (0.6766 vs 0.6769 at 4·10⁵ draws); the ULA-corrected LLC values are the E1 measurements of the note.

## GPT-6 Astra v1

Verbatim in `tide-log/gpt_gaussian_quadratic_v1.md`. Summary: Q1–Q3 correct with no symmetry assumption on `H` (the identity `∑ H_ij S_ij = tr(HS)` uses the symmetry of the PSD `S`); make the second moments `∫ xᵢxⱼ = Sᵢⱼ + mᵢmⱼ` the reusable core (Q4 non-optional), derive Q2 by summation and Q1 at `m = 0`; state the ULA/Gibbs comparison under the admissibility hypotheses `P ≻ 0`, `h > 0`, `hp_i < 2` (each summand `> 1`, so the ULA LLC exceeds `d/2`); use basis-coordinate identities `⟪eᵢ, x⟫ = xᵢ` once; do not build on a guessed `covarianceBilin_apply'`. Vote: Q1–Q4 as one cluster, finite-time trajectories deferred.

## Integration (Claude)

Accepted; the centred second moments `∫ xᵢxⱼ = Sᵢⱼ` are the core (`covarianceBilin_apply` with `IsGaussian.memLp_two_id` and `integral_id_multivariateGaussian`); the mean version is added if cheap.

## Vote
- Claude: Q1, Q3, Q4 (+ Q2 if cheap).
- GPT-6 Astra: Q1–Q4.

Agreed after one round.
