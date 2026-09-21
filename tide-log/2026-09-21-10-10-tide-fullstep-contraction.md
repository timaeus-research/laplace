# Tide: fullstep-contraction

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." Continuing the Sanity on Sampling programme (E8, "full law"): the state-dependent minibatch covariance law as the fixed point of an affine contraction on matrices: existence, uniqueness, positive semidefiniteness, convergence of the iteration the note uses, and domination of the additive Lyapunov law.
**Seabed:** laplace, commit 649efcc (origin/main at tide start)
**Started:** 2026-09-21T05:46Z
**Worktree / branch:** learning-theory/lean/laplace-tide-fullstep-contraction, tide/fullstep-contraction
**Retrospective:** skipped by user instruction for this auto run.

## Seabed snapshot

- `Laplace/Sampler/Lyapunov.lean` (`covStep`, spectral fixed point, finite-time identity), `ULA.lean`, `GaussianInvariance.lean` (`covStep_posSemidef`), `GaussianUniqueness.lean` (matrix limits, `tendsto_covStep_iterate`).
- Mathlib: `ContractingWith` API, scoped matrix norms, `Matrix.PosSemidef`.

## Candidates v1 (Claude)

Verbatim in `tide-log/gpt_fullstep_prompt_v1.md`: **F** the full law `Σ = AΣAᵀ + N + c Σ_i D_i Σ D_iᵀ` as an affine contraction: F1 unique fixed point and convergence of iterates under a Lipschitz contraction of the linear part, F2 a checkable ∞-operator-norm sufficient condition, F3 PSD of the fixed point, F4 domination of the additive law, F5 first-order lower bound on the inflation.

## Numerical check

The note's E8 solved the full law by the same iteration for linear regression (`d ≤ 50`) and found it exact against the sampled covariance; the domination `Σ_full ⪰ Σ_add` is what E8 observed as the additive law undershooting.

## GPT-6 Astra v1

Verbatim in `tide-log/gpt_fullstep_v1.md`. Summary: F1–F5 correct; F1 needs only the contraction (no positivity), F4/F5 take a *PSD* additive fixed point as input (discharged in the F2 corollary since the additive map contracts whenever the full one does); do not replace `‖Aᵀ‖` by `‖A‖` in the ∞-operator norm (transposition is not an isometry there); F5 needs no limit: `Δ - c·stateTerm S = L Δ ⪰ 0` from the fixed-point difference identity; PSD-cone closedness as a reusable lemma (entrywise symmetry + quadratic forms, continuity via `LinearMap.continuous_of_finiteDimensional` because the operator-norm topology instance need not be syntactically the Pi topology); use `PosSemidef (Y - X)` rather than a Loewner-order API; avoid the side quests (Loewner API, additive stability from arbitrary-norm contraction, deriving the law from the stochastic model). Vote: F1–F5 with the ∞-operator norm and a supplied PSD additive fixed point.

## Integration (Claude)

Accepted as is: ∞-operator norm (`open scoped Matrix.Norms.Operator`), Lipschitz constant `‖A‖‖Aᵀ‖ + c Σ ‖Dᵢ‖‖Dᵢᵀ‖`, completeness from finite dimension, `posSemidef_of_tendsto` as the reusable closedness lemma, F5 by the direct identity.

## Vote
- Claude: F1–F5.
- GPT-6 Astra: F1–F5.

Agreed after one round.
