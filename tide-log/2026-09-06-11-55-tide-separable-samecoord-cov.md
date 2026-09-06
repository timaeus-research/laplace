# Tide: separable-samecoord-cov

**Direction (user):** Continue with what you think best (auto). Deliberately diversifying off the
(now-complete) monomial cumulant corner to a different KIND of result aligned with the project's
Stage-3 multivariate-covariance goal.
**Seabed:** laplace, commit cb76b5b (branch base)
**Started:** 2026-09-06

## Candidate

Same-coordinate covariance inherited from 1D under a separable Gibbs measure:
`Cov_2D(f∘fst, g∘fst) = Cov_U(f,g)` and `Cov_2D(f∘snd, g∘snd) = Cov_V(f,g)`. Companion to the
existing `gibbsCov_addSeparable_fst_snd_eq_zero` (cross-covariance vanishes) — together they say the
covariance matrix of `(f∘fst, g∘snd)` is BLOCK-DIAGONAL for separable potentials, the structural
input for the multivariate `Cov_t = (1/t)⟨∇φ, Σ∇ψ⟩` story (Σ separable = block-diagonal).

## Numerical check

Structural (not a numeric closed form); not feasible/needed. Correctness is by the factorisation
machinery: ⟨f(z.1)·g(z.1)⟩ = ⟨(f·g)⟩_U·⟨1⟩_V = ⟨f·g⟩_U, etc., so Cov collapses to the 1D Cov.

## Result

`Laplace/TwoD/SeparableSameCoordCov.lean` (NEW, leaf): `gibbsCov_addSeparable_fst_fst_eq` and
`gibbsCov_addSeparable_snd_snd_eq`. Zero-sorry, full build clean (8886 jobs), zero warnings.
Proof reuses `gibbsExpectation_separable_addSeparable`, collapsing the free coordinate with the
constant `1` (⟨1⟩=1 via `gibbsExpectation_const`) — the same idiom the cross-vanishing proof used.
Compiled first try. No GPT.

★ PROCESS LESSON: I first EXTENDED the core `AddSeparable.lean` — the maths compiled, but touching a
widely-imported file rebuilt ALL its dependents, surfacing their PRE-EXISTING missing-`Authors:`-header
warnings (QuarticSextic*, …) — an unavoidable cascade I shouldn't chase across many files. Fix:
relocated the two theorems to a NEW LEAF file importing AddSeparable, so nothing downstream rebuilds.
AddSeparable's own pre-existing lint (no header; unused Z≠0 hyps in gibbsExpectation_separable_addSeparable)
left untouched (out of scope). Recorded the cascade rule in CLAUDE.md.
