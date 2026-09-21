# Tide: frobenius-bridge

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: the Frobenius bridges that make E4's eigenbasis statements statements about matrix norms in the original coordinates (follow-up flagged by GPT-6 Astra in tide `frobenius-free`).
**Seabed:** laplace, main after `mh-reversible` (ebcd351); `GaussianTable.lean`, `LLCSensitivity.lean` (`orthoOf_transpose_inv_mul`), `LLCMSE.lean` (`memLp_four_inner_ulaChain`)
**Started:** 2026-09-21 (UTC, see filename)

## Context

Every E4 covariance theorem so far (`frobenius_ula_le`, `frobenius_ula_le_free`, …) is stated for the pooled second-moment matrix of the
*eigen-projections* `⟨uᵢ, x_k⟩`, and its Frobenius error is written as `∑ᵢⱼ (Σ̂ᵢⱼ − EΣ̂ᵢⱼ)²`; the "target norms" `‖Σ_ULA‖_F²`, `‖P⁻¹‖_F²` appear as
eigenvalue sums `∑ᵢ s₂ᵢ²`, `∑ᵢ 1/pᵢ²`. The note measures "the relative Frobenius error of the whole covariance" in the coordinates the chain
runs in. The missing bridge is the orthogonal invariance of the Frobenius norm: the eigen-projected estimator is `Uᵀ Σ̂_raw U` pointwise, and
`∑ᵢⱼ (UᵀAU)ᵢⱼ² = ∑ᵢⱼ Aᵢⱼ²`.

## Candidates v1 (Claude)

With `U = orthoOf hQ` (`Uᵀ U = 1 = U Uᵀ`):

**A. Frobenius algebra.** `sum_sq_eq_trace : ∑ᵢⱼ Aᵢⱼ² = tr(AᵀA)`; `sum_sq_conj : ∑ᵢⱼ (UᵀAU)ᵢⱼ² = ∑ᵢⱼ Aᵢⱼ²`; `sum_sq_diagonal : ∑ᵢⱼ (diag d)ᵢⱼ² = ∑ᵢ dᵢ²`.

**B. The target norms.** `frobenius_ulaCov : ∑ᵢⱼ (Σ_ULA)ᵢⱼ² = ∑ᵢ (1/(pᵢ(1 − h pᵢ/2)))²` and `frobenius_inv : ∑ᵢⱼ (P⁻¹)ᵢⱼ² = ∑ᵢ 1/pᵢ²` — so the
denominators of tides `frobenius-free` / `llc-variance` are `‖Σ_ULA‖_F²` and `‖P⁻¹‖_F²` in the original coordinates.

**C. The estimator bridge.** For any vector chain `y`, the pooled second-moment matrix of the eigen-projections is the conjugate of the raw one,
pointwise in `ω`: `Σ̂_eig(ω) = Uᵀ Σ̂_raw(ω) U` (`pooledSecondMoment_inner_eq`), hence `Σ̂_raw = U Σ̂_eig Uᵀ`, `E Σ̂_raw = U (E Σ̂_eig) Uᵀ` (linearity),
and the centred Frobenius sums agree: `∑ᵢⱼ (Σ̂_eig − EΣ̂_eig)ᵢⱼ² = ∑ₐᵦ (Σ̂_raw − EΣ̂_raw)ₐᵦ²` (`frobenius_error_eig_eq_raw`).

**D. E4 in the original coordinates** (`frobenius_ula_le_raw`): `frobenius_ula_le`'s bound holds verbatim for the raw-coordinate pooled
covariance `Σ̂_raw` of the ULA chain — the note's "relative Frobenius error of the whole covariance against `Σ_ULA`" is
`E‖Σ̂_raw − EΣ̂_raw‖_F²/‖Σ_ULA‖_F²` with both sides now literally matrix quantities.

Vote intention: A+B+C+D.

## Numerical check

`numcheck39.py` (`d = 5`, random orthogonal `U`, random `A`, `P = U diag(p) Uᵀ`, `h = 0.3`, 7 random draws): (1) `∑ Aᵢⱼ² = tr(AᵀA)`, (2) orthogonal
invariance, (3) `‖Σ_ULA‖_F² = ∑ 1/(pᵢ(1 − h pᵢ/2))²` and `‖P⁻¹‖_F² = ∑ 1/pᵢ²`, (4) `Σ̂_eig = Uᵀ Σ̂_raw U` — all `True` to machine precision.

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_frobenius_bridge_v1.md`. Summary: A–D correct; for square real matrices either of `UᵀU = 1`, `UUᵀ = 1` implies the other; the integrability route (raw entries from the eigen-projections' `L⁴` through finite linear combinations, then commute the expectation) is sound and non-circular. Terminology: D transfers the *centred* variance normalised by the target norm, not the MSE against `Σ_ULA` (which adds the squared bias — the raw form of `frobenius_pooledSecondMoment_target` is the natural follow-up, with the closed-form mean `U diag(s₂ᵢ(1 − R₂ᵢ/N)) Uᵀ`). Lean: the outer-product identity `(Uᵀx)(Uᵀx)ᵀ = Uᵀ(xxᵀ)U` is the reusable core; keep the API in `∑ᵢⱼ Aᵢⱼ²` rather than Mathlib's scoped Frobenius norm.

## Vote
- Claude: A+B+C+D
- GPT-6 Astra: A+B+C+D

Agreed. Proceeding to Step 3.

## Result

Commit `2623d37` on `tide/frobenius-bridge`; `lake build` clean (9007 jobs), `scripts/sorries` 0/0/0/0.
`Laplace/Sampler/FrobeniusBridge.lean` (280 lines): `sum_sq_eq_trace`, `sum_sq_conj`, `sum_sq_diagonal`, `frobenius_inv`,
`frobenius_ulaCov`, `vecMulVec_transpose_mulVec`, `inner_orthoCol_eq_mulVec`, `pooledRaw` (+`_apply`), `pooledEig_eq_conj`,
`pooledRaw_eq_conj`, `memLp_four_inner_ulaChain_Q`, `pooledRaw_apply_eq_sum`, `integrable_pooledRaw_apply`, `integral_pooledRaw_apply`,
`frobenius_error_raw_eq_eig`, `frobenius_ula_le_raw`.

Surprises: the whole bridge is one outer-product identity (`vecMulVec (Uᵀx)(Uᵀx) = Uᵀ (x xᵀ) U`) pushed through the pooled sum; the
integrability of the raw entries is best obtained as finite linear combinations of the eigen entries rather than from `L⁴` of the raw
coordinates. `sum_sq_conj` needs only `U Uᵀ = 1`.
