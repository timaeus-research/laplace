# Tide: frobenius-target-raw

**Direction (user):** auto mode on the Sanity-on-Sampling note; follow-up to `frobenius-bridge`: E4's MSE of the raw-coordinate pooled ULA
covariance against its two targets (Σ_ULA and Q⁻¹), with the closed-form zero-start mean.
**Seabed:** laplace, branch `tide/frobenius-bridge` at commit 2150b62 (chained: needs `FrobeniusBridge.lean`)
**Started:** 2026-09-21T21:33Z

## Candidates v1 (Claude)

See `gpt_frobenius_target_raw_prompt_v1.md` (candidates A–D verbatim).

- A: eigenbasis Gram table + mean of the ULA eigen-projected pooled second moment, `E Σ̂_eig,ij = δᵢⱼ s₂ᵢ (1 − aᵢ)`.
- B: raw mean `E Σ̂_raw = U diag(s₂ᵢ(1 − aᵢ)) Uᵀ`, geometric closed form and bound for `aᵢ`.
- C: `E‖Σ̂_raw − Σ_ULA‖_F² = E‖Σ̂_raw − EΣ̂_raw‖_F² + ∑ᵢ (s₂ᵢ aᵢ)²` and its envelope.
- D: `E‖Σ̂_raw − Q⁻¹‖_F² = E‖Σ̂_raw − EΣ̂_raw‖_F² + ∑ᵢ (h/(2 − hpᵢ) − s₂ᵢ aᵢ)²` and its envelope; relative forms via `frobenius_inv`.

## GPT-6 Astra v1

Saved verbatim in `gpt_frobenius_target_raw_v1.md`. Summary: A–D correct; `(x − y)² ≤ x² + y²` for `x, y ≥ 0` is true (cross term
`−2xy ≤ 0`), the max form is sharper; structure the proofs around one deterministic-target identity
`E‖Σ̂ − T‖² = E‖Σ̂ − EΣ̂‖² + ‖EΣ̂ − T‖²` with `T = U diag(t) Uᵀ`, then specialise `t = s₂` and `t = 1/p`; the exact identities work for
`0 < hpᵢ < 2`, the burn-in bound for `hpᵢ ≤ 1`; the "against P⁻¹" comparison needs no further term when P = Q; relative forms are expected
squared relative error, RMS is the square root.

## Vote
- Claude: A+B+C+D (deterministic-target identity as the spine)
- GPT-6 Astra: A+B+C+D

## Numerical check

`numcheck40.py` (d = 3, random PD Q, h = 0.4/p_max, N = 5, b = 2, C = 4, 40000 Monte Carlo replicates): `Σ_ULA = U diag(s₂) Uᵀ`,
`s₂ = 1/(p(1 − hp/2))`, `s₂ − 1/p = h/(2 − hp)` and the geometric form of `aᵢ` hold to 1e-16; the Monte Carlo mean of `Σ̂_raw` matches
`U diag(s₂(1 − a)) Uᵀ` to within 0.4 standard errors (max abs deviation 6.5e-4, s.e. 1.6e-3); bias sums 3.3e-3 (Σ_ULA) and 1.5e-3 (Q⁻¹).

## Result

Commit `fc40889` on `tide/frobenius-target-raw`; `lake build` clean, `scripts/sorries` 0/0/0/0.
`Laplace/Sampler/FrobeniusTarget.lean` (     389 lines): `zeroStartFactor` (+`_eq`, `_nonneg`, `_le`), `mul_zeroStartFactor_sq_le`,
`ulaCov_eq_conj_diagonal`, `inv_eq_conj_diagonal`, `ula_variance_sub_inv`, `gram_ulaChain_eig`, `integral_pooledSecondMoment_ula`,
`integral_pooledRaw`, `integral_sum_sq_sub_eq_centred`, `frobenius_ula_target_raw_eq`, `frobenius_ula_target_raw` (+`_le`, `_rel`),
`frobenius_ula_posterior_raw` (+`_le`, `_rel`).

Surprises: `rw` with the Frobenius-decomposition lemma fails on `Matrix`-valued estimators (motive not type-correct: `Matrix ι ι ℝ` must be
unfolded to apply an entry), so the deterministic-target identity is stated once for a generic `S : ι → ι → Ω → ℝ` and applied with
`.trans`; a diagonal matrix built from a lambda with a subtraction must be bound with `set` before its entries are taken. `lean-state check`
timed out in the fresh worktree, so per-module `lake build` served as the inner loop (≈1 min per round).
