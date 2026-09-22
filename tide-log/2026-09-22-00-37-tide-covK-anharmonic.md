# Tide: covK-anharmonic

**Direction (user):** auto mode on the Sanity-on-Sampling note; E2's fourth Laplace prediction, eq:covK ("the primer's canonical experiment"),
verified for the exact one-dimensional anharmonic Gibbs measure: `t² Cov[ℓ, (B/2)x² + bx] → B/(2λ) − bα/(2λ²)`, which is `t²` times the four-term
formula of the note.
**Seabed:** laplace, branch `tide/moments-all-orders` at commit ea493ec (chained: needs `MomentsAllOrders.lean`)
**Started:** 2026-09-22T00:38Z

## Candidates v1 (Claude)

See `gpt_covK_anharmonic_prompt_v1.md` (A–C verbatim).

- A: the six pair covariances `t² Cov[xᵐ, xⁿ]` that covK needs.
- B: `t² Cov[ℓ, x²] → 1/λ`, `t² Cov[ℓ, x] → −α/(2λ²)`, `t² Cov[ℓ, (B/2)x² + bx] → B/(2λ) − bα/(2λ²)`.
- C: eq:covK's four terms in one dimension sum to `(B/(2λ) − bα/(2λ²))/t²`; asymptotic agreement.

## GPT-6 Astra v1

Saved verbatim in `gpt_covK_anharmonic_v1.md`. Summary: A, B, C correct (table of the six pair limits; the pair `(3,1)` has total degree four,
so its product term needs the refined odd limit `t²⟨x³⟩ → c`, not a degree count); the note's four `b`-terms are `+αb/(2λ²t²)` and two
`−αb/(2λ²t²)`; **rate correction**: B proves `Cov = c/t² + o(t⁻²)`, i.e. relative error `o(1)`, not the note's `O(1/t)` (that needs
remainder estimates). Product terms: integer-power factorisations (`t²M₃M₂ = (t²M₃)M₂` with `M₂ → 0`, etc.) rather than real-power
boundedness. C: state the algebraic identity `covK(t) = c/t²` (`t > 0`), the unconditional `t²(Cov − covK(t)) → 0`, and the ratio `→ 1`
only under `c ≠ 0` (the plan's `t²Cov/covK − 1` had a stray `t²`). Vote: A+B+C.

## Vote
- Claude: A+B+C
- GPT-6 Astra: A+B+C

## Numerical check

`numcheck_covK_anharmonic.py` (`λ = 2`, `a = ½`, `B = 3`, `b = 1.5`): `t² Cov[ℓ, x²] = 0.49998 → 1/λ = 0.5`, `t² Cov[ℓ, x] = −0.17674 →
−α/(2λ²) = −0.1768`, `t² Cov[ℓ, ψ] = 0.48486` at `t = 10⁴` against `c = 0.48483`; the four terms of eq:covK evaluate to
`0.75, 0.265, −0.265, −0.265` with the same sum.

## Result

Commit `ca71300` on `tide/covK-anharmonic`; `lake build` clean, `scripts/sorries` 0/0/0/0.
`Laplace/OneD/CovKAnharmonic.lean` (     350 lines): `tendsto_zero_of_tendsto_pow_mul`, `gibbsCov_pow_pow`, `gibbsCov_pow_id`,
`firstMoment_tendsto_zero`, `secondMoment_tendsto_zero`, `cov_sq_sq_asymptotic`, `cov_cube_sq_asymptotic`,
`cov_fourth_sq_asymptotic`, `cov_cube_id_asymptotic`, `cov_fourth_id_asymptotic`, `gibbsCov_anharmonic_left`,
`covK_anharmonic_sq`, `covK_anharmonic_lin`, `covK_anharmonic`, `covKOneDim`, `covKOneDim_eq`, `covK_anharmonic_agree`,
`covK_anharmonic_ratio`.

Surprises: with the all-orders moment scaling in hand the whole covK computation is bookkeeping (six pair limits, three bilinear
expansions); the note's four-term formula collapses in one dimension to `(B/(2λ) − bα/(2λ²))/t²` by `field_simp; ring`.
