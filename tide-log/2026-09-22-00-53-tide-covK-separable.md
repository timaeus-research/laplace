# Tide: covK-separable

**Direction (user):** auto mode on the Sanity-on-Sampling note; eq:covK for the separable anharmonic oscillator in `d` dimensions (E2's
"canonical experiment" as run): two-coordinate covariance factorisation, `t² Cov_L[L, ψ] → ∑ᵢ Bᵢ/(2λᵢ) − ∑ᵢ bᵢαᵢ/(2λᵢ²)` for eigenframe-diagonal
quadratic probes, the off-diagonal probe terms at leading order, and the rotated frame.
**Seabed:** laplace, branch `tide/covK-anharmonic` at commit ebf1ad0 (chained: needs `CovKAnharmonic.lean`)
**Started:** 2026-09-22T01:03Z

## Candidates v1 (Claude)

See `gpt_covK_separable_prompt_v1.md` (A–C verbatim).

- A: `Cov_L[f(uₖ), g(uᵢ)] = δₖᵢ Cov_{ℓₖ}[f, g]` from the product factorisation and coordinate reduction.
- B: covK for eigenframe-diagonal probes `ψ = ∑ᵢ (Bᵢ/2)uᵢ² + bᵢuᵢ`: `t² Cov_L[L, ψ] → ∑ᵢ Bᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²)`; eq:covK in the eigenframe;
  rotated frame.
- C: off-diagonal terms `t² Cov_L[L, uᵢuⱼ] → 0` and the full quadratic probe.

## GPT-6 Astra v1

Saved verbatim in `gpt_covK_separable_v1.md`. Summary: A–C correct; the exact off-diagonal identity is
`Cov_L[L, uᵢuⱼ] = ⟨x⟩_j Cov_i[ℓᵢ, x] + ⟨x⟩_i Cov_j[ℓⱼ, x]` (not zero), and its `t²` limit needs only `⟨x⟩_i → 0` plus the 1D
`covK_anharmonic_lin`; B's integrability obligations are the mixed products `ℓₖ(uₖ)ψᵢ(uᵢ)e^{−tL}`, monomials again. Route: a two-coordinate
product lemma, A by splitting `i = j` (combine `f·g` on the repeated coordinate rather than encoding repeats), a three-coordinate lemma for
C's `k ∉ {i,j}` case, then sum the coordinate-energy covariances and prove limits from the exact identity. A+B is a coherent checkpoint
(covK for eigenframe-aligned probes, including their rotations) but B alone does not cover E2's arbitrary random quadratics — C is needed
for that. Vote: A+B+C staged, A+B as fallback.

## Vote
- Claude: A+B+C (staged)
- GPT-6 Astra: A+B+C (staged; A+B fallback)

## Numerical check

`numcheck_covK_separable.py` (`d = 2`, `λ = (1, 3)`, `a = ½`, `B = [[2, 0.7],[0.7, 1.5]]`, `b = (0.8, −0.4)`): at `t = 800` the full-probe and
diagonal-probe `t² Cov[L, ψ]` agree with eq:covK's eigenframe value `1.1077` to three digits (`1.1087`, `1.1087`; quadrature box truncation
accounts for the drift), and the off-diagonal `t² Cov[L, u₁u₂]` is `9 × 10⁻⁵` and shrinking.

## Result

Commit `7982de3` on `tide/covK-separable`; `lake build` clean, `scripts/sorries` 0/0/0/0. All of A, B and C landed.
`Laplace/Multi/CovKSeparable.lean` (     674 lines): `gibbsExpectation_two_coord_separable`, `gibbsCov_coord_fun_separable`,
`prod_pow_single_pow`, `integrable_coord_pow_mul_separableAnharmonic`, `integrable_energy_coord_pow_separableAnharmonic`,
`gibbsCov_energy_probe_separableAnharmonic`, `covK_separable_diag`, `covKDiag`, `covKDiag_eq`, `covK_separable_diag_agree`,
`gibbsExpectation_three_coord_separable`, `integrable_coord_pow_mul_mul_separableAnharmonic`,
`integrable_energy_coord_mul_separableAnharmonic`, `gibbsCov_energy_pair_separableAnharmonic`, `covK_separable_offdiag`,
`gibbsCov_add_left_of_integrable`, `integrable_energy_mul_separableAnharmonic`, `gibbsCov_energy_coord_pow_separableAnharmonic`,
`covK_separable_pair`, `covK_separable_lin`, `covK_separable_quadratic`, `covK_rotatedAnharmonic_diag`,
`covK_rotatedAnharmonic_quadratic`.

Surprises: the whole tide is exact algebra plus the 1D limits of `covK-anharmonic`; no new analysis was needed. GPT's off-diagonal identity
`Cov_L[L, uᵢuⱼ] = ⟨x⟩ⱼ Cov_i[ℓᵢ, x] + ⟨x⟩ᵢ Cov_j[ℓⱼ, x]` came out verbatim from the three-coordinate product lemma, and the full quadratic
probe reduces to it by flattening the double sum to `ι × ι`.
