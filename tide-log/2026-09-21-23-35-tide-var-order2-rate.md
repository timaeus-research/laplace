# Tide: var-order2-rate

**Direction (user):** auto mode on the Sanity-on-Sampling note; E7 "the remainder drops from O(t⁻¹) to O(t⁻²)": an explicit second-order
rate for the exact anharmonic variance from the seabed's moment rates, in relative form and in the note's parametrisation, transported to the
separable and rotated E2 oscillators.
**Seabed:** laplace, branch `tide/gibbs-rotation` at commit 2d8170f (chained: needs `GibbsRotation.lean`)
**Started:** 2026-09-21T23:37Z

## Candidates v1 (Claude)

See `gpt_var_order2_rate_prompt_v1.md` (A–C verbatim).

- A: `(45A² − 12B)/λ − (α/(2λ²))² = α²/λ⁴ − γ/(2λ³)` and `|t Var − 1/λ − (α²/λ⁴ − γ/(2λ³))/t| ≤ K/(t√t)` for `t ≥ T`.
- B: relative form `|t(λtVar − 1) − (α²/λ³ − γ/(2λ²))| ≤ K/√t`, and `→ (a² − ½)` in the note's parametrisation.
- C: the same along every coordinate of `separableAnharmonic` and every column of `Q` for `rotatedAnharmonic`.

## GPT-6 Astra v1

Saved verbatim in `gpt_var_order2_rate_v1.md`. Summary: A correct with the combined constant `K₂ + K₁(2|m₀| + K₁)`; the `t^{-3/2}` loss comes
from the *second-moment* rate, not from the mean (whose squared contribution is already `O(t⁻²)`), so no slicker decomposition helps — the
seabed's inputs cannot certify more. B by multiplying with `λt`; C by the covariance identities (take common constants if "every direction" is
meant with one `K, T`). Wording: "the one-loop coefficient is exact; the residual is certified `O(t^{-3/2})`, hence `o(1/t)`; the numerics show
the sharper `t⁻²` of E7, not yet certified" — with a table of the three remainders (`Var − 1/(λt) − C/t²`: `t^{-5/2}`; `λtVar − 1 − λC/t`:
`t^{-3/2}`; `t(λtVar − 1) − λC`: `t^{-1/2}`). Follow-up route to `t⁻²`: a parity-aware Laplace expansion in `ε = t^{-1/2}` (odd orders vanish),
needing only a better second-moment bound. Additions: the mean restatement `|⟨x⟩ + α/(2λ²t)| ≤ K/t²`; the energy rate
`t⟨ℓ⟩ = ½ + c/t + O(t^{-3/2})` with `c = 5α²/(24λ³) − γ/(8λ²)` (`= 5a²/24 − 1/8` in the note's parametrisation) if the third/fourth-moment
rates are available (they are: `thirdMoment_anharmonic_rate`, `fourthMoment_anharmonic_order2_rate`). Vote: A+B+C plus the additions.

## Vote
- Claude: A+B+C + D (the energy rate, since the moment rates are in the seabed) + the mean restatement
- GPT-6 Astra: A+B+C (+ additions)

## Numerical check

`numcheck_var_order2_rate.py`: the coefficient identity to 1e-16 (`λ = 1, 3`); exact quadrature gives
`|t(λtVar − 1) − (a² − ½)| = 1.6e-2, 2.6e-3, 2.7e-4, 2.7e-5` at `t = 10, 100, 1000, 10000` (`≈ 0.27/t`, independent of `λ`): the true remainder
after the one-loop term is `O(1/t)` in this quantity (relative `O(t⁻²)`, the note's claim); the seabed's moment rates certify `O(t^{-1/2})`
(relative `O(t^{-3/2})`).

## Result

Commit `6861bd8` on `tide/var-order2-rate`; `lake build` clean, `scripts/sorries` 0/0/0/0.
`Laplace/Multi/VarianceOrder2.lean` (     420 lines): `var_order2_coeff`, `var_anharmonic_order2_rate`, `var_relative_rate_order2`,
`var_relative_rate_order2_note`, `separableAnharmonic_var_order2_rate_note`, `rotatedAnharmonic_var_order2_rate_note`,
`mean_anharmonic_rate_div`, `energy_order1_coeff`, `energy_anharmonic_order1_rate`, `energy_anharmonic_order1_rate_note`,
`separableAnharmonic_energy_order1_rate_note`, `rotatedAnharmonic_energy_order1_rate_note`.

Surprises: the energy's first-order coefficient `5α²/(24λ³) − γ/(8λ²)` (GPT's suggestion) reproduces E2's measured "4.76" at `t = 3`,
`d = 10`, `a = ½` to three digits (`5 − 10·0.0729/3 = 4.757`); the `t^{-3/2}` loss in the variance is entirely the second-moment
rate's, the mean enters squared and is already `O(t⁻²)`.
