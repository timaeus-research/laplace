# Tide: order3-parity

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: the E7 `t⁻²` relative rate, left open by the `var-order2-rate` tide, via a parity-aware fourth-order expansion.)
**Seabed:** laplace, commit 490d753
**Started:** 2026-09-22T01:50Z

## Candidates v1 (Claude)

See `gpt_order3_parity_prompt_v1.md` (A–E verbatim).

- A: fourth-order integral remainder `|∫ uⁿ e^{−u²/2}(e^{−s_t} − (1 − s_t + s_t²/2 − s_t³/6))| ≤ K/t²`.
- B: cubised decomposition, `J_n_asymptotic_order3`, and the parity corollaries (even `n`: the second-order formula with a `t⁻²`
  remainder; odd `n`: `J_n = −(A/√t)m_{n+3} + c/(t√t) + O(t⁻²)`).
- C: `|t⟨x²⟩ − 1/λ − C₂/t| ≤ K/t²`, `|tVar − 1/λ − C/t| ≤ K/t²`, `|t(λtVar − 1) − (a² − ½)| ≤ K/t` (E7's `t⁻²`), separable / rotated forms.
- D: `|t²⟨x³⟩ + 5α/(2λ³)| ≤ K/t`, `|t⟨x⁴⟩ − 3/(λ²t)| ≤ K/t²`, `|t⟨ℓ⟩ − ½ − c/t| ≤ K/t²` and forms.

## GPT-6 Astra v1

Saved verbatim in `gpt_order3_parity_v1.md`. Summary: A–D correct as stated (cubised coefficients and both parity corollaries checked;
the odd-`n` remainder is really `O(t^{-5/2})` but A+B only certify `O(t⁻²)`); use the direct `(x + y)⁴ ≤ 8(x⁴ + y⁴)` bound for A; the
proposed generic ratio lemma with only `r(t) ≥ t` is false (`X = 1`, `Y = 1 + 1/t` gives an intrinsic `1/(t(t+1))` term), so prove a
specialised `t⁻²` ratio lemma from the exact identity `X − (p + q/t)Y = e_X − (p + q/t)e_Y − qd/t²` with `p = a/c`, `q = (bc − ad)/c²`,
plus a zeroth-order quotient lemma for D's third moment; D's third and fourth moments need no new expansion but its energy result
depends on C's second moment. Vote: A+B+C, D as a stretch rather than an acceptance requirement.

## Vote
- Claude: A+B+C (D as stretch)
- GPT-6 Astra: A+B+C (D as stretch)

## Numerical check

`numcheck_order3_parity.py` (`λ = 2`, `a = ½`, `γ = λ²`): `t²(J_n − 3-term)` for even `n = 0, 2, 4` converges (`−0.0615`, `−1.027`,
`−16.08`); `t²(J_n − 2-term)` for odd `n = 1, 3` decays like `t^{-1/2}` (parity: the odd remainder is `O(t^{-5/2})`);
`t·[t(λtVar − 1) − (a² − ½)] → −0.2715` (the note's "≈ 0.27/t"); `t²·[t⟨ℓ⟩ − ½ − (5a²/24 − 1/8)/t] → −0.0542`;
`t·[t²⟨x³⟩ + 5α/(2λ³)] → 0.772`.

## Result

Commit `5e65337` on `tide/order3-parity`; `lake build` clean, `scripts/sorries` 0/0/0/0. A, B, C and the stretch D all landed.
`Laplace/OneD/IntegralRemainder3.lean` (     271 lines): `perturbation_remainder4_pointwise`, `add_pow_four_le_eight_mul`,
`rescaled_fourth_bound`, `perturbation_remainder4_combined`, `integrable_pow_add2_mul_exp_neg_mul_sq`, `integrable_remainder4`,
`perturbation_remainder4_integral_bound`.
`Laplace/OneD/JnThirdOrder.lean` (     306 lines): `cubed_integral_decomposition`, `J_n_asymptotic_order3`, `J_n_even_asymptotic_order3`,
`J_n_odd_asymptotic_order3`.
`Laplace/OneD/MomentThirdOrder.lean` (     393 lines): `ratio_rate_order2`, `ratio_rate_order1`, `J0_delta_order3`, `J2_delta_order3`,
`J3_delta_order2`, `J0_delta_order1`, `secondMoment_anharmonic_order3_rate`, `thirdMoment_anharmonic_rate_sharp`,
`fourthMoment_anharmonic_t_rate`.
`Laplace/Multi/VarianceOrder3.lean` (     350 lines): `var_anharmonic_order2_rate_sharp`, `var_relative_rate_order2_sharp`,
`var_relative_rate_order2_note_sharp`, `separableAnharmonic_var_order2_rate_note_sharp`,
`rotatedAnharmonic_var_order2_rate_note_sharp`, `energy_order1_coeff_sharp`, `energy_anharmonic_order1_rate_sharp`,
`energy_anharmonic_order1_rate_note_sharp`, `separableAnharmonic_energy_order1_rate_note_sharp`,
`rotatedAnharmonic_energy_order1_rate_note_sharp`.

Surprises: the fourth-order layer is *simpler* than the cubic one (an even power needs no odd-absolute-value absorption); the whole
`t⁻²` upgrade is parity bookkeeping on top of the existing expansion plus two ten-line ratio lemmas, and the energy's third and
fourth moments needed no new analysis at all.
