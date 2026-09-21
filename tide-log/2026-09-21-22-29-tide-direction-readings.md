# Tide: direction-readings

**Direction (user):** auto mode on the Sanity-on-Sampling note; two directional readings of a covariance along an eigenvector of `P`:
E7's "along an eigenvector `s` of `P` the corrected variance is `1/p_s + Π_ss/p_s²`" and Summary 4's "the whole-covariance Frobenius norm
hides [a stiff-direction error] because flat directions dominate it; the LLC exposes it because stiff directions dominate `K`".
**Seabed:** laplace, commit e49e3c9 (main)
**Started:** 2026-09-21T22:30Z

## Candidates v1 (Claude)

See `gpt_direction_readings_prompt_v1.md` (A–C verbatim).

- A: `sᵀ (P⁻¹ + P⁻¹ Π P⁻¹) s = (s·s)/p + (sᵀ Π s)/p²` for `P s = p s`; instance for `oneLoopCov` along `orthoCol i`.
- B: eigen-perturbation law `Σ' = P⁻¹ + U diag(δ) Uᵀ`: `‖Σ' − P⁻¹‖_F²/‖P⁻¹‖_F² = ∑δᵢ²/∑(1/pᵢ)²`, `½ tr(PΣ') − d/2 = ½ ∑ pᵢδᵢ`; the stiff
  case `LLC_rel² ≥ (κ/d)² Frob_rel²`, the flat case `Frob_rel² ≥ d · LLC_rel²`.
- C: a general comparison for all-inflation perturbations `δ ≥ 0`.

## GPT-6 Astra v1

Saved verbatim in `gpt_direction_readings_v1.md`. Summary: A correct, symmetry of `Π` unnecessary, but keep positive definiteness (a unit
right eigenvector of a nonsymmetric matrix does not suffice); `Π_ss` means `sᵀ Π s`. B correct including `1/p_min² ≤ ∑(1/pᵢ)² ≤ d/p_min²`;
if `Σ'` is to be a covariance require `1/pᵢ + δᵢ ≥ 0` (not needed for the identities); "exposes" is a sensitivity comparison, signed
multidirectional shifts can cancel in the LLC. Q2: `½ tr(PΣ)` is the quadratic, centred LLC statistic (`t⟨K⟩` at second order); a nonzero mean
adds `½ mᵀPm`, and inserting the one-loop covariance does not give the full one-loop `t⟨K⟩`. Q3: the sharp fixed-spectrum comparison for
`δ ≥ 0` is `d²/(QD) · L² ≤ F² ≤ d²/(p_min² D) · L²` with `Q = ∑pᵢ²`, `D = ∑1/pᵢ²`, both constants attained; it fails for signed `δ`
(upper bound). Vote: A+B now, C as the natural follow-up.

## Vote
- Claude: A+B (C's two inequalities `p_min² ∑δᵢ² ≤ (∑pᵢδᵢ)² ≤ ∑pᵢ² ∑δᵢ²` for `δ ≥ 0` added as a short extra section if cheap)
- GPT-6 Astra: A+B

## Numerical check

`numcheck_direction_readings.py` (d = 6, random PD `P`, random symmetric `Π` and `δ`): A to 1e-12 along every eigenvector; the two
identities of B to 1e-14; stiff case `LLC_rel/Frob_rel = 9.94 ≥ κ/d = 9.04`; flat case `Frob_rel/LLC_rel = 5.46 ≥ √d = 2.45`.
