# Tide: localised-frobenius

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); GPT's next target after tide 81: the Frobenius discrepancy of E2's exact localised covariance from the
Gaussian-prior resolvent, `| ‖C(t) − S(t)‖_F² − ‖V + gH⁻²‖_F²/t⁴ | ≤ K/t⁵`.
**Seabed:** laplace, commit d4e3759 (worktree `laplace-tide-localised-frobenius`, branch `tide/localised-frobenius` off `main`)
**Started:** 2026-09-22T19:34Z

## Candidates v1 (Claude)

Setting (E2, as in tides 68–81): the rotated separable anharmonic family with the isotropic localiser `g ≥ 0`, anchor `w₀`, fixed
parameters, `t → ∞`. `C(t)` the exact localised centred covariance, `S(t) = (tH + gI)⁻¹ = Q diag(1/(tλᵢ + g)) Qᵀ` the note's
Gaussian-prior resolvent, `H⁻¹ = Q diag(1/λᵢ) Qᵀ`, `vᵢ = varLocCoeff2ᵢ` (tide 74), `wᵢ = vᵢ + g/λᵢ² = covLocCoeff2ᵢ`,
`W = Q diag(wᵢ) Qᵀ = V + gH⁻²`. Tide 74 gives entrywise `|C(t)ⱼₖ − S(t)ⱼₖ − Wⱼₖ/t²| ≤ K/t³` (`localisedRotatedAnharmonic_cov_order2_rate`).
`‖X‖_F² := ∑ⱼₖ Xⱼₖ²`.

**A. The Frobenius discrepancy from the Gaussian-prior covariance.**
`|t⁴ ‖C(t) − S(t)‖_F² − ‖W‖_F²| ≤ K/t` eventually, with the invariant closed form `‖W‖_F² = ∑ᵢ (vᵢ + g/λᵢ²)²`
(`‖Q diag(a) Qᵀ‖_F² = ∑ᵢ aᵢ²` for orthogonal `Q`). Equivalently `‖C − S‖_F² = ‖V + gH⁻²‖_F²/t⁴ + O(t⁻⁵)`: the note's `O(S²)` remainder in
(eq:cov) has Frobenius norm `‖W‖_F/t² + O(t⁻³)`, i.e. `‖C − S‖_F = ‖W‖_F ‖S‖_F²·(1 + o(1))·(∑λᵢ⁻²)⁻¹`… stated as the squared form only.
Lean: entrywise square rate `sq_rate : |t²x − w| ≤ K/t ⟹ |t⁴x² − w²| ≤ (2|w|K + K²)/t` (for `t ≥ 1`), summed over `j, k`
(`sum_rate_div` finite-sum transport), plus `frobenius_conj_diagonal` (via `sum_sum_eq_trace`, `trace_mul_comm`, `QᵀQ = 1`).

**B. The discrepancy from the unlocalised Laplace covariance `H⁻¹/t`: the localiser drops out.**
`|t⁴ ‖C(t) − H⁻¹/t‖_F² − ‖V‖_F²| ≤ K/t`, `‖V‖_F² = ∑ᵢ vᵢ²`. Entrywise, `S − H⁻¹/t = −gH⁻²/t² + O(t⁻³)` exactly
(`1/(tλ + g) − 1/(tλ) = −g/(tλ(tλ + g))`, with `|t²(…) + g/λ²| = g²/(λ²(tλ + g)) ≤ g²/(λ³t)`), so `C − H⁻¹/t = V/t² + O(t⁻³)`: the
pure Gaussian-localiser term `gH⁻²` cancels between `C − S` and `S − H⁻¹/t`. Contrast with A: the discrepancy from the *resolvent* is
governed by `V + gH⁻²`, from the *unlocalised* Laplace covariance by `V` alone.

**C. The relative discrepancy (the note's `O(S²)` made quantitative).**
`‖S(t)‖_F² = ∑ᵢ 1/(tλᵢ + g)²` exactly (`locS_rot_apply` + `frobenius_conj_diagonal`), so `t²‖S‖_F² = ∑ᵢ λᵢ⁻² + O(1/t)` and
`|t² ‖C − S‖_F²/‖S‖_F² − ‖W‖_F²/‖H⁻¹‖_F²| ≤ K/t`, `‖H⁻¹‖_F² = ∑ᵢ λᵢ⁻²`: the relative Frobenius error of the note's (eq:cov) is
`(‖W‖_F/‖H⁻¹‖_F)/t + O(t⁻²)` (in the squared form). Lean: ratio bookkeeping with the positive limit `∑ λᵢ⁻² > 0` (needs `d ≥ 1`, i.e.
`Nonempty (Fin d)`; for `d = 0` both sides are `0`… state with `[Nonempty (Fin d)]` or `0 < d`).

Not proposed: operator-norm versions (Frobenius is the invariant sum-of-squares the seabed's entrywise rates reach directly); the
Frobenius *norm* (square root) — the squared form is the clean statement.

Sizing: A ~150 lines (square rate, finite sums, Frobenius of a conjugated diagonal), B ~120 (resolvent-minus-inverse entrywise rate,
combination), C ~100 (exact `‖S‖_F²`, ratio). Target A + B + C.

## Numerical check

`numcheck_localised_frobenius.py` (2D, rotation `θ = 0.6`, anchor off the minimum): `∑(vᵢ + g/λᵢ²)² = 0.14066548`, `∑vᵢ² = 2.08256044`,
`‖W‖²/‖H⁻¹‖² = 0.07702279`; at `t = 80 … 1280`: `t⁴‖C − S‖_F² = 0.13626, 0.13850, 0.13959, 0.14013, 0.14040` (`t·resid ≈ −0.34`),
`t⁴‖C − H⁻¹/t‖_F² = 2.0379 … 2.0798` (`t·resid ≈ −3.52`), `t²‖C − S‖²/‖S‖² = 0.07611 … 0.07697` (`t·resid ≈ −0.063`): all three
residuals are `O(1/t)` with bounded `t·resid`.

## GPT-6 Astra v1

Verbatim in `gpt_localised_frobenius_v1.md` (prompt: `gpt_localised_frobenius_prompt_v1.md`). Summary: **A and C correct; B's formula
correct but its slogan "the localiser drops out" is false** — `V` still depends on `g` (`vᵢ = αᵢ²/λᵢ⁴ − g x₀ᵢαᵢ/λᵢ³ − g/λᵢ² − γᵢ/(2λᵢ³)`);
only the explicit `+gH⁻²` of `W` cancels (decisive check: the purely quadratic case has `C = S`, `W = 0`, `V = −gH⁻²`). Rename B
"**changing the reference covariance**": switching the reference from the Gaussian-prior resolvent to `H⁻¹/t` changes the leading
discrepancy coefficient from `W = V + gH⁻²` to `V`. C needs `Nonempty (Fin d)` (state it, do not exploit `0/0 = 0`). The informal
multiplicative `(1 + o(1))` norm form needs `W ≠ 0`; the additive norm forms `‖C − S‖_F = ‖W‖_F/t² + O(t⁻³)`,
`‖C − S‖_F/‖S‖_F = (‖W‖_F/‖H⁻¹‖_F)/t + O(t⁻²)` hold for all `W` but should come from the matrix remainder bound and the reverse
triangle inequality, not from square roots of the squared asymptotic (loses the rate when `W = 0`). The squared Frobenius statement is
"an excellent invariant, Lean-friendly quantitative version" of `C = S + O(S²)`. Lean route: one scalar square lemma
(`|y − w| ≤ K/t ⟹ |y² − w²| ≤ (K/t)(2|w| + K)`, `y = t²x`), finite-sum transport, invariance via the landed trace lemmas
(`sum_sum_eq_trace`, `trace_mul_conj_diagonal`, `conj_conj`); a reusable ratio lemma (`|a − a₀| ≤ kₐ/t`, `|b − L| ≤ k_b/t`, `L > 0`,
threshold `t ≥ 2k_b/L` so `b ≥ L/2`, bound `(2kₐ/L + 2|a₀|k_b/L²)/t`); uniformise the entrywise thresholds before summing. **Cheap
corollary**: if `∑wᵢ² > 0`, eventually `∑wᵢ²/(2t⁴) ≤ ‖C − S‖_F² ≤ 3∑wᵢ²/(2t⁴)` (sharp `t⁻²` Frobenius order; when `W = 0` the
entrywise remainder gives `‖C − S‖_F² = O(t⁻⁶)`). **Next target**: the derivative discrepancy
`|t⁶ ‖−∂ₜC − H⁻¹/t²‖_F² − 4∑vᵢ²| ≤ K/t` from tide 80's entrywise expansion (not by differentiating a remainder); the weighted trace
`tr(H(C − S))` has coefficient `∑λᵢwᵢ` with no universal sign.

## Vote
- Claude: A + B + C (+ the two-sided corollary), B reworded as GPT says
- GPT-6 Astra: "**Vote: A+B+C.** Commit in that order … If proof engineering overruns, preserve A+B and defer C rather than weakening
  the quantitative statements."

## Result

Commit `ac4fc17` on `tide/localised-frobenius`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/LocalisedFrobenius.lean` (     353 lines).
A + B + C as voted plus the two-sided corollary; B reworded per GPT ("changing the reference covariance", not "the localiser
drops out": `V` still depends on `g`).
Algebra/rates: `frobenius_eq_trace`, `frobenius_conj_diagonal`, `sq_rate`, `order3_to_scaled`, `order2_to_scaled`, `ratio_rate`,
`two_sided_of_rate`, `resolvent_sq_coord_rate`, `frobenius_conj_rate` (the generic Frobenius transport of per-coordinate rates).
A: `localisedCov_sub_locS_entry`, `localisedCov_frobenius_locS_rate`. B: `localisedCov_sub_inv_entry`, `localisedCov_frobenius_inv_rate`.
C: `locS_frobenius`, `locS_frobenius_rate`, `localisedCov_frobenius_relative_rate` (needs `0 < d`). D: `localisedCov_frobenius_locS_two_sided`.

Surprises: the frame route makes A and B one generic transport lemma each (per-coordinate `t²(Var_loc,ᵢ − ref_i) − coeff_i = O(1/t)`
from tide 74's 1D rates, weighted by `QⱼᵢQₖᵢ`, squared, summed over `(j, k)`), so no matrix remainder bookkeeping is needed at all.
