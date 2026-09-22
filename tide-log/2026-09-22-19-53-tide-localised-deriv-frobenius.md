# Tide: localised-deriv-frobenius

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); GPT's next target after tide 82: the derivative discrepancy `|t⁶ ‖−∂ₜC − H⁻¹/t²‖_F² − 4∑vᵢ²| ≤ K/t` from tide 80's
entrywise expansion.
**Seabed:** laplace, commit dbe3e49 (worktree `laplace-tide-localised-deriv-frobenius`, branch `tide/localised-deriv-frobenius` off `main`)
**Started:** 2026-09-22T19:54Z

## Candidates v1 (Claude)

Setting (E2, as in tides 68–82): `C(t)` the exact localised centred covariance, `S(t) = (tH + gI)⁻¹ = Q diag(1/(tλᵢ + g)) Qᵀ`,
`H⁻¹ = Q diag(1/λᵢ) Qᵀ`, `vᵢ` the `O(S²)` variance coefficients, `wᵢ = vᵢ + g/λᵢ²`, `V = Q diag(vᵢ) Qᵀ`, `W = V + gH⁻²`,
`Dᵢ(t) = −∂ₜ Var_loc(uᵢ)` (tide 80). Landed: `−∂ₜ Cⱼₖ = ∑ᵢ QⱼᵢQₖᵢ Dᵢ` exactly (`hasDerivAt_localised_cov_coord`), the per-coordinate
`|t² Dᵢ − 1/λᵢ − 2vᵢ/t| ≤ K/t²` (`localisedVar_neg_deriv_order2_rate`), the entrywise
`|t²(−∂ₜCⱼₖ) − (H⁻¹)ⱼₖ − 2Vⱼₖ/t| ≤ K/t²` (`localisedCov_neg_deriv_order2_rate`), and tide 82's Frobenius transport
`frobenius_conj_rate` (per-coordinate `|t² fᵢ − wᵢ| ≤ K/t` ⟹ `|t⁴ ∑ⱼₖ (∑ᵢ QⱼᵢQₖᵢ fᵢ)² − ∑ᵢ wᵢ²| ≤ K/t`). `‖X‖_F² = ∑ⱼₖ Xⱼₖ²`.

**A. The derivative's Frobenius discrepancy from the unlocalised Laplace derivative `H⁻¹/t²`.**
`|t⁶ ‖−∂ₜC(t) − H⁻¹/t²‖_F² − 4∑ᵢ vᵢ²| ≤ K/t`, i.e. `‖−∂ₜC − H⁻¹/t²‖_F² = 4‖V‖_F²/t⁶ + O(t⁻⁷)`.
Route: `−∂ₜCⱼₖ − (H⁻¹)ⱼₖ/t² = ∑ᵢ QⱼᵢQₖᵢ (Dᵢ − 1/(λᵢt²))` (frame), per coordinate `|t³(Dᵢ − 1/(λᵢt²)) − 2vᵢ| ≤ K/t` (multiply the landed
rate by `t`), then the Frobenius transport generalised to the scaling `t³` (a power-`n` version of `frobenius_conj_rate`:
`|tⁿfᵢ − wᵢ| ≤ K/t ⟹ |t²ⁿ ∑ⱼₖ (∑ᵢ QⱼᵢQₖᵢ fᵢ)² − ∑ᵢ wᵢ²| ≤ K/t`).

**B. The derivative's Frobenius discrepancy from the resolvent's derivative** (the derivative reading of tide 82's A).
`−∂ₜ S(t) = Q diag(λᵢ/(tλᵢ + g)²) Qᵀ` exactly (`HasDerivAt` of the entries through `locS_rot_apply`), and
`|t⁶ ‖−∂ₜC(t) + ∂ₜS(t)‖_F² − 4∑ᵢ wᵢ²| ≤ K/t`, i.e. `‖∂ₜ(C − S)‖_F² = 4‖W‖_F²/t⁶ + O(t⁻⁷)` — consistent with the formal derivative of
`C − S = W/t² + O(t⁻³)` but proved from the derivative expansions, not by differentiating a remainder. Per coordinate:
`t³(λ/(tλ + g)² − 1/(λt²)) + 2g/λ² = g²(3tλ + 2g)/(λ²(tλ + g)²) ≤ g²(3λ + 2g)/(λ⁴ t)` for `t ≥ 1`, and
`t³(Dᵢ − λᵢ/(tλᵢ + g)²) − 2wᵢ = [t³(Dᵢ − 1/(λᵢt²)) − 2vᵢ] − [t³(λᵢ/(tλᵢ + g)² − 1/(λᵢt²)) + 2g/λᵢ²]`.

**C. The relative form.** `‖H⁻¹/t²‖_F² = (∑ᵢ λᵢ⁻²)/t⁴` exactly, so
`|t² ‖−∂ₜC − H⁻¹/t²‖_F²/‖H⁻¹/t²‖_F² − 4∑ᵢvᵢ²/∑ᵢλᵢ⁻²| ≤ K/t` in positive dimension (plain division by the exact denominator).

**D (cheap).** Two-sided: if `∑ᵢ vᵢ² > 0`, eventually `2∑vᵢ² ≤ t⁶‖−∂ₜC − H⁻¹/t²‖_F² ≤ 6∑vᵢ²` (tide 82's `two_sided_of_rate`).

Sizing: the power-`n` transport ~60 lines, A ~50, B ~120 (`HasDerivAt` of `locS` entries, the resolvent-derivative coordinate rate,
combination), C ~30, D ~20. Target A + B + C + D.

## Numerical check

`numcheck_localised_deriv_frobenius.py` (2D, rotation `θ = 0.6`, anchor off the minimum; `−∂ₜC` by central differences of the exact frame
variances): `4∑vᵢ² = 8.33024174`, `4∑wᵢ² = 0.56266194`, relative limit `4.56130717`; at `t = 80, 160, 320, 640`:
`t⁶‖−∂ₜC − H⁻¹/t²‖_F² = 8.0612, 8.1958, 8.2615, 8.2922` (`t·resid ≈ −21.5 … −24`), `t⁶‖∂ₜ(C − S)‖_F² = 0.5359, 0.5493, 0.5556, 0.5582`
(`t·resid ≈ −2.1 … −2.8`), relative `4.414, 4.488, 4.524, 4.540`; all `O(1/t)` (the mild drift at `t = 640` is finite-difference noise).

## GPT-6 Astra v1

Verbatim in `gpt_localised_deriv_frobenius_v1.md` (prompt: `gpt_localised_deriv_frobenius_prompt_v1.md`). Summary: **A–D correct**
under the standing hypotheses (B's displayed bound uses `g ≥ 0`; C needs positive dimension). B's identity
`t³(λ/(tλ+g)² − 1/(λt²)) + 2g/λ² = g²(3tλ + 2g)/(λ²(tλ+g)²)` confirmed, bound via `tλ + g ≥ tλ`, `3tλ + 2g ≤ t(3λ + 2g)`; the subtraction of
the two coordinate errors is right since `wᵢ = vᵢ + g/λᵢ²`. **Signs**: `S' = −Q diag(λᵢ/(tλᵢ+g)²) Qᵀ`, so `−C' + S' = −(C − S)'`; do not call
the positive diagonal expression `S'`. C: divide A's constant by `L = ∑λᵢ⁻²`. D: enlarge the threshold until `K/t ≤ 2a`. Wording: "For
`R(t) = C(t) − S(t)`, the independently established derivative expansion gives `R'(t) = −2W/t³ + O_F(t⁻⁴)`, `‖R'(t)‖_F = 2‖W‖_F/t³ +
O(t⁻⁴)`; against the unlocalised negative Laplace derivative `H⁻¹/t²` the corresponding coefficient is `2‖V‖_F`" — note the agreement
with the formal derivative of tide 82's expansion **as a consistency check only**; the norm statement (also when `W = 0`) follows from
the coordinate/matrix derivative expansion and the reverse triangle inequality, not from B's squared rate. Lean route: **reuse
`frobenius_conj_rate` through `f̃ᵢ = t fᵢ`** (a small `t³` wrapper shared by A and B; no power-`n` generalisation this tide); prove the
finite-sum rational formula's `HasDerivAt` directly with `tλᵢ + g ≠ 0` supplied to the inverse rule, transfer to `locS` by local eventual
equality on `t > 0`, keep the derivative as `−λᵢ/(tλᵢ+g)²` and normalise signs afterwards. Optional addition: the unsquared norm rate
from the coordinate rates (not merely square roots). **Next target**: the mean's squared discrepancy against the resolvent mean,
reusing the squared-norm transport, if `meanLocResidual2` supplies the vector coefficient and remainder; defer second derivatives;
parameter-uniformity would be new; ULA/SGLD is a larger pivot.

## Vote
- Claude: A + B + C + D
- GPT-6 Astra: "**Vote: A+B+C+D**, with A+B the protected core; C and D are cheap corollaries."
