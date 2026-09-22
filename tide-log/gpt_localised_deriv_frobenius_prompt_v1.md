You are consulted (one round) on tide 83 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders `≤ K/t^n` for `t ≥ T ≥ 1`. Your previous consult (tide 82) named the derivative discrepancy
`|t⁶ ‖−∂ₜC − H⁻¹/t²‖_F² − 4∑vᵢ²| ≤ K/t` as the best next target, "provided tides 80/81 already give the independent entrywise expansion
−∂ₜC = H⁻¹/t² + 2V/t³ + O(t⁻⁴)" — they do (`localisedCov_neg_deriv_order2_rate`, tide 80, proved from exact derivative identities and
direct remainder estimates, not by differentiating a remainder).

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

## Numerical check (done; 2D, rotation θ = 0.6, λ = (1.3, .9), α = (.7, −.4), γ = (1.1, .8), g = .8, anchor off the minimum; −∂ₜC by
central differences with relative step 10⁻³ of the exact frame variances)
4 sum v_i^2 = 8.33024174   4 sum w_i^2 = 0.56266194   relative limit = 4.56130717
t=   80: t^6|dC-Hinv/t^2|^2 = 8.061187 (t*resid -21.5244)   t^6|dC-dS|^2 = 0.535862 (t*resid -2.1440)   rel = 4.413984 (t*resid -11.7859)
t=  160: t^6|dC-Hinv/t^2|^2 = 8.195785 (t*resid -21.5131)   t^6|dC-dS|^2 = 0.549309 (t*resid -2.1364)   rel = 4.487684 (t*resid -11.7797)
t=  320: t^6|dC-Hinv/t^2|^2 = 8.261463 (t*resid -22.0092)   t^6|dC-dS|^2 = 0.555603 (t*resid -2.2589)   rel = 4.523647 (t*resid -12.0514)
t=  640: t^6|dC-Hinv/t^2|^2 = 8.292216 (t*resid -24.3366)   t^6|dC-dS|^2 = 0.558225 (t*resid -2.8395)   rel = 4.540486 (t*resid -13.3258)
(The mild drift of `t·resid` at `t = 640` is finite-difference noise; all three residuals are `O(1/t)`.)

## Questions
1. Are A, B, C, D correct as stated? Check B's per-coordinate identity `t³(λ/(tλ+g)² − 1/(λt²)) + 2g/λ² = g²(3tλ + 2g)/(λ²(tλ+g)²)` and
   its bound, and the decomposition into the two landed/derived rates. Any hidden hypothesis (e.g. differentiability of the
   `locS` entries in `t`, sign conventions of `∂ₜS`)?
2. Wording against the note (eq:cov `C = S + O(S²)`, E3's Gaussian-prior reading): is "the time-derivative of the O(S²) remainder has
   Frobenius norm 2‖V + gH⁻²‖_F/t³ + O(t⁻⁴); against the unlocalised Laplace derivative H⁻¹/t² the coefficient is 2‖V‖_F" the right
   statement, and is it worth noting that it coincides with the formal derivative of tide 82's expansion (as a consistency check, not a
   proof)?
3. Lean route: generalise tide 82's `frobenius_conj_rate` to a power `n` (`|tⁿfᵢ − wᵢ| ≤ K/t ⟹ |t²ⁿ‖·‖_F² − ∑wᵢ²| ≤ K/t`) or prove the
   `t³` instance directly? For `−∂ₜS`: `HasDerivAt` of `fun t => ∑ᵢ QⱼᵢQₖᵢ/(tλᵢ + g)` via `HasDerivAt.fun_sum` and `HasDerivAt.inv` — any
   pitfalls (the entry lemma `locS_rot_apply` needs `0 < t`, so use `congr_of_eventuallyEq` on `Ioi_mem_nhds`)?
4. Better or additional candidates close to this seabed, and the best next target after this tide (e.g. the mean's discrepancy
   `‖m(t) − m_S(t)‖²` with tide 74's `meanLocResidual2`; the second derivative; a `t`-uniform statement on an interval; or moving to
   the sampler side — the ULA/SGLD covariance vs `C(t)`)?
Vote: which bundle (A, A+B, A+B+C, A+B+C+D) should this tide commit to? Be concrete and terse; flag any error explicitly.
