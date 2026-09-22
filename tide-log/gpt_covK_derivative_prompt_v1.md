# Tide `covK-derivative` (laplace seabed): candidates for GPT-6 Astra

## Context

The note's Hessian-route formulas (Setup): eq:cov `Cov[w] = S + O(S²)`, eq:mean `⟨w⟩ − w* = −½ S (tT:S) + γ S (w₀ − w*) + O(S²)`,
eq:covK `Cov[K, ψ] = ½ tr(HSBS) + ½ (Sb)ᵀ(T:S) − (t/2) bᵀ SHS (T:S) − (t/2) (Sb)ᵀ (T:(SHS))`, with `S = P⁻¹ = (tH + γI)⁻¹` and the
probe `ψ = ½ vᵀBv + bᵀv`, `v = w − w*`. The seabed has `covKFormula t H T B b` (the right-hand side of eq:covK at `γ = 0`,
`S = (tH)⁻¹`), `meanShift t H T := −½ S (t T:S)`, their evaluations on E2's tensors and Rosenbrock, and the rates. It also has,
for one-dimensional Gibbs measures `e^{−tℓ}` with the quartic anharmonic `ℓ(x) = λx²/2 + αx³/6 + γx⁴/24` (`λ, γ > 0`,
`α² < 3λγ`), exact moments, `ℓ ≥ 0` with `ℓ(x) > 0` for `x ≠ 0` (this morning), integrability of polynomials against the weight, and a
worked pattern for `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`TiltInterpolation`: `d/du P_u(f) = −t Cov_{P_u}(f, R)` for a
*bounded* tilt `R`, via a `TiltData` structure; `MorseBottResponse`).

## Observation

For a `t`-independent probe, `d/dt ⟨ψ⟩_t = −Cov_t[K, ψ]` exactly (`⟨ψ⟩_t = ∫ψe^{−tK}/∫e^{−tK}`). Correspondingly eq:covK is
`−∂ₜ` of the first-order prediction `⟨ψ⟩ ≈ ½ tr(BS) + bᵀ(⟨w⟩ − w*)`: with `∂ₜS = −SHS` and `∂ₜ(tT:S) = T:S − t T:(SHS)`,
`−∂ₜ[½ tr(BS) − ½ (Sb)ᵀ(tT:S)] = ½ tr(HSBS) − (t/2) bᵀSHS(T:S) + ½ (Sb)ᵀ(T:S) − (t/2)(Sb)ᵀ(T:(SHS))`, which is eq:covK *term by
term* — including for `S = (tH + γI)⁻¹`. At `γ = 0`, `SHS = S/t`, the second and fourth terms cancel and
`covKFormula t = t⁻² (½ tr(BH⁻¹) − ½ bᵀH⁻¹(T:H⁻¹))`. Numerically (`numcheck_covK_derivative.py`): `covKFormula(t) = −F'(t)` to `1e-10`
for random `H, T, B, b`; and for the anharmonic measure `Cov_t[ℓ, xᵏ] = −d⟨xᵏ⟩/dt` to `1e-9` (`k = 1, 2, 3`, `t = 2, 8`).

## Candidates

**A. eq:covK is `−∂ₜ` of eq:cov and eq:mean, at the formula level.** For `IsUnit H.det`, `t ≠ 0`:
`covKFormula_eq_neg_deriv : covKFormula t H T B b = −deriv (fun s => ½ (B * (s • H)⁻¹).trace + b ⬝ᵥ meanShift s H T) t`, via
`(s • H)⁻¹ = s⁻¹ • H⁻¹`, linearity of `contractT` in `S`, so the function is `c · s⁻¹` with `c = ½ tr(BH⁻¹) − ½ bᵀH⁻¹(T:H⁻¹)`, and
`covKFormula_eq : covKFormula t H T B b = c / t²` (the cancellation of terms 2 and 4 made explicit:
`covKFormula_terms_cancel`). `HasDerivAt` form as well.

**B. The exact identity in one dimension.** For the anharmonic `ℓ` and `k : ℕ`, `t > 0`:
`hasDerivAt_gibbsExpectation_pow : HasDerivAt (fun s => ⟨xᵏ⟩_s) (−Cov_t[ℓ, xᵏ]) t`, by `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
on numerator `∫ xᵏ e^{−sℓ}` and denominator `∫ e^{−sℓ}` with the dominating function `|x|ᵏ ℓ(x) e^{−(t/2)ℓ(x)}` on the ball
`|s − t| < t/2` (valid because `ℓ ≥ 0`), then the quotient rule. Corollary `gibbsCov_eq_neg_deriv : Cov_t[ℓ, xᵏ] = −deriv (⟨xᵏ⟩_·) t`,
and by linearity for the probe `(B/2)x² + bx` of tide `covK-anharmonic` (so tide 54's rate for `Cov[ℓ, ψ]` is a rate for
`−d⟨ψ⟩/dt`).

**C. (optional) The `γ`-version of A.** Define `covKFormulaLoc t γ H T B b` with `S = (tH + γ1)⁻¹` (the note's actual eq:covK) and
prove it equals `−∂ₜ` of `½ tr(BS) + bᵀ(−½ S (tT:S))` (all four terms survive); needs the derivative of `s ↦ (sH + γ1)⁻¹`
(`−S H S`), i.e. differentiating a matrix inverse along a line.

## Questions

1. Is the observation right as stated — in particular that eq:covK's four terms are exactly `−∂ₜ[½ tr(BS) + bᵀ meanShift]` for
   `S = (tH + γ)⁻¹` including `γ`, and that terms 2 and 4 cancel at `γ = 0`? Is this how the note's authors would describe eq:covK
   ("lem:laplace_cov2 applied to `V`") or is it a new remark worth staging?
2. For B: is the dominating function `|x|ᵏ ℓ(x) e^{−(t/2)ℓ(x)}` and the ball `|s − t| < t/2` the right choice, and is the
   `HasDerivAt` of the quotient best assembled by `HasDerivAt.div` on numerator/denominator (with `Z > 0`) and then identified with
   `−Cov` by `field_simp`/`ring`? Any pitfall in the measurability/`ae` hypotheses of `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   in this pinned Mathlib (the `TiltInterpolation` file used it successfully for bounded tilts)?
3. For C: the cleanest Mathlib route to `HasDerivAt (fun s => (s • H + γ • 1)⁻¹) (−S * H * S) t` — `Matrix.inv` as `Ring.inverse` on
   the matrix ring and `hasFDerivAt_ring_inverse`, or avoid it by working with `IsUnit` and `Matrix.mul_nonsing_inv` identities
   (e.g. differentiate the identity `S(s)(sH + γ) = 1`)?
4. Scope and vote (A+B, with C optional)?
