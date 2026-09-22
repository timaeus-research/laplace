# Tide `covK-derivative-multi` (laplace seabed, local): candidates for GPT-6 Astra

## Context

Tide `covK-derivative` proved in one dimension `d/ds ⟨xᵏ⟩_s = −Cov_t[ℓ, xᵏ]` for the anharmonic Gibbs measure by dominated
differentiation (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `s > t/2`, bound `|x|^k ℓ e^{−(t/2)ℓ}` using `ℓ ≥ 0`), and at
the formula level `covKFormula = −∂ₜ[½ tr(BS) + b⬝meanShift]`. The seabed's `d`-dimensional separable measure
`e^{−t L(u)}`, `L(u) = ∑ᵢ ℓᵢ(uᵢ)` on `Fin d → ℝ` (`separableAnharmonic`), has: integrability of every monomial
`∏ₙ uₙ^{eₙ} e^{−tL}` (`integrable_monomial_separableAnharmonic (e : ι → ℕ)`), of `ℓₖ(uₖ) uᵢ^m e^{−tL}` and `ℓₖ(uₖ) uᵢuⱼ e^{−tL}`, of
`L ψ e^{−tL}` given the coordinate pieces (`integrable_energy_mul_separableAnharmonic`), positivity of its partition function, the
exact covariances `Cov_L[L, uᵢ^m] = Cov_{ℓᵢ}[ℓᵢ, xᵐ]` and `Cov_L[L, uᵢuⱼ]`, the quadratic-probe split
`Cov_L[L, ∑ᵢⱼ Bᵢⱼ/2 uᵢuⱼ + ∑ bᵢuᵢ] = ∑ᵢⱼ Bᵢⱼ/2 Cov[L, uᵢuⱼ] + ∑ bᵢ Cov[L, uᵢ]` (`gibbsCov_energy_quadratic_split`), continuity of
`L`, and the transport of expectations and covariances of continuous observables to E2's rotated oscillator `L∘A`
(`gibbsExpectation_rotated_of_continuous`, `gibbsCov_rotated_of_continuous`, `probe_affineFrame`).

## Candidates

**A. Monomials.** `hasDerivAt_gibbsExpectation_monomial (e : ι → ℕ) : HasDerivAt (fun s => ⟨∏ₙ uₙ^{eₙ}⟩_s) (−Cov_t[L, ∏ₙ uₙ^{eₙ}]) t`
for `t > 0`, by dominated differentiation on `s > t/2` with bound `‖L(u) ∏ uₙ^{eₙ} e^{−(t/2)L(u)}‖` (integrable by
`integrable_energy_mul_separableAnharmonic` at `t/2`, since `L ≥ 0`), and the quotient rule with `Z(s) = ∫e^{−sL}`.

**B. Quadratic probes.** `hasDerivAt_gibbsExpectation_quadratic (B b) : HasDerivAt (fun s => ⟨∑ᵢⱼ Bᵢⱼ/2 uᵢuⱼ + ∑ bᵢuᵢ⟩_s)
(−Cov_t[L, ψ]) t`, by linearity of `⟨·⟩_s` (on `s > 0`, via `congr_of_eventuallyEq`) and A for `uᵢuⱼ`, `uᵢ`, then
`gibbsCov_energy_quadratic_split`.

**C. E2's oscillator.** `hasDerivAt_gibbsExpectation_rotatedAnharmonic_probe : HasDerivAt (fun s => ⟨½(w−c)ᵀB(w−c) + b⬝(w−c)⟩_{L∘A, s})
(−Cov_t[L∘A, ψ]) t`, by transporting B through the rotation (both the expectation at every `s` and the covariance at `t`). Together
with tide `covK-derivative`'s `covKFormula_eq_neg_deriv` this makes both sides of eq:covK `−∂ₜ` of both sides of eq:cov + eq:mean
for E2's oscillator (a remark, not a new theorem).

## Questions

1. Any pitfall in the `d`-dimensional DCT (measure `volume` on `Fin d → ℝ`, the bound `‖L ∏uₙ^{eₙ} e^{−(t/2)L}‖` with
   `Integrable.norm`, measurability by continuity of polynomials and of `L`)? Is `L ≥ 0` (from `ℓᵢ ≥ 0`, tide `unique-minimum`)
   correctly what makes `e^{−sL} ≤ e^{−(t/2)L}` on `s > t/2`?
2. For B, is it cleaner to prove `HasDerivAt` for `⟨ψ⟩_s` directly by one DCT on `ψ e^{−sL}` (bound `‖L ψ e^{−(t/2)L}‖`, integrable
   by the coordinate pieces) rather than through monomials and linearity? The direct route needs `Integrable (ψ e^{−tL})` and
   `Integrable (L ψ e^{−tL})` for the probe only, which the seabed has.
3. For C: the transport `⟨ψ⟩_{L∘A, s} = ⟨ψ∘A⁻¹⟩_{L, s}` holds for every `s` (`gibbsExpectation_rotated_of_continuous`), so the
   `HasDerivAt` transfers by `funext`; anything subtle about the probe `probe_affineFrame` identity under the derivative?
4. Scope and vote (A+B+C, or direct-B+C)?
