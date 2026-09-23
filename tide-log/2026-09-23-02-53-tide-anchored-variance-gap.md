# Tide: anchored-variance-gap

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: the anchored Gaussian *variance* of the quadratic energy under the tilted Gaussian (exact, via the landed Wick fourth moment), its `1/t` expansion, and the variance gap against the landed second-order localised variance: three gaps (transform, energy, variance), one coefficient `C₁′`.
**Seabed:** laplace, commit c9e1d26 (tide 95 `anchored-energy-gap` landed)
**Started:** 2026-09-23T02:53Z

## Candidates v1 (Claude)

- **A** (Sampler, general): `tiltedVar_quadForm` — for `P ≻ 0`, `H` symmetric, `Σ = P⁻¹`, `m = P⁻¹v`:
  `⟨(uᵀHu)²⟩_{P,v} − ⟨uᵀHu⟩²_{P,v} = 2·tr((HΣ)²) + 4·(Hm)ᵀΣ(Hm)`; hence `Var_{P,v}(½uᵀHu) = ½tr((HΣ)²) + mᵀHΣHm`.
  Route: shift `u ↦ u + m` (`tiltedExpectation_eq`), Wick fourth moment `gaussian_fourth_moment_matCLM` for `∫(uᵀHu)² gw = Z(tr(HΣ)² + 2tr((HΣ)²))`, second moments for `∫(mᵀHu)² gw = Z(Hm)ᵀΣ(Hm)`, odd moments vanish.
- **B** (Sampler, eigen): `P = tH + gI`, `aᵢ = (Uᵀv)ᵢ`: `t²Var_{tH+gI,v}(½uᵀHu) = ½∑(tλᵢ/(tλᵢ+g))² + t²∑λᵢ²aᵢ²/(tλᵢ+g)³`.
- **C** (Multi): for `t ≥ 1`, `|B − d/2 − (∑aᵢ²/λᵢ − g∑1/λᵢ)/t| ≤ K/t²`, explicit `K`.
- **D** (Multi): `t²Var_loc(L∘A) − t²Var_anch(½uᵀHu) = 2C₁′/t + O(t⁻²)` from tide 87's `localisedVar_energy_order2` and `energyLocCoeff1_anchored`.

## Numerical check

`numcheck_anchored_variance_gap.py` (λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35); `C₁′ = −0.272888`, `2C₁′ = −0.545776`, `∑a²/λ − g∑1/λ = −1.268240`):
formula B equals the direct Gaussian integral to 1e-10 at t = 50; `t(t²Var_anch − d/2)` → −1.26630 (t = 640) vs −1.26824; `t(t²Var_loc − t²Var_anch)`: −0.48797 (t = 40) → −0.54199 (t = 640) vs `2C₁′ = −0.54578`; `t²`-remainder 2.31 → 2.42, converging. (The GPT prompt quoted preliminary figures −0.48 → −0.535 and remainder ≈ 3.4 typed before the run finished; the values here are the run's.)

## Questions for GPT-6 Astra (prompt in `gpt_anchored_variance_gap_prompt_v1.md`)

Correctness of A–D and the cumulant consistency (mean `E₁/t`, variance `2E₁/t`, transform `−sE₁/((1+s)t)`); cleanest odd-moment route (Stein `n = 2` vs reflection); the quadruple-sum → trace bookkeeping; whether to fold in the anchored covariance of two quadratic probes; wording ("three gaps, one coefficient"); vote.

## GPT-6 Astra v1 (summary; verbatim in `gpt_anchored_variance_gap_v1.md`)

- A–D correct (H, P symmetric, P ≻ 0; λᵢ > 0, g ≥ 0). A: `q(u+m) = q(u) + 2b(u) + c`, `E[q²] = tr(HΣ)² + 2tr(HΣHΣ)`, `E[b²] = (Hm)ᵀΣ(Hm)`, odd terms vanish, so `Var(q) = 2tr(HΣHΣ) + 4(Hm)ᵀΣ(Hm)`. B exact. D: `C₁′ = E₁^loc − E₁^anch`, `E₁^anch = ½∑(aᵢ² − g)/λᵢ`; remainder constant `K_loc + K_anch`.
- C: cleaner bounds valid for all `t > 0`: central `0 ≤ ½(u/(u+g))² − ½ + g/u = g²/(u(u+g)) + g²/(2(u+g)²) ≤ 3g²/(2u²)`; noncentral with `r = u/(u+g)`: `0 ≤ 1 − r³ ≤ 3g/u`, so `|t²λ²a²/(tλ+g)³ − a²/(λt)| ≤ 3ga²/(λ²t²)`; constant `K_anch = ∑(3g²/2 + 3gaᵢ²)/λᵢ²` (adopted).
- Cumulant check: `log Λ = −(d/2)log(1+s) − (E₁/t)·s/(1+s) + O(t⁻²)` gives mean `d/2 + E₁/t`, variance `d/2 + 2E₁/t` — consistent, but a consistency check only (no differentiation of the pointwise remainder).
- Odd moments: Stein `n = 2` recommended, reflection acceptable if a general odd-function lemma exists — it does (`integral_odd_mul_gaussian_eq_zero`, no integrability needed), so we use reflection. Wick: split the three contractions and prove them as separate finite-sum identities; `Finset.sum_comm` for binder permutations, `ring` only once binders are aligned.
- Nearby: `Cov_{P,v}(uᵀHu, uᵀKu) = 2tr(HΣKΣ) + 4(Hm)ᵀΣ(Km)` by polarisation — optional, not a dependency of D; deferred.
- Wording: "for fixed admissible parameters and anchor, the exact localised law and the anchored Gaussian prediction have scaled-energy mean, variance and Laplace-transform discrepancies `C₁′/t`, `2C₁′/t`, `−sC₁′/((1+s)^{d/2+1}t)` (+O(t⁻²)), exact minus Gaussian: a single coefficient controls all three leading corrections." Qualifications: scaled energies `t(L∘A)`, `tQ`; if `C₁′ = 0` the discrepancies are `O(t⁻²)`; landed `s`-range, no uniformity claims; `C₁′` includes the anchor–cubic interaction; observable-level asymptotics, not a distributional distance.

## Vote
- Claude: A–D (`tiltedVar_quadForm`, `anchoredGaussianVar_eq`, `anchoredGaussianVar_rate2`, `localisedVar_anchoredGap`), mixed covariance deferred
- GPT-6 Astra: A → B → C → D this tide; mixed covariance only if genuinely cheap

## Result

Commit `e63f59b` on `tide/anchored-variance-gap`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/AnchoredVarianceGap.lean` (     506 lines).
A–D as voted.
Sampler: `inv_apply_symm`, `apply_symm_of_isHermitian`, `transpose_eq_of_isHermitian`, `dotProduct_mulVec_symm_of_isHermitian`,
`dotProduct_mulVec_eq_sum`, `quadForm_sq_mul_eq_sum`, `dotProduct_sq_mul_eq_sum`, `quadForm_mul_dotProduct_mul_eq_sum`,
`integrable_three_coord_mul_gaussianWeight_matCLM`, `integrable_quadForm_sq_mul_gaussianWeight_matCLM`,
`integrable_dotProduct_sq_mul_gaussianWeight_matCLM`, `integrable_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM`,
`integral_quadForm_sq_mul_gaussianWeight_matCLM` (Wick: `Z(tr(HΣ)² + 2tr(HΣHΣ))`), `integral_dotProduct_sq_mul_gaussianWeight_matCLM`,
`integral_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM` (= 0 by reflection), `tiltedVar_quadForm`,
`mul_inv_localisedPrecision_eq_conj`, `trace_sq_mul_inv_localisedPrecision`, `anchoredMean_energy_localised`, `anchoredGaussianVar_eq`.
Multi: `central_var_term_bound`, `noncentral_var_term_bound`, `anchoredGaussianVar_rate2`, `localisedVar_anchoredGap`.

Surprises: the three Wick contractions need only one binder permutation (the second connected contraction is the first after
`c ↔ d`, two `Finset.sum_comm`s); the existing `integral_odd_mul_gaussian_eq_zero` kills the cubic moment with no integrability
hypothesis; `ring` cannot equate `((tλ+g)⁻¹)³` with `((tλ+g)³)⁻¹` (expanded-polynomial inverse is a fresh atom) — normalise with
`simp only [div_eq_mul_inv, ← inv_pow]` first.
