# Tide: localised-covK

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); E3's eq:covK on the exact localised measure at leading order (tides 63/69/73 follow-up).
**Seabed:** laplace, commit bfac237 (worktree `laplace-tide-localised-covK`, branch `tide/localised-covK` off
`tide/covK-order2-multi` — a linear chain, for tide 75's `prod_rate`)
**Started:** 2026-09-22T17:22Z

## Candidates v1 (Claude)

Setting: the 1D anharmonic oscillator `ℓ = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` (`λ, γ > 0`, `α² < 3λγ`) with E3's isotropic localiser
(`g ≥ 0`, anchor `x₀`, `a = g x₀`, `φ = e^{ax − (g/2)x²}`, `⟨·⟩_loc = ⟨·φ⟩/⟨φ⟩`); E2's rotated separable oscillator with the isotropic
localiser (`u = Qᵀ(w − c)`, frame anchor `u₀ = Qᵀ(w₀ − c)`, `aᵢ = g u₀ᵢ`). The covariance is always between the *unlocalised* energy
`ℓ` (resp. `L∘A`) and the probe, on the localised measure — the quantity whose Hessian-route prediction is the note's localised eq:covK
(tide 63's `covKFormulaLoc = −∂ₜ` of the displayed localised eq:cov/eq:mean). Write `c = −α/(2λ²) + a/λ` (the leading `t⟨x⟩_loc`,
tide 67), `c₃' = c₃ + 3a/λ²` (the leading `t²⟨x³⟩_loc`, tide 73).

Seabed state. 1D localised moments: `t⟨x⟩_loc → c` (`localisedMean_anharmonic_rate_sharp`, `K/t`), `t⟨x²⟩_loc → 1/λ`
(`locSecondMoment_loc_rate2`, `K/t²`), `t²⟨x³⟩_loc → c₃'` and `t²⟨x⁴⟩_loc → 3/λ²` (`locThirdMoment_loc_rate2`, `locFourthMoment_loc_rate2`,
`K/t`), `t⟨ℓ⟩_loc → ½` (`localisedEnergy_rate`, `K/t`), `⟨ℓ⟩_loc = (λ/2)⟨x²⟩_loc + (α/6)⟨x³⟩_loc + (γ/24)⟨x⁴⟩_loc` (`locEnergy_eq`),
integrability `integrable_pow_locPotential1`, the shared `x²φ` expansion `locSquare_pointwise` (tide 73) and `prod_rate` (tide 75).
Generic separable machinery (`CovKSeparable`, for any family `ℓ : ι → ℝ → ℝ` with nonzero partition functions):
`gibbsExpectation_coord_separable`, `gibbsExpectation_two_coord_separable`, `gibbsExpectation_three_coord_separable`,
`gibbsCov_coord_fun_separable` (`Cov[f(uᵢ), g(uⱼ)] = δᵢⱼ Cov_i[f, g]`), `gibbsCov_finsetSum_left`; the anharmonic-specific
`gibbsCov_energy_coord_pow_separableAnharmonic` and `gibbsCov_energy_pair_separableAnharmonic` (measure family = observable family).
Localised E2: `localisedRotatedAnharmonic_eq_rotated` (the localised rotated potential is `rotated Q c` of the frame separable potential
with family `locPotential1 (λᵢ, αᵢ, γᵢ, g, u₀ᵢ, t)`), `gibbsCov_rotated_of_continuous`, `probe_affineFrame`, `integrable_localised_of_integrable`,
`partitionFunction_localisedAnharmonic_pos`. Tide 63: `covKFormulaLoc` (no anchor term) `= −∂ₜ(½tr(BS) + bᵀ meanShiftLoc)`.

### A. eq:covK on the exact localised measure at leading order (1D)

`|t²Cov_loc[ℓ, x] − c| ≤ K/t` (`localisedCovK_lin_rate`), `|t²Cov_loc[ℓ, x²] − 1/λ| ≤ K/t` (`localisedCovK_sq_rate`), and for the probe
`ψ = (B/2)x² + bx`: `|t²Cov_loc[ℓ, ψ] − (B/(2λ) + bc)| ≤ K/t` (`localisedCovK_rate`).
Route: `Cov_loc[ℓ, x] = ⟨ℓx⟩_loc − ⟨ℓ⟩_loc⟨x⟩_loc`, `⟨ℓx⟩_loc = (λ/2)⟨x³⟩_loc + (α/6)⟨x⁴⟩_loc + (γ/24)⟨x⁵⟩_loc`, so
`t²Cov_loc[ℓ, x] = (λ/2)t²⟨x³⟩_loc + (α/6)t²⟨x⁴⟩_loc + (γ/24)(t³⟨x⁵⟩_loc)/t − (t⟨ℓ⟩_loc)(t⟨x⟩_loc)` and the constants assemble to
`(λ/2)c₃' + (α/6)(3/λ²) − ½c = c` (check: `−5α/(4λ²) + 3a/(2λ) + α/(2λ²) + α/(4λ²) − a/(2λ) = −α/(2λ²) + a/λ`). New inputs: a bounded
`t³⟨x⁵⟩_loc` (from the shared expansion times `x³`: `x⁵φ = x⁵ + ax⁶ + x³·R + p₃x⁷ + p₄x⁸`, signed `x⁵` by `fifthMoment_lead`, the rest by
even envelopes up to `x¹⁴`) and `0 ≤ t³⟨x⁶⟩_loc ≤ K` (`φ ≤ e^M`, `evenMoment_bound 3`, `D ≥ ½`). For `x²`:
`t²Cov_loc[ℓ, x²] = (λ/2)t²⟨x⁴⟩_loc + (α/6)(t³⟨x⁵⟩_loc)/t + (γ/24)(t³⟨x⁶⟩_loc)/t − (t⟨ℓ⟩_loc)(t⟨x²⟩_loc) → 3/(2λ) − 1/(2λ) = 1/λ`.
**Reading**: at leading order the localiser enters eq:covK only through the anchor, `bc = −bα/(2λ²) + b a/λ` — the `a/λ` term is
`−∂ₜ` of the anchor term `a/(tλ + g)` of the displayed localised eq:mean at leading order; with the anchor at the minimiser
(`a = 0`) the leading constants are the unlocalised ones (`g` alone does not enter).

### B. E2: the general quadratic probe on the exact localised measure

Generic two-family lemmas (measure family `ℓ`, observable family `φ`, both `ι → ℝ → ℝ`, with the needed integrability):
`gibbsCov_energy_coord_separable`: `Cov[∑ₖ φₖ(uₖ), f(uᵢ)] = Cov_i[φᵢ, f]`; `gibbsCov_energy_pair_separable` (`i ≠ j`):
`Cov[∑ₖ φₖ(uₖ), uᵢuⱼ] = ⟨x⟩_j Cov_i[φᵢ, x] + ⟨x⟩_i Cov_j[φⱼ, x]` (the anharmonic proof with the families abstracted). Instantiated on the
localised frame measure (family `locPotential1 (λᵢ, αᵢ, γᵢ, g, u₀ᵢ, t)`) with the unlocalised energies `ℓᵢ` as observables:
`|t²Cov_loc[L, uᵢ²] − 1/λᵢ| ≤ K/t`, `|t²Cov_loc[L, uᵢ] − cᵢ| ≤ K/t`, `|t²Cov_loc[L, uᵢuⱼ]| ≤ K/t` (`i ≠ j`; `(t⟨x⟩_j,loc)(t²Cov_i,loc)/t`),
then the quadratic probe: `|t²Cov_loc[L, ψ̃] − ∑ᵢ (B̃ᵢᵢ/(2λᵢ) + b̃ᵢcᵢ)| ≤ K/t` (`localisedCovK_separable_quadratic_rate`) and the ambient
E2 form `|t²Cov_loc[L∘A, ψ] − ∑ᵢ (B̃ᵢᵢ/(2λᵢ) + b̃ᵢcᵢ)| ≤ K/t` (`localisedRotatedAnharmonic_covK_rate`; `B̃ = QᵀBQ`, `b̃ = Qᵀb`,
`cᵢ = −αᵢ/(2λᵢ²) + g u₀ᵢ/λᵢ`), via `localisedRotatedAnharmonic_eq_rotated`, `gibbsCov_rotated_of_continuous`, `probe_affineFrame`.

### C. Against the displayed localised eq:covK (remark, not formalised)

Tide 63's `covKFormulaLoc t g H T B b` has leading term `∑ᵢ (B̃ᵢᵢ/(2λᵢ) − b̃ᵢαᵢ/(2λᵢ²))/t²` — the unlocalised constant — because it omits
the anchor term (it is `−∂ₜ` of `½tr(BS) + bᵀ meanShiftLoc`, without `gS(w₀ − c)`). B shows the exact localised covariance's leading
constant carries in addition `∑ᵢ b̃ᵢ g u₀ᵢ/λᵢ = bᵀ g H⁻¹(w₀ − c)`, i.e. `−∂ₜ` of the anchor term at leading order. So the displayed
localised eq:covK is exact at leading order iff the anchor term is included (or `w₀ = w*`). Formalising the matrix expansion of
`covKFormulaLoc` itself (rational functions of `t` in `locS`) is left as a follow-up.

### D. Follow-up recorded, not claimed: the second order

Numerically (below) the `1/t` coefficients of `t²Cov_loc[ℓ, x]` and `t²Cov_loc[ℓ, x²]` are `2c'` and `2c₂'` (tides 72/73's second-order
localised mean and second-moment coefficients), i.e. the derivative reading `Cov_loc = −∂ₜ⟨·⟩_loc` persists coefficientwise at second
order under localisation, as it did without (tide 71: `C' = 2B`). Proving it needs either a Stein identity for the localised measure or
the `x³φ`, `x⁴φ` expansions to second order; deferred.

Proposed bundle: A + B (C, D as remarks). Line estimate ~650 (generic lemmas ~150, 1D ~250, E2 ~250).

Numerical check (`numcheck_localised_covK.py`, 1D quadrature, `λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`): `t²Cov_loc[ℓ, x] = 0.16909,
0.16527, 0.16303, 0.16236` at `t = 10, 40, 160, 640` vs `c = 0.162130`; `t²Cov_loc[ℓ, x²] = 0.65227, 0.73655, 0.76083, 0.76711` vs
`1/λ = 0.769231`; the `1/t` coefficients `t(t²Cov − const) → 0.1487` vs `2c' = 0.150301` and `→ −1.3544` vs `2c₂' = −1.357602`.

## Numerical check

`numcheck_localised_covK.py`: see the last paragraph of the candidates — leading constants `c`, `1/λ` confirmed; the `1/t` coefficients
match `2c'`, `2c₂'` (recorded as the follow-up D, not claimed).

## GPT-6 Astra v1

Verbatim in `gpt_localised_covK_v1.md` (prompt: `gpt_localised_covK_prompt_v1.md`). Summary: A's constants re-derived (`c`, `1/λ`); the
fifth/sixth `t³`-bounds correct (the fifth is a *signed* cancellation, not `⟨|x|⁵⟩_loc = O(t⁻³)`); a cheaper fifth-moment route via
`|φ − 1| ≤ C|x|` (or `|e^u − 1| ≤ max(1, e^M)|u|`) needing only degrees six and eight — ours (the shared expansion times `x³`, degrees up to
fourteen) is already written and equally valid; the localiser reading right for fixed `g, x₀` ("centred localisation does not change the
leading constant"; the identification with `−∂ₜ(a/(tλ + g)) = aλ/(tλ + g)² → a/λ·t⁻²` fair *at leading order*). Qualifications: the
seabed's `locSecondMoment_loc_rate2` is the second-order statement `|t⟨x²⟩_loc − 1/λ − c₂'/t| ≤ K/t²` (the candidates abbreviated it), so
no contradiction; B's `b̃ = Qᵀb` is right because the seabed's probes are *centred* (`probe_affineFrame`: `ψ(w) = ½(w − c)ᵀB(w − c) + bᵀ(w − c)`).
Infrastructure: the two-family separable decomposition is the right abstraction; the derivative identity for `t`-dependent potentials
(`d/dt⟨ψ⟩ = −Cov[ψ, U + t∂ₜU]`, here `U + t∂ₜU = ℓ`) is conceptually clean but not a cheaper proof, and a fixed-potential
`hasDerivAt_gibbsExpectation` does not justify inserting `locPotential1 t`. **C corrected**: "only for `w₀ = w*`" is too strong for a fixed
probe — agreement iff `bᵀgH⁻¹(w₀ − w*) = 0` (centred localisation, `g = 0`, `b = 0`, or orthogonality); for fixed `g > 0` agreement for
*every* linear probe iff `w₀ = w*`. Wording: "Tide 63's anchor-free `covKFormulaLoc` reproduces the exact localised covariance's leading
coefficient for centred localisation; for a general anchor it omits `bᵀgH⁻¹(w₀ − w*)/t²`, except where that scalar vanishes — the leading
negative time derivative of the anchor displacement in the localised mean." D: the Stein identity `⟨f'⟩_loc = ⟨f(tℓ' + gx − a)⟩_loc` is exact
with clean boundary conditions and gives `(tλ + g)m_{k+1} + (tα/2)m_{k+2} + (tγ/6)m_{k+3} = k m_{k−1} + a m_k`, but does not close the
hierarchy; second order still needs second coefficients for `m₃, m₄` — keep deferred.

## Vote
- Claude: A + B (C as the corrected remark, D deferred)
- GPT-6 Astra: "A + B, with corrected C as a remark and D deferred"

## Result

Commit `e1f9b6f` on `tide/localised-covK`; `lake build` clean, `scripts/sorries` 0/0/0/0. A + B as voted; C as the corrected remark
(centred localisation or ), D deferred.
`Laplace/Multi/LocalisedCovK.lean` (    1139 lines): `gibbsCov_energy_coord_separable`, `gibbsCov_energy_pair_separable` (generic, two families),
`locN₆`…`locN₁₄`, `locFifth_pointwise`, `locFifth_expansion`, `locFifth_bound`, `locSixth_bound`, `loc_ratio_bounded`,
`locFifth_loc_bound`, `locSixth_loc_bound`, `order2_to_order1`, `covK_loc_lin_assembly`, `covK_loc_sq_assembly`,
`locEnergyMul_eq`, `locEnergyMulSq_eq`, `localisedEnergy_leading`, `locSecondMoment_loc_leading`, `locMean_loc_leading`,
`localisedCovK_lin_rate`, `localisedCovK_sq_rate`, `localisedCov_probe_eq`, `localisedCovK_rate` (A); `locFamily`,
`separablePotential_locFamily`, `localisedRotatedAnharmonic_eq_rotated_locFamily`, `integrable_locFamily_of_integrable`,
`localisedRotated_gibbsCov_eq`, `partitionFunction_locFamily_ne`, `integrable_energy_*_locFamily`, `localisedCovK_frame_coord`,
`localisedCovK_frame_pair`, `localisedCovK_frame_sq/lin/offdiag/pair_rate`, `localisedCovK_quadratic_split`,
`localisedCovK_frame_quadratic_rate`, `localisedRotatedAnharmonic_covK_rate` (B).

Surprises: none mathematical — the constants came out as predicted (`c`, `1/λ`), and GPT's independent check agreed. The
two-family generic decomposition is the seabed's anharmonic proof with the families abstracted; the E2 quadratic split is the
seabed's `gibbsCov_energy_quadratic_split` transported through the rotation lemma and re-proved on the frame localised measure.
GPT's cheaper fifth-moment route (`|φ − 1| ≤ C|x|`) is noted; ours (the shared expansion times `x³`) was already written.
