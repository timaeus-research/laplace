You are GPT-6 Astra consulting on a Lean 4 + Mathlib formalisation tide ("laplace" seabed: Laplace asymptotics of Gibbs expectations for
the quartic anharmonic oscillator, with the isotropic Gaussian localiser of a research note's E3; eq:covK is the note's Hessian-route
formula for `Cov_t[L, ψ]`, and its localised version is `−∂ₜ` of the displayed localised eq:cov/eq:mean). Below are the candidates for
the tide. Please answer:

1. Are A and B correct as stated? Check independently the leading constant `c = −α/(2λ²) + a/λ` of `t²Cov_loc[ℓ, x]` (from
   `(λ/2)c₃' + (α/6)(3/λ²) − ½c` with `c₃' = −5α/(2λ³) + 3a/λ²`) and `1/λ` for `x²`, and the claim that `t³⟨x⁵⟩_loc` and `t³⟨x⁶⟩_loc` are
   bounded. Is the reading "at leading order the localiser enters only through the anchor (`b a/λ`); `g` alone does not" right, and is
   its identification with `−∂ₜ` of the anchor term `a/(tλ + g)` of the localised eq:mean fair?
2. Is the two-family generic separable covariance decomposition (measure family ≠ observable family) the right infrastructure, or is
   there a slicker route to `Cov_loc[L∘A, ψ]` for quadratic probes (e.g. via the exact derivative identity `Cov_loc[L, ψ] = −∂ₜ⟨ψ⟩_loc`, which
   holds because the localiser `(g/(2t))|w − w₀|²·t = (g/2)|w − w₀|²` is `t`-independent in the exponent — do we already have such an
   identity for `t`-dependent potentials in the seabed's `hasDerivAt_gibbsExpectation` lemmas?)? Pitfalls?
3. C: is the diagnosis right that tide 63's `covKFormulaLoc` (defined without the anchor term) is exact at leading order only for
   `w₀ = w*`, the exact localised covariance carrying the extra `bᵀ g H⁻¹(w₀ − w*)/t²`? How should this be worded against the note?
4. D: the numerics show the `1/t` coefficients are `2c'`, `2c₂'` — the derivative reading at second order under localisation. Is there a
   cheap rigorous route (an integration-by-parts/Stein identity for the localised measure: `⟨f'⟩_loc = ⟨f (tℓ' + g(x − x₀))⟩_loc`), and
   would it make the second order reachable in this tide? Or keep D as a follow-up?
5. Vote: which single bundle do you back?

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
