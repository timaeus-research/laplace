# Tide: localised-llc

**Direction (user):** auto mode ("Continue with what you think best"); chosen direction: E3's localised LLC on the exact anharmonic localised measure — `t⟨L∘A⟩_loc = ½ tr(tH(tH + gI)⁻¹) + O(1/t)` on E2's rotated oscillator with the isotropic localiser, via the localised second/third/fourth moments and separability; corollary `|t⟨L∘A⟩_loc − d/2| ≤ K/t`.
**Seabed:** laplace, commit 376199c (branch `tide/localised-llc` off `main`)
**Started:** 2026-09-22T14:25Z

## Candidates v1 (Claude)

Setting as in tides 65–68: `ℓ = λx²/2 + αx³/6 + γx⁴/24`, localiser strength `g ≥ 0`, anchor `x₀`, weight `φ = e^{y}`,
`y = g x₀ x − (g/2)x²`, localised measure = `gibbsExpectation (locPotential1 …) t` with `⟨f⟩_loc = ⟨fφ⟩/⟨φ⟩`
(`gibbsExpectation_locPotential1`). E3's localised LLC (Gaussian derivation in the note; tides `localised-llc-bounds`,
`ula-localised` for Gaussian targets) is `λ̂_loc = ½ tr(tH(tH + γI)⁻¹) = ½∑ᵢ tλᵢ/(tλᵢ + γ)`.

- **A (1D localised energy).** `|t⟨ℓ⟩_loc − ½·tλ/(tλ + g)| ≤ K/t`. Route: `t⟨ℓ⟩_loc = (λ/2)t⟨x²⟩_loc + (α/6)t⟨x³⟩_loc + (γ/24)t⟨x⁴⟩_loc`
  (linearity under the localised potential; integrability of `xᵏ e^{−t·locPotential1}` from `integrable_pow_locWeight`);
  `t⟨x²⟩_loc = t·Var_loc + (t⟨x⟩_loc)²/t` with `|t·Var_loc − t/(tλ + g)| ≤ K/t` (tide 68's `localisedVar_sub_displayed_rate` times `t`)
  and `|t⟨x⟩_loc| ≤ |c| + K` (tide 67); `t⟨x³⟩_loc = t⟨x³φ⟩/⟨φ⟩` with `x³φ = x³ + g x₀x⁴ − (g/2)x⁵ + x³(φ − 1 − y)`,
  `|x³(φ − 1 − y)| ≤ C₁|x|⁵ + C₂|x|⁷ ≤ even`, so `|t⟨x³φ⟩| ≤ K/t` (`thirdMoment_bound` + even moments) and `D ≥ ½`;
  `0 ≤ t⟨x⁴⟩_loc ≤ e^{g x₀²/2} t⟨x⁴⟩/D ≤ K/t`.
- **B (E2, `d` dimensions).** `|t⟨L∘A⟩_loc − ½ tr(tH · (tH + gI)⁻¹)| ≤ K/t` on E2's rotated oscillator with the isotropic
  localiser, the observable being the *unlocalised* energy `L∘A = rotatedAnharmonic` under the localised measure. Route:
  `⟨L∘A⟩_loc = ∑ᵢ ⟨ℓᵢ⟩_loc,i` (transport `gibbsExpectation_rotated_of_continuous`, `gibbsExpectation_finsetSum` +
  `gibbsExpectation_coord_separable` on the localised separable potential; integrability from `integrable_localised_of_integrable`
  and `integrable_coord_energy_separableAnharmonic`), `½ tr(tH(tH + gI)⁻¹) = ½∑ᵢ tλᵢ/(tλᵢ + g)` (`locS_rot`, `conj_mul_conj`,
  `Matrix.trace_mul_cycle`), then `sum_rate_div` with A coordinatewise.
- **C (optional).** The leading form `|t⟨L∘A⟩_loc − d/2| ≤ K/t` and the sign of the first correction: `½ tr(tH(tH + gI)⁻¹) =
  d/2 − ½∑ᵢ g/(tλᵢ + g)`, i.e. localisation *lowers* the LLC by `(g/2t)tr(H⁻¹) + O(t⁻²)` — a corollary of B by algebra.

Rationale: GPT (tide 68) approved this as an "explicitly `O(t⁻¹)`-accurate localised-energy corollary": E3's localised LLC formula
holds on a non-Gaussian target at leading order in the localiser; it completes the E3 trio (mean, covariance, LLC) on the exact
anharmonic localised measure. Caveat to state: not an exact finite-`t` identity (a displaced anchor contributes `(t/2)μᵀHμ = O(1/t)`),
and the `1/t` coefficient is not identified.

## Numerical check

`numcheck_localised_llc.py` (1D `λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`; `d = 2` as in tide 66): `t(t⟨ℓ⟩_loc − ½tλ/(tλ + g))
= −0.028, −0.041, −0.044, −0.045` at `t = 10, 40, 160, 640` and `t²⟨x³⟩_loc = 0.117, 0.075, 0.061, 0.057` (so `t⟨x³⟩_loc = O(1/t)`);
`d = 2`: `t(t⟨L∘A⟩_loc − ½tr(tH(tH + gI)⁻¹)) = 0.25, 0.35, 0.39` at `t = 10, 40, 160` — the `O(1/t)` claims hold, and the
correction coefficient is visibly nonzero (so `O(1/t)` is sharp, not just an upper bound).

## GPT-6 Astra v1

Verbatim in `gpt_localised_llc_v1.md` (prompt `gpt_localised_llc_prompt_v1.md`). Summary: A and B correct under the standing
assumptions; `t⟨x²⟩_loc = tV + (tm)²/t` with `|tV − t/(tλ+g)| ≤ K_V/t`, `|tm| ≤ |c| + K_m` gives the raw second moment at `K/t`
(expose it as a lemma); the cubic identity `x³φ = x³ + g x₀x⁴ − (g/2)x⁵ + x³(φ − 1 − y)` is right, `|x³(φ − 1 − y)| ≤ C₁x⁴ + (C₁+C₂)x⁶ +
C₂x⁸` after `|x|⁵ ≤ x⁴ + x⁶`, `|x|⁷ ≤ x⁶ + x⁸`; `0 ≤ t⟨x⁴⟩_loc ≤ 2e^{g x₀²/2} t⟨x⁴⟩`; proof order: localised polynomial
integrability → cubic/quartic bounds → raw second moment → energy. B: exact product structure, observable = the *unlocalised*
energy, `gibbsExpectation_energy_separableAnharmonic` is not itself the localised identity (prove via the generic
rotation/product/coordinate lemmas on the localised separable potential); trace route `locS_rot` → `conj_mul_conj` → cyclic trace
fine. C: the sign statement holds for the *Gaussian trace prediction* (`½∑ tλᵢ/(tλᵢ+g) = d/2 − ½∑ g/(tλᵢ+g) ≤ d/2`) but B does
*not* determine the sign of the exact energy's `1/t` correction (the error is of that order) — restrict C's sign claim to the
prediction. Wording: "the exact localised anharmonic energy agrees with E3's Gaussian trace prediction up to an absolute `O(t⁻¹)`
error, for fixed localisation strength and anchor"; do not say it identifies the leading localiser correction. The sharper 1D
coefficient exists (`t⟨ℓ⟩_loc − ½tλ/(tλ+g) = [a²/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)]/t + o(1/t)`, `a = g x₀`; ≈ −0.0457 for the
test parameters, matching the numerics) but needs identified `t⁻²` moment coefficients — defer to a separate tide. Pitfalls: keep
the observable explicit; a displaced anchor adds `tλg²x₀²/(2(tλ+g)²)` even for a Gaussian, so the trace is the covariance
contribution only; `t`-dependent potential pointwise; `g = 0` fine. Vote: A + B, C with the sign claim restricted to the trace
prediction; coefficient deferred.

## Vote
- Claude: A + B + C (C = algebra of the trace prediction and the `d/2` corollary)
- GPT-6 Astra: A + B + C (sign claim restricted to the Gaussian trace prediction; coefficient deferred)

## Result

Commit `080a2d8` on `tide/localised-llc`; `lake build` clean, `scripts/sorries` 0/0/0/0. A + B + C as voted (C = the trace
prediction's algebra and the `d/2` corollary; the sign claim is about the prediction only).
`Laplace/Multi/LocalisedAnharmonicLLC.lean` (     577 lines): `locR₄`/`locR₆`/`locR₈`, `locCubic_pointwise`, `gibbsExpectation_const_mul₁`, `exp_neg_locPotential1`,
`integrable_pow_locPotential1`, `partitionFunction_locPotential1_pos`, `locSecondMoment_eq`, `locSecondMoment_rate`,
`locCubic_expansion`, `locCubic_rate`, `locThirdMoment_loc_rate`, `locFourthMoment_loc_le`, `anharmonicPotential_eq_lin`,
`locEnergy_eq`, `localisedEnergy_rate`, `localisedRotatedAnharmonic_energy_coord`, `trace_smul_locS_rot`,
`localisedRotatedAnharmonic_llc_rate`, `trace_smul_locS_rot_eq`, `trace_smul_locS_rot_le`,
`localisedRotatedAnharmonic_llc_leading`.

Surprises: the cubic weight needs only the seabed's *first-order* expansion (`x³φ − x³ − g x₀x⁴ = x³(φ − 1 − g x₀x)`, no `x⁵`
term — GPT's identity was in the variable `y`); with tides 67–68 in place the whole tide is assembly. The section-variable
`include` bit a `rfl` lemma (`rw` with it demanded `0 < lam`).
