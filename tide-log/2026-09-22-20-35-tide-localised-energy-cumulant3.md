# Tide: localised-energy-cumulant3

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); after tide 85 (the LLC as the leading coefficient of `−∂ₜ⟨L⟩_loc = Var_loc(L)`), one derivative further at leading
order: the third cumulant of the localised energy and the second temperature derivative `∂ₜ²⟨L∘A⟩_loc`.
**Seabed:** laplace, commit d0ca324 (worktree `laplace-tide-localised-energy-cumulant3`, branch
`tide/localised-energy-cumulant3` off `main`)
**Started:** 2026-09-22T20:38Z

## Candidates v1 (Claude)

Setting (E2, as in tides 68–85): the exact localised measure, frame coordinates `uᵢ`, `ℓᵢ = anharmonicPotential (λᵢ, αᵢ, γᵢ)`,
`aᵢ = g u₀ᵢ`. Landed (tide 85): `∂ₜ⟨L∘A⟩_loc = −Var_loc(L∘A)` exactly, `Var_loc(L∘A) = ∑ᵢ Var_loc,ᵢ(ℓᵢ)`, `t²Var_loc(ℓ) → ½`,
`t²⟨ℓ²⟩_loc → 3/4`; the localised Stein recursion `(tλ + g)m_{k+1} + (tα/2)m_{k+2} + (tγ/6)m_{k+3} = k m_{k−1} + a m_k` (tide 77);
the leading localised moments `t²m₃ → c₃ = −5α/(2λ³) + 3a/λ²` (`locThirdCoeff`), `t²m₄ → 3/λ²`, `t³m₅ → c₅ = −35α/(2λ⁴) + 15a/λ³`
(`locFifthCoeff`), `t³m₆ → 15/λ³`, all with `O(1/t)` remainders; even envelopes through degree 8 (tide 85's template).

**A. The signed localised seventh moment is `O(t⁻⁴)`.** From the Stein recursion at `k = 4`,
`t⁴m₇ = (6/γ)[4t(t²m₃ − c₃) + a t(t²m₄ − 3/λ²) − λt(t³m₅ − c₅) − g(t³m₅) − (α/2)t(t³m₆ − 15/λ³)]` because the `O(t)` terms cancel exactly:
`4c₃ + 3a/λ² − λc₅ − (α/2)(15/λ³) = 0` (Stein consistency of the leading coefficients), hence `|t⁴⟨x⁷⟩_loc| ≤ K` eventually. Plus the
localised even envelopes of degrees 10 and 12 (`|t⁵⟨x¹⁰⟩_loc|`, `|t⁶⟨x¹²⟩_loc|` bounded, or the weaker `t⁴`-scaled versions) and the odd
envelopes 9, 11 via `|x|⁹ ≤ (x⁸ + x¹⁰)/2`, `|x|¹¹ ≤ (x¹⁰ + x¹²)/2`. (The unlocalised `seventhMoment_bound : |t⁴m₇| ≤ K` is landed;
this is its localised analogue, obtained from the recursion rather than an expansion.)

**B. The localised energy's third moment and third cumulant at leading order.**
`ℓ³ = (λ/2)³x⁶ + (λ²α/8)x⁷ + (λ²γ/32 + λα²/24)x⁸ + (λαγ/48 + α³/216)x⁹ + (λγ²/384 + α²γ/288)x¹⁰ + (αγ²/1152)x¹¹ + (γ/24)³x¹²`, so
`|t³⟨ℓ³⟩_loc − 15/8| ≤ K/t` (the `x⁶` term gives `(λ³/8)(15/λ³)`; `x⁷` needs A's signed bound; `x⁸…x¹²` the envelopes), and with tide 85's
`⟨ℓ²⟩`, `⟨ℓ⟩` rates: **`|t³ κ₃,loc(ℓ) − 1| ≤ K/t`**, `κ₃ = ⟨ℓ³⟩ − 3⟨ℓ²⟩⟨ℓ⟩ + 2⟨ℓ⟩³` (`15/8 − 3·(3/4)(1/2) + 2/8 = 1`): the third cumulant of a
`Gamma(½, t)` energy, unchanged at leading order by the localiser and the anchor.

**C. The second temperature derivative of the localised energy on E2 (the headline).** Exactly, on the frame family,
`∂ₜ⟨ℓᵢ(uᵢ)²⟩_loc = −Cov_loc[L∘A, ℓᵢ²] = −Cov_1D,ᵢ[ℓᵢ, ℓᵢ²]` and `∂ₜ⟨ℓᵢ⟩_loc = −Cov_1D,ᵢ[ℓᵢ, ℓᵢ]` (tide 77's derivative identity with
two-coordinate integrability, coordinate independence), so `∂ₜ Var_loc,ᵢ(ℓᵢ) = −κ₃,loc,ᵢ(ℓᵢ)` and, with tide 85's exact splitting,
**`∂ₜ² ⟨L∘A⟩_loc = −∂ₜ Var_loc(L∘A) = ∑ᵢ κ₃,loc,ᵢ(ℓᵢ)`** exactly; therefore **`|t³ ∂ₜ²⟨L∘A⟩_loc − d| ≤ K/t`**: the LLC `d/2` governs the
second temperature derivative too (`∂ₜ²⟨L⟩ = 2·(d/2)/t³`, the `Gamma(d/2, t)` law's third cumulant `2k/t³`). Together with tide 85:
`t⟨L⟩ → d/2`, `−t²∂ₜ⟨L⟩ → d/2`, `t³∂ₜ²⟨L⟩ → d` — the first three temperature derivatives of the localised free-energy-like quantity
are governed by the one number `d/2`.

**D (optional).** The direct multi-d third cumulant `⟨(L∘A)³⟩ − 3⟨(L∘A)²⟩⟨L∘A⟩ + 2⟨L∘A⟩³ = ∑ᵢ κ₃,ᵢ` (cumulant additivity over the product
measure) — needs triple-coordinate integrability; defer unless cheap.

Sizing: A ~150 lines (recursion algebra + consistency identity + envelopes), B ~200 (`⟨ℓ³⟩` expansion: 7 monomials, assembly, cumulant
algebra), C ~250 (two derivative identities per coordinate with integrability, independence reductions, the second derivative via
`deriv` of `deriv`, the sum). Target A + B + C.

## Numerical check

`numcheck_localised_energy_cumulant3.py` (two frame coordinates, anchor off the minimum; 2D quadrature for the direct cumulant at
`t = 40`): (a) `t⁴⟨x⁷⟩_loc` converges per coordinate (`−13.36`, `60.87` at `t = 640`) and the leading Stein consistency
`4c₃ + 3a/λ² − λc₅ − (α/2)(15/λ³)` tends to `0` (its finite-`t` value is the `O(1/t)` error of the moment estimates; symbolically it is
exactly `0` with `c₃ = locThirdCoeff`, `c₅ = locFifthCoeff` — checked with sympy); (b) `t³⟨ℓ³⟩_loc → 15/8` (`1.8687, 1.8654` at `t = 640`),
`t³κ₃ → 1` per coordinate (`0.99664, 0.99489`), sum `→ 2 = d`; (c) at `t = 40`: `−∂ₜVar_loc(L) = 2.92607e−5`, `∑κ₃ᵢ = 2.92607e−5`, the direct
2D `κ₃(L) = 2.92607e−5`, `∂ₜ²⟨L⟩ = 2.92607e−5`; (d) `t³∂ₜ²⟨L⟩_loc = 1.934, 1.967, 1.983, 1.992 → 2`.

## GPT-6 Astra v1

Verbatim in `gpt_localised_energy_cumulant3_v1.md` (prompt: `gpt_localised_energy_cumulant3_prompt_v1.md`). Summary: **A, B, C correct;
"the mathematics is correct".** The Stein consistency identity closes exactly (`(−10 + 35/2 − 15/2)α/λ³ + (12 + 3 − 15)a/λ² = 0`; the
prompt's `−3a/λ²` had dropped the explicit `+3a/λ²`), so `locFifthCoeff` is consistent; the `t⁴m₇` formula is right and needs `γ ≠ 0`
(E2's `γ > 0`). All seven `ℓ³` coefficients right; `15/8 − 9/8 + 2/8 = 1`. Degrees 8–12 need only bounded `t⁴`-scaled absolute moments;
degree 7 needs the *signed* bound. The finite-`t` "consistency" numbers are residuals of scaled moments, not values of the identity
(which is identically `0`). C's chain `M₁' = −(M₂ − M₁²)`, `M₂' = −(M₃ − M₁M₂)`, `(M₂ − M₁²)' = −κ₃` correct; keep parameters fixed, supply
the differentiation hypotheses, and use `deriv f = −Var` *locally* (we have it on `(0, ∞)`). **Wording**: not "first three temperature
derivatives" but "the localised mean energy and its first two temperature derivatives" (or the first three derivatives of `−log Z_loc`);
say *cumulants*: for a Gamma law with shape `k` and rate `t` the first three cumulants are `k/t, k/t², 2k/t³`; suggested: "The LLC `d/2`
governs the localised mean energy and its first two temperature derivatives: `t⟨L⟩ → d/2`, `−t²∂ₜ⟨L⟩ → d/2`, `t³∂ₜ²⟨L⟩ → d`. These match
the first three cumulants of a Gamma law with shape `d/2` and rate `t`" — worth stating, but not a convergence-in-law claim; until D is
formalised, call the last exact quantity `∑ᵢ κ₃,ᵢ`. Lean route: prove the coefficient cancellation separately (`field_simp`/`ring`) and
rewrite the scaled recursion into remainder form; separate pointwise identity, linearity and bounds for `ℓ³`; build `HasDerivAt` for the
coordinate variances and their sum first, converting to nested `deriv` only at the end. **Next target**: the second-order energy variance
(needs the missing second-order fifth/sixth moments).

## Vote
- Claude: A + B + C (D deferred)
- GPT-6 Astra: "**Vote: A+B+C, staged with A+B as the firm checkpoint; defer D.**"

## Result

Commit `71ea1a6` on `tide/localised-energy-cumulant3`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/LocalisedEnergyCumulant3.lean` (     919 lines).
A + B + C as voted; D (the direct multi-d cumulant identity) deferred per GPT.
1D: `loc_ratio_bounded4`, `locEven_weighted_bound4`/`locOdd_weighted_bound4` (generic degrees `2k`, `2k+1`, `k ≥ 4`), `locEven_loc_bound4`,
`locOdd_loc_bound4`, `stein_leading_consistency`, `locSeventhMoment_loc_bound4` (the signed seventh moment), `locEnergyCube_eq`,
`energyCube_assembly`, `locEnergyCube_leading`, `locEnergy_leading`, `locEnergyCum3_leading`.
E2: `localised_frame_fun_expectation`, `localisedCovK_frame_fun`, `hasDerivAt_localised_frame_fun`, the integrability suppliers
`integrable_energy_energy_coord`, `integrable_energy_energySq_coord`, `integrable_energy_coord_alone`, `integrable_energySq_coord_alone`,
`integrable_energy_energy_locFamily`, `integrable_energy_energySq_locFamily`, `hasDerivAt_localised_frame_energyVar`,
`localisedVar_energy_eq_frame_sum`, `hasDerivAt_localised_energy_deriv`, `localisedEnergy_deriv2_leading`.

Surprises: the seventh moment costs one Stein recursion plus the exact cancellation of its `O(t)` terms — no new expansion; the
second derivative is `HasDerivAt` of `deriv f` through the local identity `deriv f = −Var` on `(0, ∞)`.
