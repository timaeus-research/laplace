# Tide: localised-cov

**Direction (user):** auto mode ("Continue with what you think best"); chosen direction: E3/eq:cov with the localiser on the exact localised anharmonic measure — the localised variance `|t·Var_loc − 1/λ| ≤ K/t` and `|Var_loc − 1/(tλ + g)| ≤ K/t²` in 1D via the second-order weight expansion of `x²φ`, and on E2's rotated oscillator `Cov_loc[wⱼ, wₖ] = ∑ᵢ QⱼᵢQₖᵢ Var_loc,i` (frame covariances vanish by separability) with `|Cov_loc − (tH + gI)⁻¹|ⱼₖ ≤ K/t²`; optionally E3's localised LLC `t⟨L∘A⟩_loc = ½ tr(tH(tH + gI)⁻¹) + O(1/t)`.
**Seabed:** laplace, commit faf94e0 (branch `tide/localised-cov` off `main`)
**Started:** 2026-09-22T14:09Z

## Candidates v1 (Claude)

Setting as in tides 65–67: `ℓ = λx²/2 + αx³/6 + γx⁴/24` (`λ, γ > 0`, `α² < 3λγ`), localiser strength `g ≥ 0`, anchor `x₀`, weight
`φ = e^{y}`, `y = g x₀ x − (g/2)x²`; the localised measure `e^{−tℓ − (g/2)(x − x₀)²}` is `gibbsExpectation` of the `t`-dependent
potential `ℓ + (g/(2t))(x − x₀)²` (tide 66's `gibbsExpectation_localisedAnharmonic_id`). E3's eq:cov with the localiser reads
`Σ = S + O(S²)`, `S = (tH + γI)⁻¹`.

- **A (1D localised variance).** `localisedVar := gibbsCov (ℓ + (g/(2t))(x − x₀)²) t id id = ⟨x²φ⟩/⟨φ⟩ − (⟨xφ⟩/⟨φ⟩)²`;
  `|t·Var_loc − 1/λ| ≤ K/t` and `|Var_loc − 1/(tλ + g)| ≤ K/t²` — eq:cov with its `O(S²)` remainder in one dimension.
  Route: `x²φ = x² + g x₀ x³ + c₂ x⁴ + R'` with `|R'| ≤ A'x⁴ + B'x⁶ + C'x⁸` (from tide 67's `locWeight_taylor2`,
  `abs_locExponent_cube_le`; `x²·E|y|³ ≤ 4E(|gx₀|³|x|⁵ + (g/2)³x⁸)`, `|x|⁵ ≤ (x⁴ + x⁶)/2`), `⟨x³⟩ = O(t⁻²)` (`thirdMoment_bound`),
  `⟨x⁴⟩ ≤ C/t²`, so `|t⟨x²φ⟩ − 1/λ| ≤ K/t`; with `|⟨φ⟩ − 1| ≤ K/t`, `D ≥ ½`, and `|t⟨xφ⟩| ≤ |c| + K` (tide 67),
  `t·Var = tN₂/D − (tN₁)²/(tD²)` gives the `K/t` rate; `|1/(λt) − 1/(tλ + g)| = g/(λt(tλ + g)) ≤ g/(λ²t²)` gives the displayed form.
- **B (E2, `d` dimensions).** For E2's rotated oscillator with the isotropic localiser, for all ambient `j, k`:
  `Cov_loc[wⱼ, wₖ] = ∑ᵢ Qⱼᵢ Qₖᵢ Var_loc,i` (frame covariances vanish by separability: `gibbsCov_coord_separable` on the localised
  separable potential, transport `gibbsCov_rotated_of_continuous`, bilinearity `gibbsCov_linear_combination` +
  `gibbsCov_const_add_both`, integrability by `integrable_localised_of_integrable`), hence
  `|Cov_loc[wⱼ, wₖ] − (locS g H t)ⱼₖ| ≤ K/t²` with `locS g H t = (tH + gI)⁻¹ = Q diag(1/(tλᵢ + g)) Qᵀ` (`locS_rot`) — eq:cov's
  displayed right-hand side with its `O(S²)` remainder on the exact localised measure; and `|t·Cov_loc[wⱼ, wₖ] − (Q diag(1/λ) Qᵀ)ⱼₖ| ≤ K/t`.
- **C (optional: E3's localised LLC).** `|t⟨L∘A⟩_loc − ½ tr(tH (tH + gI)⁻¹)| ≤ K/t`, i.e. `t⟨L∘A⟩_loc = ½∑ᵢ tλᵢ/(tλᵢ + g) + O(1/t)`
  — the note's localised LLC formula (certified so far only for Gaussian targets, tides `localised-llc-bounds`, `ula-localised`) on
  the exact anharmonic localised measure. Route: `t⟨ℓ⟩_loc = (λt/2)⟨x²⟩_loc + (αt/6)⟨x³⟩_loc + (γt/24)⟨x⁴⟩_loc`;
  `⟨x²⟩_loc = Var_loc + mean² = 1/(tλ + g) + O(t⁻²)` (A and tide 67), `t⟨x³⟩_loc = O(1/t)` (expand `x³φ = x³ + g x₀ x⁴ + x³(φ − 1 − y)`,
  `|x³(φ − 1 − y)| ≤ C₁|x|⁵ + C₂|x|⁷`), `t⟨x⁴⟩_loc ≤ e^{g x₀²/2} t⟨x⁴⟩/⟨φ⟩ = O(1/t)`; sum over coordinates by separability.

Rationale: the sibling of tides 65–67 for eq:cov; closes E3's eq:cov for a non-Gaussian target in the note's own notation and, with
C, the localised LLC formula of E3 on the same measure. No new analysis beyond tide 67's expansion applied to `x²φ` and `x³φ`.

## Numerical check

`numcheck_localised_cov.py` (1D: `λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`; `d = 2` as in tide 66): `t(t·Var_loc − 1/λ) = −0.64,
−0.69, −0.70, −0.70` and `t²(Var_loc − 1/(tλ + g)) = −0.20, −0.22, −0.23, −0.23` at `t = 10, 40, 160, 640`; in `d = 2` the frame
off-diagonal covariance is `< 1e-18` (exactly zero by separability) and `t²·max|Cov_w − (tH + gI)⁻¹| = 0.22, 0.19, 0.17` at
`t = 10, 40, 160` — both claims of A and B hold with room.

## GPT-6 Astra v1

Verbatim in `gpt_localised_cov_v1.md` (prompt `gpt_localised_cov_prompt_v1.md`). Summary: A and B correct for fixed parameters and
`t ≥ T ≥ 1`: `t·Var = tN₂/D − (tN₁)²/(tD²)` with `|tN₂ − 1/λ| ≤ K₂/t`, `|D − 1| ≤ K_D/t`, `D ≥ ½`, `|tN₁| ≤ B` gives
`|t·Var − 1/λ| ≤ (2K₂ + 2K_D/λ + 4B²)/t`; the `x²φ` expansion `x²e^y = x² + ax³ + (a²/2 − b)x⁴ + R'`, `R' = −abx⁵ + (b²/2)x⁶ +
x²(e^y − 1 − y − y²/2)` has the even bound after `|x|⁵ ≤ (x⁴ + x⁶)/2`; `|1/(λt) − 1/(tλ + g)| = g/(λt(tλ + g)) ≤ g/(λ²t²)`. Frame
off-diagonal covariances vanish *exactly* (product measure); `Cov_loc(wⱼ, wₖ) = ∑ᵢ QⱼᵢQₖᵢ Var_loc,i` by translation invariance and
bilinearity; `K_jk = ∑ᵢ|QⱼᵢQₖᵢ|Kᵢ`. Expose the `N₂` rate as its own theorem (done: `locSecond_rate`). C correct as an `O(1/t)`
energy statement with the *unlocalised* energy as observable; the cubic expansion needs the `−bx⁵` term
(`x³φ = x³ + ax⁴ − bx⁵ + x³(φ − 1 − y)`); qualification: C matches E3's trace expression only to `O(1/t)` (a displaced anchor
adds `(t/2)μᵀHμ`, `μ = gSw₀`, itself `O(1/t)`), so it is not an exact finite-`t` LLC identity and does not identify the first
correction coefficient. Vote: A + B core, C optional stretch ("an explicitly `O(t⁻¹)`-accurate localised-energy corollary").
Wording for A + B: "eq:cov with an entrywise `O(t⁻²)` remainder for the exact isotropically localised rotated separable anharmonic
Gibbs measure; equivalently a normwise `O(‖S‖²)` remainder for fixed model parameters" (`‖S‖ ≍ 1/t`); also `tΣ = H⁻¹ + O(1/t)`.
Not certified: nonseparable targets, `g = g(t)`, moving anchors, the `t⁻²` coefficient, entrywise comparison with `S²`'s entries,
sampling guarantees. Pitfalls: `t > 0` explicit; treat the `t`-dependent potential pointwise in `t`; keep the original energy and
the localised potential distinct in C; anchor `Qᵀ(w₀ − c)`; the discarded constant `e^{−g x₀²/2}` cancels but normalisers must be
nonzero; no `g > 0` needed.

## Vote
- Claude: A + B (C if it fits)
- GPT-6 Astra: A + B core; C optional as an `O(1/t)` energy corollary

## Result

Commit `0a1dc0d` on `tide/localised-cov`; `lake build` clean, `scripts/sorries` 0/0/0/0. A + B as voted; C (the localised LLC at
`O(1/t)`) left for its own tide.
`Laplace/Multi/LocalisedAnharmonicCov.lean` (     592 lines): `locQ₄`/`locQ₆`/`locQ₈`, `locSecond_pointwise`, `locPotential1`, `localisedVar`,
`gibbsExpectation_locPotential1`, `localisedVar_eq`, `locSecond_expansion2`, `locSecond_rate`, `localisedVar_rate`,
`localisedVar_sub_displayed_rate`, `sum_rate_div`, `localisedRotatedAnharmonic_cov_frame`, `localisedRotatedAnharmonic_cov_coord`,
`locS_rot_apply`, `conj_diagonal_inv_apply`, `localisedRotatedAnharmonic_cov_rate`, `localisedRotatedAnharmonic_cov_rate_leading`.

Surprises: `open scoped Nat` silently turns the observable name `φ` into the totient notation and breaks named arguments; the
ratio lemma needed the explicit `integral_const_mul` route because `simp only` with the pointwise identity also cancelled the
constant and left a shape the planned rewrite could not see. The mathematics was exactly tide 67's expansion applied to `x²φ`.
