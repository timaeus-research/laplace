# Tide 68 consult: eq:cov with the localiser on the exact localised anharmonic measure (and E3's localised LLC)

One-round consult on a Lean 4 / Mathlib formalisation step in the `laplace` seabed. Available (real theorem names):

- 1D anharmonic Gibbs measure `e^{−tℓ}`, `ℓ = λx²/2 + αx³/6 + γx⁴/24`; rates `mean_anharmonic_O2_rate`, `evenMoment_anharmonic_rate k`,
  `oddMoment_anharmonic_rate k`; tide 65: localised weight `φ`, `|⟨φ⟩ − 1| ≤ K/t` (`locDenominator_rate`), `⟨x⟩_loc = ⟨xφ⟩/⟨φ⟩`;
  tide 66: `d`-dim frame invariance/separability of the isotropic localiser, `localisedRotatedAnharmonic`, exact reductions,
  `locS_rot : (tH + gI)⁻¹ = Q diag(1/(tλᵢ + g)) Qᵀ`, `sum_rate_div_sqrt`; tide 67: `|e^y − 1 − y − y²/2| ≤ (e^M + 3)|y|³`
  (`abs_exp_sub_taylor2_le`, `locWeight_taylor2`), `|y|³ ≤ 4(|gx₀|³|x|³ + (g/2)³x⁶)`, `thirdMoment_bound : |t⟨x³⟩| ≤ M/t`,
  `|t⟨xφ⟩ − c| ≤ K/t`, `|t⟨x⟩_loc − c| ≤ K/t`, `sum_rate_div_sq`.
- Covariance API: `gibbsCov L t φ ψ = ⟨φψ⟩ − ⟨φ⟩⟨ψ⟩` (1D and multi), `gibbsCov_coord_separable : Cov[uᵢ, uⱼ] = if i = j then Var_{ℓᵢ}
  else 0`, `gibbsCov_rotated_of_continuous : Cov_{L∘A}[φ∘A, ψ∘A] = Cov_L[φ, ψ]`, `gibbsCov_linear_combination`, `gibbsCov_const_add_both`,
  `gibbsCov_coord_rotatedAnharmonic : Cov[wⱼ, wₖ] = ∑ᵢ QⱼᵢQₖᵢ Var_{ℓᵢ}` (unlocalised).
- The note: E3 localises with `(γ/2)|w − w₀|²`; eq:cov `Σ = S + O(S²)`, `S = (tH + γI)⁻¹`; E3's localised LLC
  `λ̂_loc = ½ tr(tH(tH + γI)⁻¹) = ½∑ᵢ tλᵢ/(tλᵢ + γ)` (Gaussian derivation).

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

## Questions

1. Are A, B, C correct as stated? In particular: (i) in A, is `t·Var = tN₂/D − (tN₁)²/(tD²)` with `|tN₁| ≤ |c| + K`, `D ≥ ½` enough for
   the `K/t` rate, and is the expansion of `x²φ` (remainder `A'x⁴ + B'x⁶ + C'x⁸`) right? (ii) in B, do the frame covariances vanish
   exactly for the localised separable potential (product measure), so that `Cov_loc[wⱼ, wₖ] = ∑ᵢ QⱼᵢQₖᵢ Var_loc,i` is exact? (iii) in
   C, is `t⟨L∘A⟩_loc = ½∑ᵢ tλᵢ/(tλᵢ + g) + O(1/t)` the right leading statement (the `O(1/t)` absorbs `(αt/6)⟨x³⟩_loc`,
   `(γt/24)⟨x⁴⟩_loc` and `(λt/2)·mean²`), and is it the note's E3 localised LLC?
2. Which bundle is reachable in one tide: A + B, or A + B + C? C adds the `x³φ` expansion and the energy bookkeeping over coordinates
   (the seabed has `gibbsExpectation_energy_separableAnharmonic` for the unlocalised case).
3. Wording against the note: which claims of E3 / eq:cov does A + B certify (with `S = (tH + gI)⁻¹`, `O(S²) = O(t⁻²)`), which not?
4. Any pitfalls (e.g. the `t`-dependent potential in `gibbsCov`, or the need for `g > 0` anywhere)? Vote.
