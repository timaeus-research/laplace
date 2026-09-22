# Tide: localised-mean-multi

**Direction (user):** auto mode ("Continue with what you think best"); chosen direction: E3/eq:mean in `d` dimensions — the localisation term `gS(w₀ − w*)` together with `−½S(tT:S)` at leading order for E2's rotated anharmonic oscillator with an isotropic Gaussian localiser, by separability of the localised measure in the eigenframe and transport through the affine frame; reduces to the 1D localised-mean rate (tide `localised-mean-1d`) coordinatewise.
**Seabed:** laplace, commit 7570538 (branch `tide/localised-mean-multi` off `tide/localised-mean-1d`, now `main`)
**Started:** 2026-09-22T13:29Z

## Candidates v1 (Claude)

Setting: `Q : Matrix (Fin d) (Fin d) ℝ` with `Qᵀ Q = 1`, centre `c`, anchor `w₀`, E2's `lam alpha gamma : Fin d → ℝ`
(`λᵢ, γᵢ > 0`, `αᵢ² < 3λᵢγᵢ`), localiser strength `g ≥ 0`. The *localised ambient potential*
`L_loc(w) = rotatedAnharmonic Q c lam alpha gamma w + g/(2t) ∑ⱼ (wⱼ − w₀ⱼ)²`, so that `e^{−t L_loc} = e^{−t L(Qᵀ(w−c)) − (g/2)|w − w₀|²}`
is the exact localised measure of E3 on E2's target; `⟨ψ⟩_loc := gibbsExpectation L_loc t ψ`. Let `u₀ = Qᵀ(w₀ − c)`,
`H = Q diag(λ) Qᵀ`, `T = rotT Q α`, `vᵢ = −αᵢ/(2λᵢ²) + g u₀ᵢ/λᵢ`.

- **A (frame coordinates).** For each `i`: `∃ K T, ∀ t ≥ T, |t ⟨(Qᵀ(w − c))ᵢ⟩_loc − vᵢ| ≤ K/√t`.
  Route: the isotropic localiser is frame-invariant, `|w − w₀|² = |Qᵀ(w − c) − u₀|²`, so `L_loc = rotated Q c L'` with
  `L'(u) = ∑ᵢ (ℓᵢ(uᵢ) + g/(2t)(uᵢ − u₀ᵢ)²)` separable; `gibbsExpectation_rotated_of_continuous` + `gibbsExpectation_coord_separable`
  reduce `⟨(Aw)ᵢ⟩_loc` to the 1D `localisedMean λᵢ αᵢ γᵢ g u₀ᵢ t`, then `localisedMean_anharmonic_rate`.
- **B (ambient, note's `S = (tH)⁻¹`).** For each `j`: `|(⟨w⟩_loc − c − meanShift t H T − g (tH)⁻¹(w₀ − c))ⱼ| ≤ K/(t√t)`.
  Route: `wⱼ − cⱼ = ∑ᵢ Qⱼᵢ (Aw)ᵢ` (`coord_eq_sum_affineFrame`), linearity, A, and the exact identity
  `Q v = t(meanShift t H T + g (tH)⁻¹(w₀ − c))` from `meanShift_rot` and `(tH)⁻¹ = Q diag(1/(tλ)) Qᵀ`.
- **C (ambient, the displayed `S = (tH + gI)⁻¹`).** For each `j`:
  `|(⟨w⟩_loc − c − meanShiftLoc t g H T − g • locS g H t *ᵥ (w₀ − c))ⱼ| ≤ K/(t√t)`.
  Route: `locS g H t = Q diag(1/(tλᵢ + g)) Qᵀ`, so the prediction is `Q (P_t,i)ᵢ` with `P_t,i = locLeading λᵢ αᵢ g u₀ᵢ t` the 1D
  displayed formula; then `localisedMean_sub_locLeading_rate` coordinatewise and the finite sum.

Rationale: closes the "localisation term only for Gaussian targets" caveat in the note's own dimension and notation (eq:mean's
full right-hand side on E2's exact localised measure), reusing tide 65 verbatim; no new analysis, only factorisation, transport and
matrix identities that the seabed already has in `GibbsRotation`, `SeparableExact`, `E2Matrix`, `CovKDerivativeLoc`.

## Numerical check

`numcheck_localised_mean_multi.py` (`d = 2`, rotation `θ = 0.6`, `λ = (1.3, 0.7)`, `α = (0.7, −0.4)`, `γ = (1.1, 0.9)`,
`c = (0.3, −0.2)`, `w₀ = (0.5, 0.9)`, `g = 0.8`, `dblquad`): `t(⟨w⟩_loc − c) → Qv = (−0.5151, 1.2429)` with `t·|error| = 2.38, 2.77,
2.87` at `t = 10, 40, 160` (so `O(1/t)`, better than the `1/√t` claimed); the identity `Qv/t = meanShift + g(tH)⁻¹(w₀ − c)` holds to
`1e-17`; against the displayed formula (C) `t²·|error| = 0.66, 0.86, 0.92` (so `O(t⁻²)`, better than the `t^{−3/2}` claimed).

## GPT-6 Astra v1

Verbatim in `gpt_localised_mean_multi_v1.md` (prompt `gpt_localised_mean_multi_prompt_v1.md`). Summary: A, B, C correct with
`Qᵀ Q = 1`, `λᵢ, γᵢ > 0`, `αᵢ² < 3λᵢγᵢ`, `g ≥ 0`, `t > 0`; the frame invariance of the isotropic localiser is the one new
ingredient, the rest is discharging the transport/separability premises (continuity, nonzero spectator partition functions,
integrability — the nonnegative localiser only lowers the Boltzmann factor). Expose the exact reductions as theorems:
`⟨(Qᵀ(w − c))ᵢ⟩_loc = localisedMean λᵢ αᵢ γᵢ g aᵢ t` and `⟨wⱼ⟩_loc − cⱼ = ∑ᵢ Qⱼᵢ localisedMean(…)`, `a = Qᵀ(w₀ − c)`. Matrix
identities confirmed: `tH + gI = Q diag(tλᵢ + g) Qᵀ`, `locS = Q diag(1/(tλᵢ+g)) Qᵀ`, `meanShiftLoc = Q(−αᵢt/(2(tλᵢ+g)²))`,
`g locS (w₀ − c) = Q(g aᵢ/(tλᵢ+g))`, sum exactly `Q (locLeading λᵢ αᵢ g aᵢ t)ᵢ`. `K/(t√t)` right for B and C; prove C directly
from `localisedMean_sub_locLeading_rate` (no need to compare B and C). Wording: "the exact localised Gibbs mean agrees with the
displayed eq:mean prediction with `S = (tH + gI)⁻¹` up to a coordinatewise `O(t^{−3/2})` error"; certifies the localisation term
for a non-Gaussian target, in ambient coordinates, with the note's actual `S`, on the exact localised measure; does *not*
certify the `O(S²)` remainder. Follow-up: anisotropic localiser `Γ = Q diag(ηᵢ) Qᵀ` (same-frame diagonality; commuting with `H`
alone is not enough under repeated eigenvalues); localised covariance needs new second-moment work.

## Vote
- Claude: A + B + C (C flagship, exact reductions exposed)
- GPT-6 Astra: A + B + C (C flagship; if scope shrinks, A + C)
