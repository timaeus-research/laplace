# Tide 66 consult: eq:mean's localisation term in d dimensions on E2's exact localised measure

You are consulted, one round, on a Lean 4 / Mathlib formalisation step ("tide") in the `laplace` seabed. The seabed formalises the
Laplace/Hessian-route formulas of a note on SGLD sanity checks. Context available in the seabed (theorem names are real):

- 1D anharmonic potential `anharmonicPotential λ α γ x = λx²/2 + αx³/6 + γx⁴/24` with `λ, γ > 0`, `α² < 3λγ`; Gibbs measure
  `e^{−tℓ}`; sharp moment rates (`mean_anharmonic_O2_rate`: `|t⟨x⟩ + α/(2λ²)| ≤ K/t`, `evenMoment_anharmonic_rate`).
- Tide 65 (just landed, `Laplace/Multi/LocalisedAnharmonic.lean`): the 1D localised measure `e^{−tℓ(x) − (g/2)(x − x₀)²}`, `g ≥ 0`;
  `localisedMean λ α γ g x₀ t` := its mean; `localisedMean_anharmonic_rate : |t·localisedMean − (−α/(2λ²) + g x₀/λ)| ≤ K/√t` for
  `t ≥ T`; `locLeading λ α g x₀ t := −αt/(2(tλ+g)²) + g x₀/(tλ+g)` (the note's eq:mean with `S = (tλ + g)⁻¹`, `T = α`, `x* = 0`) and
  `localisedMean_sub_locLeading_rate : |localisedMean − locLeading| ≤ K/(t√t)`.
- Multi-d: `separablePotential ℓ u = ∑ᵢ ℓᵢ(uᵢ)`; `separableAnharmonic lam alpha gamma`; `affineFrame Q c w = Qᵀ(w − c)`;
  `rotated Q c L = L ∘ affineFrame Q c`; `rotatedAnharmonic Q c lam alpha gamma` (E2's oscillator in the note's frame, `Qᵀ Q = 1`);
  `gibbsExpectation_rotated_of_continuous : ⟨φ ∘ A⟩_{L∘A} = ⟨φ⟩_L`; `gibbsExpectation_coord_separable : ⟨φ(uᵢ₀)⟩_L = ⟨φ⟩_{ℓᵢ₀}`
  (spectator partition functions nonzero); `coord_eq_sum_affineFrame : wⱼ − cⱼ = ∑ᵢ Qⱼᵢ (Aw)ᵢ`; linearity lemmas for
  `gibbsExpectation` (`gibbsExpectation_finsetSum`, `gibbsExpectation_const_mul`, `gibbsExpectation_add_of_integrable`).
- The note's matrix functionals: `meanShift t H T = −½ (tH)⁻¹ (t T:(tH)⁻¹)` with `meanShift_rot : meanShift t (Q diag λ Qᵀ) (rotT Q α) =
  Q (−αᵢ/(2λᵢ²t))ᵢ`; `locS γ H s = (sH + γ1)⁻¹`, `meanShiftLoc s γ H T = −½ locS (s T:locS)`; `meanShift_rot_rate` (eq:mean at `K/t²`
  without localiser).
- The note's eq:mean: `⟨w⟩ − w* = −½ S (tT:S) + γ S (w₀ − w*) + O(S²)`, `S = (tH + γI)⁻¹`, for the localised posterior
  `e^{−tL(w) − (γ/2)|w − w₀|²}` (the note writes `γ` for the localiser strength; the seabed uses `g` to avoid the quartic's `γ`).

## Candidates (Claude, v1)

[same text as the tide log's "Candidates v1" and "Numerical check" sections, pasted below]

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

## Questions

1. Are A, B, C correct as stated? In particular: (i) is the frame invariance `|w − w₀|² = |Qᵀ(w − c) − Qᵀ(w₀ − c)|²` all that is
   needed for the localised measure to factorise in the eigenframe (isotropic localiser; `Qᵀ Q = 1` gives `Q Qᵀ = 1` in finite
   dimension)? (ii) Is `locS g H t = Q diag(1/(tλᵢ + g)) Qᵀ` and hence `meanShiftLoc t g H (rotT Q α) = Q(−αᵢ t/(2(tλᵢ + g)²))ᵢ`,
   `g locS (w₀ − c) = Q (g u₀ᵢ/(tλᵢ + g))ᵢ`, so that C's prediction is exactly `Q (locLeading λᵢ αᵢ g u₀ᵢ t)ᵢ`? (iii) Any hidden
   hypothesis (e.g. `t ≠ 0` in `g/(2t)`, `g ≥ 0` for integrability, `d ≥ 1`)?
2. Which is the strongest target reasonably reachable in one tide with this infrastructure — A only, A+B, or A+B+C? The plan is to
   prove A by transport + coordinate reduction + tide 65, B and C as corollaries via finite sums of coordinate rates and the two
   matrix identities. Is the `K/(t√t)` in B and C the right thing to state (B's `−½S(tT:S) + gS(w₀−w*)` at `S = (tH)⁻¹` vs C's
   displayed `S = (tH + gI)⁻¹` differ by `O(t⁻²)`, so both carry the same `t^{−3/2}` bound)?
3. How should the result be worded against the note (which of eq:mean's claims does it certify, which not — the `O(S²)` remainder is
   *not* proved, only `O(t^{−3/2})` with `S = O(1/t)`)? Any better candidate close to this seabed that I am missing (e.g. an
   anisotropic localiser `(g/2)(w − w₀)ᵀΓ(w − w₀)` commuting with `H`, or the localised *covariance* eq:cov with `S = (tH + gI)⁻¹`)?
4. Vote: which single candidate (or bundle) do you back for this tide?
