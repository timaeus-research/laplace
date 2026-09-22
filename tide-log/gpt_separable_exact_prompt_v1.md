# Tide `separable-exact` (seabed: laplace, off main) — candidates v1

Context. E2 of the Sanity-on-Sampling note: "Separable anharmonic oscillators in d = 10 with κ = 10 and anharmonicity a = 0.5 and 1 …
exact quadrature is available to measure [the Laplace formulas'] remainder. All four Laplace predictions converge to the exact values with
relative error proportional to 1/t: for the covariance at a = 0.5, 2.7×10⁻² at t = 10 and 2.5×10⁻⁴ at t = 1000." The note's potential is
`L(w) = ∑ᵢ ℓᵢ(wᵢ)`, `ℓᵢ(x) = λᵢx²/2 + αᵢx³/6 + gᵢx⁴/24` with `αᵢ² = a²λᵢ³`, `gᵢ = λᵢ²` (so `a² < 3` is the discriminant condition). Tide
`separable-oneloop` (section 37) proved the *one-loop formula* for this potential is diagonal with relative correction `(a² − 1/2)/t`; nothing
yet says the *exact* Gibbs moments of the d-dimensional separable potential behave this way.

Seabed (Lean 4 / Mathlib, all proved). Multi-dimensional Gibbs: `Laplace.Multi.partitionFunction L t = ∫ w : ι → ℝ, exp(−t L w)`,
`gibbsExpectation L t φ = (∫ φ w exp(−tLw)) / Z`, `gibbsCov L t φ ψ = ⟨φψ⟩ − ⟨φ⟩⟨ψ⟩` (Lebesgue on `ι → ℝ`, `ι` a Fintype). One-dimensional
analogues `Laplace.partitionFunction/gibbsExpectation/gibbsCov` on `ℝ`. `SeparableRecovery.lean` factorises the *monomial* separable
potential `∑ aᵢ wᵢ^{2kᵢ}/(2kᵢ)!` via `integral_fintype_prod_volume_eq_prod` (`∫ ∏ᵢ fᵢ(wᵢ) = ∏ᵢ ∫ fᵢ`, no integrability hypothesis) and
`Finset.prod_ite_eq'`/`Finset.mul_prod_erase`: `partitionFunction_separableMonomial`, `coordSq_integral_separableMonomial`,
`gibbsExpectation_coordSq_separableMonomial` (spectator factors cancel given `0 < Zᵢ`). One-dimensional anharmonic asymptotics for
`anharmonicPotential λ α γ` under `0 < λ, 0 < γ, α² < 3λγ`: `mean_anharmonic_asymptotic : t⟨x⟩ → −α/(2λ²)`,
`cov_self_anharmonic_asymptotic : t Var → 1/λ`, `var_anharmonic_second_order : t²(Var − 1/(λt)) → α²/λ⁴ − γ/(2λ³)`,
`secondMoment_anharmonic_asymptotic`; integrability `integrable_exp_neg_t_anharmonic`, `integrable_x_mul_exp_neg_t_anharmonic`,
`integrable_abs_pow_mul_exp_neg_t_anharmonic`.

Candidates.

A. **Generic separable factorisation** (`separablePotential ℓ w := ∑ᵢ ℓᵢ(wᵢ)`; `exp_separable`, `partitionFunction_separable : Z = ∏ᵢ Zᵢ`,
   `coord_integral_separable : ∫ φ(wᵢ₀) e^{−tL} = (∫ φ e^{−tℓᵢ₀}) ∏_{i≠i₀} Zᵢ`, `gibbsExpectation_coord_separable : ⟨φ(wᵢ₀)⟩_L = ⟨φ⟩_{ℓᵢ₀}`
   given `∀ i, 0 < Zᵢ`; `pair_integral_separable` for `wᵢwⱼ`, `i ≠ j`, and `gibbsCov_coord_separable : Cov_L[wᵢ, wⱼ] = if i = j then Var_{ℓᵢ}[x]
   else 0`). No integrability needed for the identities (Bochner integrals are total and the product lemma has no hypotheses); `0 < Zᵢ` for the
   cancellation.

B. **The exact covariance of the separable anharmonic oscillator** (`gibbsCov_separableAnharmonic`): with `ℓᵢ = anharmonicPotential λᵢ αᵢ γᵢ`,
   `0 < λᵢ, 0 < γᵢ, αᵢ² < 3λᵢγᵢ`, `t > 0`: `Cov_L[wᵢ, wⱼ] = δᵢⱼ Var_{ℓᵢ}[x]`, and the asymptotics per coordinate
   `t²(Var_L[wᵢ] − 1/(λᵢt)) → αᵢ²/λᵢ⁴ − γᵢ/(2λᵢ³)` (`separable_var_second_order`), the relative form
   `t (λᵢ t Var_L[wᵢ] − 1) → αᵢ²/λᵢ³ − γᵢ/(2λᵢ²)` (`separable_var_relative_rate`), and in the note's parametrisation `→ a² − 1/2`
   (`separable_var_relative_rate_note`): the exact remainder is `∝ 1/t` with the one-loop constant of section 37. Also the mean
   `t⟨wᵢ⟩_L → −αᵢ/(2λᵢ²)` (`separable_mean_asymptotic`). Positivity of `Zᵢ` for the anharmonic potential is needed (is there a lemma? if not,
   `integral_pos_iff_support_of_nonneg` with continuity/`exp_pos`).

C. **The LLC** `t⟨L⟩_L → d/2`: `⟨L⟩_L = ∑ᵢ ⟨ℓᵢ⟩_{ℓᵢ}` (linearity needs integrability of `ℓᵢ e^{−tℓᵢ}`) and a one-dimensional `t⟨ℓ⟩ → 1/2`,
   which we have not located in the seabed (there are cumulant/log-partition files: `−∂_t log Z = ⟨ℓ⟩` and `Z ~ c t^{−1/2}` would give it).
   E2's "at t = 3 the exact LLC is 4.76, not 5" is the finite-t deviation of this limit.

Numerical check done (`numcheck43.py`): for `a = 0.5`, `λ ∈ {1, 3, 10}`, exact quadrature gives `t(λtVar − 1) = −0.2655, −0.2526, −0.2503`
at `t = 10, 100, 1000` (limit `a² − 1/2 = −0.25`), `t⟨x⟩ → −α/(2λ²)` to 3 digits, `t⟨ℓ⟩ = 0.49993` at `t = 1000`; a 2-D check confirms
`Z = Z₁Z₂` and cross-covariance `≈ 1e-14`.

Questions. (1) Are A and B correct as stated — in particular is `gibbsCov_coord_separable` right with the `0 < Zᵢ` hypothesis only, and does the
relative-rate statement follow from `var_anharmonic_second_order` by `t(λtV − 1) = λ · t²(V − 1/(λt))` (so the limit is `λ(α²/λ⁴ − γ/(2λ³))`)?
(2) For C, is there a standard route to `t⟨ℓ⟩_t → 1/2` from what is listed (e.g. via `⟨ℓ⟩ = −∂_t log Z` and the second-order partition-function
asymptotics), or should C be dropped from this tide? (3) Anything close to this seabed we are missing — e.g. should A be stated for
`gibbsExpectation` of a general product observable `∏ᵢ φᵢ(wᵢ)` (`⟨∏φᵢ⟩ = ∏⟨φᵢ⟩`), from which both the coordinate and pair statements follow?
Please end with a vote on the subset A–C.
