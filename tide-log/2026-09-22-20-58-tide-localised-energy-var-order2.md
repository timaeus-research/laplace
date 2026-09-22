# Tide: localised-energy-var-order2

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); GPT's next substantial target after tides 85–86: the second-order localised energy variance and the correctly
normalised derivative discrepancy from the Gaussian trace prediction — now reachable through the Stein–covariance reduction with tide
86's signed seventh and eighth-moment bounds.
**Seabed:** laplace, commit 5a819b8 (worktree `laplace-tide-localised-energy-var-order2`, branch
`tide/localised-energy-var-order2` off `main`)
**Started:** 2026-09-22T21:00Z

## Candidates v1 (Claude)

Setting (E2, as in tides 68–86): the exact localised measure per frame coordinate (`ℓ = λx²/2 + αx³/6 + γx⁴/24`, anchor `a = g u₀`);
`e₁ = energyLocCoeff1 = (a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)` (tide 73), `c₂' = locSecondCoeff2` (`t m₂ = 1/λ + c₂'/t + …`),
`c₃ = locThirdCoeff`, `c₅ = locFifthCoeff`. Landed: the localised Stein–covariance reduction (tide 77)
`t²Cov[ℓ, xⁿ] = (n/2) t mₙ − (α/12) t²Cov[x³, xⁿ] − (γ/24) t²Cov[x⁴, xⁿ] − (g/2) t Cov[x², xⁿ] + (a/2) t Cov[x, xⁿ]`;
`t²Cov[ℓ, x²] = 1/λ + 2c₂'/t + O(t⁻²)` (tide 78); the moment rates `t m₁, t m₂` (second order), `t²m₃, t²m₄, t³m₅, t³m₆` (leading, `O(1/t)`
remainders), and tide 86's `|t⁴m₇| ≤ K`, `|t⁴m₈| ≤ K`; tide 85's exact `−∂ₜ⟨L∘A⟩_loc = Var_loc(L∘A) = ∑ᵢ Var_loc,ᵢ(ℓᵢ)`.

**A. The second-order localised energy variance (1D).** `Var_loc(ℓ) = Cov[ℓ, ℓ] = (λ/2)Cov[ℓ,x²] + (α/6)Cov[ℓ,x³] + (γ/24)Cov[ℓ,x⁴]`
(bilinearity), and by the reduction with `n = 3, 4` and the landed rates:
`t²Cov[ℓ, x³] = C₃'/t + O(t⁻²)`, `C₃' = (3/2)c₃ − 5α/(4λ³) + 3a/(2λ²) = −5α/λ³ + 6a/λ²` (the terms `t²Cov[x⁴,x³]`, `t Cov[x²,x³]` are
`O(t⁻²)` because `t⁴m₇`, `t³m₅` are bounded); `t²Cov[ℓ, x⁴] = 6/(λ² t) + O(t⁻²)` (all other terms `O(t⁻²)`, using `|t⁴m₈| ≤ K`). Hence
**`|t² Var_loc(ℓ) − ½ − 2e₁/t| ≤ K/t²`**: the `1/t` coefficient is exactly `2e₁` (`λc₂' + (α/6)C₃' + γ/(4λ²) = 2e₁`, checked
symbolically), i.e. the variance's second-order term is the derivative reading of the energy's first correction.

**B. On E2.** `|t² Var_loc(L∘A) − d/2 − 2(∑ᵢ e₁ᵢ)/t| ≤ K/t²`, equivalently **`−∂ₜ⟨L∘A⟩_loc = d/(2t²) + 2(∑ᵢe₁ᵢ)/t³ + O(t⁻⁴)`** — the
coefficientwise derivative of tide 73's `t⟨L∘A⟩_loc = d/2 + ∑e₁/t + O(t⁻²)`, established from moments (a consistency check with the
formal derivative, not obtained from it).

**C. The correctly normalised derivative discrepancy from the Gaussian trace prediction** (GPT's tide-85 target). With
`P(t) = ½ tr(H S(t)) = ½∑ᵢ λᵢ/(tλᵢ + g)`, exactly `P'(t) = −½∑ᵢ λᵢ²/(tλᵢ + g)²`, and per coordinate
`|½λ²t³/(tλ + g)² − t/2 + g/λ| = g²(3λt + 2g)/(2λ(tλ + g)²) ≤ g²(3λ + 2g)/(2λ³t)`; hence
**`|t³ (Var_loc(L∘A) + P'(t)) − 2C₁| ≤ K/t`**, `C₁ = ∑ᵢ (e₁ᵢ + g/(2λᵢ))` — twice tide 85's invariant trace-discrepancy coefficient, recovered
from genuine fluctuation estimates. (`−∂ₜ(⟨L⟩_loc − P) = 2C₁/t³ + O(t⁻⁴)`, the derivative reading of `t(⟨L⟩ − P) = C₁/t + O(t⁻²)`.)

Sizing: A ~350 lines (bilinearity of the 1D covariance in the second slot with the polynomial probe, the two reductions with ~10 moment
products each to `O(t⁻²)`, assembly, the coefficient identity), B ~60, C ~120 (`HasDerivAt` of the trace prediction through
`hasDerivAt_locS_entry`/`trace_mul_conj_diagonal`, the rational coordinate bound, assembly). Target A + B + C.

## Numerical check

`numcheck_localised_energy_var_order2.py` (two frame coordinates, anchor off the minimum): `t(t²Var_loc(ℓ) − ½) = −0.7176, −1.0935` at
`t = 1280` against `2e₁ = −0.7185, −1.0955`; `t³Cov[ℓ, x³] → C₃' = −0.0310, 0.6694` (`−0.0286, 0.6612` at `t = 1280`); `t³Cov[ℓ, x⁴] → 6/λ² =
3.5503, 7.4074` (`3.5426, 7.3836`); E2: `t³(Var_loc(L) + P'(t)) = −0.2863, −0.2979, −0.3038, −0.3067 → 2C₁ = −0.3097`; the coefficient
identity `λc₂' + (α/6)C₃' + γ/(4λ²) = 2e₁` is exact in sympy.

## GPT-6 Astra v1

Verbatim in `gpt_localised_energy_var_order2_v1.md` (prompt: `gpt_localised_energy_var_order2_prompt_v1.md`). Summary: **A, B, C correct;
"the earlier requirement for second-order fifth/sixth moments was unnecessary."** Full bookkeeping table confirmed: at `n = 3` the `1/t`
contributions are `3c₃/(2t)` (from `(n/2)t mₙ`), `15/(λ³t)` (from `t²Q₃₃`) and `3/(λ²t)` (from `tQ₁₃`); at `n = 4` only `6/(λ²t)`; every product
subtraction is `O(t⁻²)` (`t²m₃²`, `tm₁m₃`, `t²m₇`, `t²m₈`, `t²m₃m₄`, `t²m₄²`); hence `C₃' = −5α/λ³ + 6a/λ²`. B follows from the *exact*
variance decomposition. C's identity `R_λ(t) = g²(3λt + 2g)/(2λ(tλ+g)²)`, `0 ≤ R_λ ≤ g²(3λ+2g)/(2λ³t)` right (uses `g ≥ 0`, `t ≥ 1`), and
`t³(Var + P') = ∑(2e₁ᵢ + g/λᵢ) + O(1/t) = 2C₁ + O(1/t)`. The coefficient identity is exactly the coefficientwise derivative relation
(`c₂' = (a² − g)/λ² − 2aα/λ³ − γ/(2λ³) + 5α²/(4λ⁴)`). Wording: B "second-order localised susceptibility expansion:
`−∂ₜ⟨L∘A⟩_loc = d/(2t²) + 2∑e₁ᵢ/t³ + O(t⁻⁴)`; its correction coefficient agrees with coefficientwise differentiation of the localised energy
expansion"; C "the exact localised response differs from the Gaussian-trace response by `−∂ₜ(⟨L∘A⟩_loc − P) = 2C₁/t³ + O(t⁻⁴)`" — proved
from moments, and localised/E2-specific. Lean route: work with scaled moments `Mⱼ`, separate exact scaled identities (`field_simp`/`ring`)
from estimates, only `M₃, M₄, M₆` need leading rates (others bounds), bilinearity needs energy×probe integrability to degree eight,
differentiate the scalar finite sum for `P`, combine thresholds by finiteness. Line estimates "plausible but optimistic". **Next**:
sampler-side transfer of the localised response estimate, if hypotheses allow; in the moment hierarchy `t³κ₃ = 1 + 6e₁/t` (needs
second-order `m₆`, leading rates of `t⁴m₇`, `t⁴m₈`, and remainders through degree twelve).

## Vote
- Claude: A + B + C
- GPT-6 Astra: "**Vote: A+B+C**, with A+B the mandatory core and C the first stretch … Commitment order: the two covariance-rate
  lemmas → A → B → C."

## Result

Commit `db791e7` on `tide/localised-energy-var-order2`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/LocalisedEnergyVarOrder2.lean` (     709 lines).
A + B + C as voted.
Rates: `bound_of_rate`, `bound_of_rate2`, `prod_div_sq_bound`, `scale_down_sq`, `scale_down_one`, `rate_shift_one`, `rate_shift_two`.
1D: `integrable_energy_pow_locPotential1`, `locEnergyVar_split` (bilinearity), `locCovK_cubic_order2`, `locCovK_quartic_order2`,
`varOrder2_coeff_identity` (`λc₂' + (α/6)C₃' + γ/(4λ²) = 2e₁`), `locEnergyVar_order2`.
E2: `tracePrediction_eq`, `hasDerivAt_tracePrediction`, `tracePrediction_coord_rate`, `localisedVar_energy_order2`,
`localisedEnergy_neg_deriv_order2`, `localisedVar_energy_add_tracePrediction_deriv`.

Surprises: GPT's earlier "needs second-order fifth/sixth moments" was unnecessary — the Stein–covariance reduction turns the
second-order variance into leading rates plus the bounded signed seventh/eighth moments; the identity `λc₂' + (α/6)C₃' + γ/(4λ²) = 2e₁`
closes by `field_simp; ring` after unfolding five coefficient definitions.
