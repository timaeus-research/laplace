# Tide: localised-order2-multi

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); tides 72/73 follow-up: eq:mean's and eq:cov's `O(S²)` coefficients on E2's exact localised measure.
**Seabed:** laplace, commit b866486 (worktree `laplace-tide-localised-order2-multi`, branch
`tide/localised-order2-multi` off `tide/localised-llc-coeff` — a linear chain, since A uses tide 73's `locSecondMoment_loc_rate2`)
**Started:** 2026-09-22T16:01Z

## Candidates v1 (Claude)

Setting as in tides 65–73 (1D anharmonic oscillator `ℓ = (λ/2)x² + (α/6)x³ + (γ/24)x⁴`, `λ, γ > 0`, `α² < 3λγ`; isotropic localiser
`g ≥ 0`, anchor `x₀`, `a = g x₀`, `φ = e^{ax − (g/2)x²}`, `⟨·⟩_loc = ⟨·φ⟩/⟨φ⟩`; E2's rotated separable oscillator `w = c + Qu`,
frame anchor `u₀ = Qᵀ(w₀ − c)`, `S = (tH + gI)⁻¹`, `H = Q diag(λ) Qᵀ`).

Seabed state. Second-order localised results now available in 1D: the mean `|t⟨x⟩_loc − c − c'/t| ≤ K/t²`
(`localisedMean_order2_rate`, tide 72; `c = −α/(2λ²) + a/λ`, `c' = meanLocCoeff2 = B₁ + aα²/λ⁴ − aγ/(2λ³) + αg/λ³ − αa²/(2λ³) − ag/λ²`),
the second moment `|t⟨x²⟩_loc − 1/λ − c₂'/t| ≤ K/t²` (`locSecondMoment_loc_rate2`, tide 73; `c₂' = locSecondCoeff2 = n₂ − d₁/λ`,
`n₂ = B₂ + ac₃ + 3p₃/λ²`), `⟨x²⟩_loc = Var_loc + ⟨x⟩_loc²` (`locSecondMoment_eq`), `Var_loc` as a ratio (`localisedVar_eq`). The E2
transports: `⟨wⱼ⟩_loc = cⱼ + ∑ᵢ Qⱼᵢ ⟨uᵢ⟩_loc,i` (`localisedRotatedAnharmonic_ambient_coord`), the displayed right-hand side of eq:mean in
frame form `meanShiftLoc + gS(w₀ − c) = Q (P_t,i)ᵢ` with `P_t = locLeading = −αt/(2(tλ + g)²) + a/(tλ + g)` (`displayed_mean_rot`),
`Cov_loc[wⱼ, wₖ] = ∑ᵢ QⱼᵢQₖᵢ Var_loc,i` (`localisedRotatedAnharmonic_cov_coord`), `Sⱼₖ = ∑ᵢ QⱼᵢQₖᵢ/(tλᵢ + g)` (`locS_rot_apply`), and the
finite-sum transport lemmas `sum_rate_div`, `sum_rate_div_sq`. Tides 67 (§72) and 68 (§73) certified eq:mean's and eq:cov's `O(S²)`
remainders on E2's exact localised measure (`K/t²` per entry) without their coefficients; tide 72 (§77) gave the mean's second-order
coefficient in 1D only. The unlocalised variance's second-order coefficient is `α²/λ⁴ − γ/(2λ³)` (`var_anharmonic_order2_rate`), the
mean's is `B₁ = meanCoeff2`.

### A. The localised variance to second order (1D)

`|t·Var_loc − 1/λ − v'/t| ≤ K/t²` with `v' = c₂' − c² = α²/λ⁴ − aα/λ³ − g/λ² − γ/(2λ³)`, from `t Var_loc = t⟨x²⟩_loc − (t⟨x⟩_loc)²/t`
and the two second-order inputs (`(c + c'/t + O(t⁻²))² = c² + O(1/t)`). Against the displayed `S = 1/(tλ + g)`:
`|Var_loc − 1/(tλ + g) − (v' + g/λ²)/t²| ≤ K/t³` since `1/(λt) − 1/(tλ + g) = g/(λ²t²) − g²/(λ²t²(tλ + g))`, and
**`v' + g/λ² = (α²/λ⁴ − γ/(2λ³)) − aα/λ³`**: eq:cov's `O(S²)` term under localisation is the unlocalised second-order variance
coefficient minus `aα/λ³`.

### B. eq:mean's `O(S²)` coefficient on E2

1D: `|⟨x⟩_loc − P_t − r/t²| ≤ K/t³` with `r = c' − c'_S`, `c'_S = αg/λ³ − ag/λ²` the `t⁻²` coefficient of `P_t`
(`P_t = c/t + c'_S/t² + O(t⁻³)`, algebra as in `locLeading_sub_le`), so
**`r = B₁ + aα²/λ⁴ − aγ/(2λ³) − αa²/(2λ³)`**. E2: `|(⟨w⟩_loc − c − meanShiftLoc − gS(w₀ − c))ⱼ − (∑ᵢ Qⱼᵢ rᵢ)/t²| ≤ K/t³` by
`ambient_coord`, `displayed_mean_rot` and a `sum_rate_div_cube` (copy of `sum_rate_div_sq`). This identifies the `O(S²)` of eq:mean
whose existence §72 certified.

### C. eq:cov's `O(S²)` coefficient on E2

`|Cov_loc[wⱼ, wₖ] − Sⱼₖ − (∑ᵢ QⱼᵢQₖᵢ (v'ᵢ + g/λᵢ²))/t²| ≤ K/t³` by `cov_coord`, `locS_rot_apply`, A and `sum_rate_div_cube`.

### D. Corollary: the anchor at the minimiser

With `w₀ = c` (so `u₀ = 0`, every `aᵢ = 0`): `rᵢ = B₁,ᵢ` and `v'ᵢ + g/λᵢ² = αᵢ²/λᵢ⁴ − γᵢ/(2λᵢ³)` — the `O(S²)` coefficients of eq:mean and
eq:cov on the localised measure are the *unlocalised* second-order coefficients, independent of `g`: **the displayed formulas with
`S = (tH + γI)⁻¹` absorb the localiser exactly through second order** (pure algebra on A–C's coefficients; `affineFrame Q c c = 0`).
For `a ≠ 0` the `g`-dependence enters only through `a = g u₀`: `−aα/λ³` in the variance, `aα²/λ⁴ − aγ/(2λ³) − αa²/(2λ³)` in the mean.

Proposed bundle: A + B + C + D. Line estimate ~500–600 (no new expansions; ratio and transport bookkeeping).

Numerical check (`numcheck_localised_order2_multi.py`, sympy Wick expansion with the localiser inside the perturbation, `ε = 1/√t`; quadrature at
`λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`): `t Var_loc = 1/λ + 0·ε + v'ε² + …` with `v'` exactly `c₂' − c²`;
`P_t`'s `t⁻²` coefficient is exactly `c'_S`; quadrature `t(t Var_loc − 1/λ) = −0.6424, −0.6888, −0.7010, −0.7041, −0.7048` vs
`v' = −0.70509`, `t²(Var_loc − S) → −0.23157` vs `v' + g/λ² = −0.23171`, `t²(⟨x⟩_loc − P_t) → 0.04738` vs `r = 0.047476`
(`t = 10, …, 2560`).

## Numerical check

`numcheck_localised_order2_multi.py`: see the last paragraph of the candidates — `v'`, `c'_S` reproduced exactly; quadrature
`t(t Var_loc − 1/λ) → −0.7048` vs `v' = −0.70509`, `t²(Var_loc − S) → −0.23157` vs `−0.23171`, `t²(⟨x⟩_loc − P_t) → 0.04738` vs
`r = 0.047476`.

## GPT-6 Astra v1

Verbatim in `gpt_localised_order2_multi_v1.md` (prompt: `gpt_localised_order2_multi_prompt_v1.md`). Summary: A, B, C correct as stated
(remainder constants enlarge: `|m − c| ≤ M/t`, `|m² − c²| ≤ M(2|c| + M)/t` with `M = |c'| + K_m`; the rational identity
`1/(tλ + g) − 1/(λt) + g/(λ²t²) = g²/(λ²t²(tλ + g)) ≤ g²/(λ³t³)`; a Lean-friendly bound `|P_t − c/t − c'_S/t²| ≤ (g²/t³)(3|α|/(2λ⁴) + |a|/λ³)`);
`v'`, `v' + g/λ²`, `c'_S`, `r` re-derived independently and agree. D's coefficient identities are correct; **reword**: not "the
displayed formulas are exact through second order" (they are not — `B₁` and `V₂ = α²/λ⁴ − γ/(2λ³)` remain) but "at the minimiser
anchor, using `S = (tH + gI)⁻¹` absorbs all localiser-dependent contributions through order `t⁻²`; the remaining second-order
coefficients are the unlocalised ones". Structural reason: at `x₀ = 0` the localised density is exactly the anharmonic density with
`λ → λ_t = λ + g/t`, whose displayed leading terms are `−α/(2tλ_t²)`, `1/(tλ_t)`, and `B₁(λ_t)/t²`, `V₂(λ_t)/t²` differ from the values
at `λ` only at `t⁻³`; the `g`-dependence returns at third order via `gB₁'(λ) = g(25α³/(8λ⁶) − 8αγ/(3λ⁵))` and
`gV₂'(λ) = g(−4α²/λ⁵ + 3γ/(2λ⁴))` (not certified here). Wording safeguards: keep `g` (localiser) distinct from the quartic `γ`;
attribute to the separable oscillator, not the note's general big-O; an `O(S²)` assertion does not name a coefficient — the theorems
identify the `t⁻²` coefficients of the residuals under `S ≍ 1/t`. Order: A → B scalar → `t⁻³` transport → B, C rotated → D. The rotated
eq:covK second order is a worthwhile next tide but adds a mixed-moment bookkeeping layer. Optional cheap corollary: entrywise limits.

## Vote
- Claude: A + B + C + D (D's docstrings reworded as GPT suggests)
- GPT-6 Astra: A + B + C + D, "with enlarged remainder constants explicit and D phrased as absorption of all localiser-dependent terms
  through `t⁻²`, not exact second-order accuracy"

## Result

Commit `0a8ee05` on `tide/localised-order2-multi`; `lake build` clean, `scripts/sorries` 0/0/0/0. A + B + C + D as voted, with D's docstrings in
GPT's wording.
`Laplace/Multi/LocalisedOrder2Multi.lean` (     430 lines): `varLocCoeff2`(+`_eq`), `covLocCoeff2`(+`_eq`, `_anchor_zero`), `locLeadingCoeff2`, `meanLocResidual2`(+`_eq`,
`_anchor_zero`), `locLeading_order2_sub_le`, `displayed_var_remainder`, `var_assembly`, `localisedVar_order2_rate` (A),
`localisedVar_sub_displayed_order2_rate`, `localisedMean_sub_locLeading_order2_rate` (B, 1D), `sum_rate_div_cube`,
`localisedRotatedAnharmonic_displayed_order2_rate` (B), `localisedRotatedAnharmonic_cov_order2_rate` (C), `affineFrame_self`,
`localisedRotatedAnharmonic_displayed_order2_rate_anchor`, `localisedRotatedAnharmonic_cov_order2_rate_anchor` (D).

Surprises: none mathematical — every input existed (tides 72, 73 and the E2 transports of tides 66–68), and the whole tide is ratio
and finite-sum bookkeeping. GPT's structural reading of D (the localiser at the minimiser is the substitution `λ ↦ λ + g/t`, whose
effect on second-order coefficients is `O(t⁻³)`) went into the module docstring; its predicted third-order `g`-dependence
(`gB₁'(λ)`, `gV₂'(λ)`) is a follow-up, not certified.
