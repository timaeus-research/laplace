# Tide: the localised Gibbs law as a tilted Gaussian (E3)

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." (auto run on the Sanity on Sampling mathematics; this tide formalises E3: the localisation term belongs in the effective Hessian, and a mis-centred anchor biases the LLC by `½ t μᵀHμ`.)
**Seabed:** laplace, `main` at 58cc9e9; worktree `laplace-tide-localised-bias`, branch `tide/localised-bias`
**Started:** 2026-09-21 (UTC, see file name)

## Context

The note's sampler targets `π(w) ∝ exp(−tL(w) − (γ/2)|w − w₀|²)`; for the quadratic model `L = ½ wᵀHw` (minimiser `w* = 0`) this is
`exp(−½ wᵀPw + wᵀv)` with `P = tH + γI` (the note's effective precision) and `v = γw₀`. Completing the square, it is the Gaussian
`N(m, P⁻¹)` with `m = P⁻¹v = γP⁻¹w₀` (the note's `eq:mean` at leading order and the E3 caption's `μ = γP⁻¹(w₀ − w*)`). E3's findings:
(i) the sampled covariance matches `(tH + γI)⁻¹`, not `(tH)⁻¹`; (ii) the LLC follows `eq:llc` with `P`; (iii) displacing `w₀` adds
`½ t μᵀHμ` to the LLC. The seabed has, for `P.PosDef` on `ι → ℝ` (tides `gaussian-moments-posdef`, `gaussian-moments-high`): `gaussianZ`,
second moments `Z (P⁻¹)ᵢⱼ`, `gaussian_quadForm_integral_posDef`, and the first moments vanish (`gaussian_stein_prod_coord_matCLM` at `n = 0`).

## Candidates v1 (Claude)

**A. The tilted Gaussian on `ι → ℝ` and E3.** For `P.PosDef`, `v : ι → ℝ`, `m := P⁻¹ *ᵥ v`, `tiltedWeight P v u := exp(−½ uᵀPu + v ⬝ᵥ u)`:

1. `tiltedWeight_eq`: `tiltedWeight P v u = exp(½ m ⬝ᵥ P *ᵥ m) * gaussianWeight (matCLM P) (u − m)` (complete the square; `P` symmetric, `P m = v`).
2. `integral_tilted`: `∫ f u * tiltedWeight P v u = exp(½ mᵀPm) * ∫ f (u + m) * gW u` (translation invariance of Lebesgue measure, `integral_add_right_eq_self`), hence `tiltedZ P v = exp(½ mᵀPm) * gaussianZ (matCLM P)` and integrability transfers.
3. Moments of `tiltedExpectation P v φ := (∫ φ u * tiltedWeight P v u) / tiltedZ P v`: `⟨uᵢ⟩ = mᵢ`, `⟨uᵢuⱼ⟩ = (P⁻¹)ᵢⱼ + mᵢmⱼ`, covariance `(P⁻¹)ᵢⱼ`, and `⟨quadForm (matCLM H) u⟩ = ∑ᵢⱼ Hᵢⱼ(P⁻¹)ᵢⱼ + m ⬝ᵥ H *ᵥ m` (the cross term vanishes by the first-moment identity).
4. **E3**: with `P = t•H + γ•1` (`H.PosDef`, `t > 0`, `γ ≥ 0`), `v = γ•w₀`, `m = γ P⁻¹ w₀`: the localised covariance is `(tH + γI)⁻¹` and the LLC estimate is
   `t ⟨½ wᵀHw⟩ = ½ ∑ᵢⱼ (tH)ᵢⱼ ((tH+γ)⁻¹)ᵢⱼ + ½ t m ⬝ᵥ H *ᵥ m` (`localisedLLC_eq`); at `w₀ = 0` the bias term is `0` and at `γ = 0` the first term is `d/2` (`gaussian_llc_posDef`). Optional: the eigenvalue form `½ ∑ᵢ tλᵢ/(tλᵢ + γ)` via `orthoOf`.

Rationale: the direct formalisation of E3's three findings for the quadratic model, on the seabed's own `ι → ℝ` Gaussian machinery; one new idea (the shift). Closed forms as stated (numerical check below).

**B. The same through Mathlib's `multivariateGaussian m S`** (the tilted density is the law of `N(m, P⁻¹)`), reusing tide `gaussian-quadratic`'s `integral_inner_euclid_multivariateGaussian'` (`tr(HS) + ⟨m, Hm⟩`). Needs the identification of the density of `multivariateGaussian` with `tiltedWeight / Z`, which Mathlib may not expose directly. Riskier bridge for the same result.

**C. E3 plus the sampler**: the ULA chain for the localised quadratic has the ULA law with `Q = tH + γI` (tide `sampler-laws` instantiated) — a two-line corollary; add to A if cheap.

Claude's preference: A (+ C).

## Numerical check

`scratchpad/numcheck14.py`, `H = [[3, 0.8], [0.8, 1.2]]`, `t = 5`, `γ = 2`, `w₀ = (0.4, −0.7)`, scipy `dblquad`:
mean `(0.1, −0.225)` = `m` exactly; `‖second moments − (P⁻¹ + mmᵀ)‖_max = 7e-18`; `t⟨K⟩ = 0.92854166…` = `½ tr(tH P⁻¹) + ½ t mᵀHm`
(the unlocalised value would be `d/2 = 1`); `Z = 0.69881530…` = `exp(½ mᵀPm) · 2π/√det P`.

## GPT-6 Astra v1

Saved verbatim in `gpt_localised_bias_v1.md`. Summary: A.1–A.4 correct (the quadratic-expectation formula needs no symmetry of `H`; the note's `μ` is `m` in coordinates centred at `w*`). Make explicit the bridge from the note's weight `exp(−tL − (γ/2)|w − w₀|²) = exp(−(γ/2)|w₀|²) · tiltedWeight (tH + γ) (γw₀) w` (the constant cancels in expectations, matters for `Z`). Use `integral_add_right_eq_self` (no integrability needed for the identity), a *normalised* translation lemma `tiltedExpectation P v f = (∫ f(u+m) gW u)/Z(P)` centralising the cancellations, first moments from the Stein identity at `Fin 0` (`fun k : Fin 0 => Fin.elim0 k`), and `(hH.smul ht).add_posSemidef (Matrix.PosSemidef.one.smul hγ)` with `0 ≤ γ`. Defer the eigenvalue form. Cheap consequences: the bias is nonnegative and vanishes iff `m = 0` (iff the anchor is centred when `γ > 0`). On C: finite-step ULA does *not* have covariance `P⁻¹` but the discretisation-corrected one; label it as such if added. Votes **A** with the normalised translation lemma and the original-weight bridge.

## Vote
- Claude: candidate A (normalised translation lemma, original-weight bridge, bias nonnegativity)
- GPT-6 Astra: candidate A (same)

Agreed.

## Result

Committed as \`Laplace/Multi/TiltedGaussian.lean\` (119b6ee), 324 lines, 0 sorries, \`lean-state check\` clean.

Theorems: \`tiltedWeight\`, \`tiltMean\`, \`tiltedZ\`, \`tiltedExpectation\`; \`mulVec_tiltMean\`, \`dotProduct_mulVec_symm\`,
\`tiltedWeight_eq\` (completed square), \`integral_tilted\` (the shift), \`tiltedZ_eq\`, \`tiltedZ_pos\`, \`tiltedExpectation_eq\`
(normalised shift); centred helpers \`integrable_coord_mul_gaussianWeight_matCLM'\`, \`integral_coord_mul_gaussianWeight_matCLM_eq_zero\`,
\`integrable_dotProduct_mul_gaussianWeight_matCLM\`, \`integral_dotProduct_mul_gaussianWeight_matCLM\`,
\`integrable_quadForm_mul_gaussianWeight_matCLM\`; moments \`tiltedExpectation_coord\` (\`= m\`), \`tiltedExpectation_coord_mul\`
(\`P⁻¹ + mmᵀ\`), \`tiltedCov\` (\`P⁻¹\`), \`tiltedExpectation_quadForm\` (\`∑ Hᵢⱼ(P⁻¹)ᵢⱼ + mᵀHm\`), \`tiltedExpectation_const_mul\`;
E3: \`effectivePrecision_posDef\`, \`localisedWeight_eq\` (the note's target is a tilted Gaussian), \`localised_cov\` (\`(tH+γ)⁻¹\`),
\`localised_llc\` (\`½ ∑ (tH)ᵢⱼ((tH+γ)⁻¹)ᵢⱼ + ½ t mᵀHm\`), \`localised_llc_bias_nonneg\`, \`tiltMean_zero\`, \`tiltedWeight_zero\`,
\`localised_llc_unlocalised\` (\`d/2\`).

Surprises: \`integral_add_right_eq_self\` does the whole shift in one line and needs no integrability; the only friction was
\`integral_add\` wanting lambda-typed integrability facts, and Matrix-as-function transparency defeating \`simp … at h\`.
