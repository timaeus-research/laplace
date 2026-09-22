# Tide: localised-mean-euclid

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); GPT's next target after tide 83: the mean's squared discrepancy against the displayed (resolvent) mean, reusing the
squared-norm transport, plus its derivative.
**Seabed:** laplace, commit 25d0426 (tide 83 merged with a concurrent germbij landing) (worktree `laplace-tide-localised-mean-euclid`, branch `tide/localised-mean-euclid` off `main`)
**Started:** 2026-09-22T20:05Z

## Candidates v1 (Claude)

Setting (E2, as in tides 68–83): `m(t) = ⟨w⟩_loc` the exact localised mean, `μᵢ(t) = ⟨uᵢ⟩_loc` its frame coordinates (`m − c = Qμ`),
`Pᵢ(t) = −αᵢt/(2(tλᵢ + g)²) + aᵢ/(tλᵢ + g)` (`aᵢ = g u₀ᵢ`) the note's displayed (E3) mean shift per frame coordinate, so that the displayed
physical mean is `m_S(t) = c + QP(t)` (tide 74's `meanShiftLoc + g • locS *ᵥ (w₀ − c)`), `rᵢ = meanLocResidual2ᵢ` the `t⁻²` coefficient
of `μᵢ − Pᵢ` (tide 74, `|μᵢ − Pᵢ − rᵢ/t²| ≤ K/t³`), `c₁ᵢ = −αᵢ/(2λᵢ²) + aᵢ/λᵢ` the localised leading mean, `c'ᵢ = meanLocCoeff2ᵢ` its second-order
coefficient (`μᵢ = c₁ᵢ/t + c'ᵢ/t² + O(t⁻³)`), and exactly `∂ₜμᵢ = −Cov_loc[L∘A, uᵢ]` (tide 80) with
`|t² Cov_loc[L∘A, uᵢ] − c₁ᵢ − 2c'ᵢ/t| ≤ K/t²` (tide 79). `‖x‖² = ∑ⱼ xⱼ²`.

**A. The mean's squared discrepancy from the displayed mean.**
`|t⁴ ‖m(t) − m_S(t)‖² − ∑ᵢ rᵢ²| ≤ K/t`, i.e. `‖m − m_S‖² = ‖r‖²/t⁴ + O(t⁻⁵)` — eq:mean's `O(S²)` remainder, invariantly.
Route: `m − m_S = Q(μ − P)` so `‖m − m_S‖² = ∑ᵢ (μᵢ − Pᵢ)²` (`QᵀQ = 1`: `∑ⱼ (Qy)ⱼ² = ∑ᵢ yᵢ²`), per coordinate `|t²(μᵢ − Pᵢ) − rᵢ| ≤ K/t`
(tide 74's rate × `t²`), the square lemma `sq_rate`, and a vector transport `euclid_conj_rate` (the vector analogue of
`frobenius_conj_rate`: `|t² fᵢ − wᵢ| ≤ K/t ⟹ |t⁴ ∑ⱼ (∑ᵢ Qⱼᵢ fᵢ)² − ∑ᵢ wᵢ²| ≤ K/t`).

**B. The mean's derivative: the derivative reading of eq:mean.**
Exactly `∂ₜ mⱼ = −∑ᵢ Qⱼᵢ Cov_loc[L∘A, uᵢ]` (from `hasDerivAt_localised_frame_pow` at `m = 1` and `localised_mean_coord`), and
`|t⁶ ‖∂ₜm(t) + Q c₁/t²‖² − 4∑ᵢ c'ᵢ²| ≤ K/t`, i.e. `‖∂ₜm + Qc₁/t²‖² = 4‖c'‖²/t⁶ + O(t⁻⁷)`: against the unlocalised-plus-anchor leading
derivative `−Qc₁/t²` the coefficient is `2‖c'‖`. Route: per coordinate `t³(Cov_loc[L∘A, uᵢ] − c₁ᵢ/t²) − 2c'ᵢ = t(t²Cov − c₁ − 2c'/t)`, then
the `t³` vector transport (wrapper `f̃ = t f` as in tide 83).

**C. The derivative against the displayed mean's derivative.** `∂ₜPᵢ` in closed form (`−αᵢ(g − tλᵢ)/(2(tλᵢ + g)³) − aᵢλᵢ/(tλᵢ + g)²`),
and `|t⁶ ‖∂ₜ(m − m_S)‖² − 4∑ᵢ rᵢ²| ≤ K/t` — the derivative reading of A, from the derivative expansions (per coordinate
`t³(∂ₜPᵢ + c₁ᵢ/t²) + 2(c'ᵢ − rᵢ)` is `O(1/t)` since `c'ᵢ − rᵢ = locLeadingCoeff2ᵢ = αᵢg/λᵢ³ − g aᵢ/λᵢ²` is exactly `P`'s own `t⁻²`
coefficient). Requires `HasDerivAt` of `Pᵢ` (rational in `t`) and its second-order expansion `|t³(∂ₜPᵢ + c₁ᵢ/t²) + 2 locLeadingCoeff2ᵢ| ≤ K/t`.

**D (cheap).** Two-sided bounds for A when `∑rᵢ² > 0`, and the relative form of A against `‖m_S − c‖² = ∑Pᵢ²` (`t²‖m_S − c‖² → ∑c₁ᵢ²`,
needs `∑c₁ᵢ² > 0` as a hypothesis).

Sizing: vector transport + `t³` wrapper ~90 lines, A ~60, B ~80, C ~150 (the rational derivative and its expansion), D ~40.
Target A + B + C, D if cheap.

## Numerical check

`numcheck_localised_mean_euclid.py` (two frame coordinates, `λ = (1.3, .9)`, `α = (.7, −.4)`, `γ = (1.1, .8)`, `g = .8`, `u₀ = (.55, −.35)`):
`∑rᵢ² = 0.02585691`, `4∑c'ᵢ² = 0.43430821`; at `t = 80 … 1280`: `t⁴‖μ − P‖² = 0.022282, 0.023996, 0.024908, 0.025377, 0.025616`
(`t·resid ≈ −0.29 … −0.31`), `t⁶‖Cov[L,u] − c₁/t²‖² = 0.37431, 0.40301, 0.41832, 0.42623, 0.43025` (`t·resid ≈ −4.8 … −5.2`): both
`O(1/t)`.

## GPT-6 Astra v1

Verbatim in `gpt_localised_mean_euclid_v1.md` (prompt: `gpt_localised_mean_euclid_prompt_v1.md`). Summary: **A, B, C correct; D correct
with its nondegeneracy hypotheses.** C's closed form `Pᵢ' = −αᵢ(g − tλᵢ)/(2d³) − aᵢλᵢ/d²` (`d = tλᵢ + g`) confirmed, and
`Pᵢ = c₁ᵢ/t + bᵢ/t² + O(t⁻³)` with `bᵢ = αᵢg/λᵢ³ − gaᵢ/λᵢ² = locLeadingCoeff2ᵢ` exactly, so `(μᵢ − Pᵢ)' = −2rᵢ/t³ + O(t⁻⁴)` from the two
derivative expansions. Cautions: fixed parameters/frame/anchor; nonzero denominators eventually; use derivative identities, never
differentiate an `O(t⁻³)` remainder; no `r ≠ 0` needed for A–C; **Lean norm trap** — the standard norm on `ι → ℝ` is the sup norm, so use
explicit sums of squares (we do). Wording: "For fixed parameters, the remainder in eq:mean has Euclidean norm `‖r‖₂/t² + O(t⁻³)`; its
time derivative has Euclidean norm `2‖r‖₂/t³ + O(t⁻⁴)`, established independently from the derivative expansions" (the unsquared forms
via the reverse triangle inequality from the vector bounds; not formalised). Keep B alongside C, with **C the headline** (C
differentiates the displayed approximation; B identifies the correction to the simpler leading derivative). Lean route: separate the
exact orthogonal sum-of-squares identity, the finite-family squared-rate lemma and thin scaling wrappers; for `Pᵢ'` differentiate inverse
powers or the quotient and normalise afterwards; for the derivative rate use the exact cancellations
`(1−z)/(1+z)³ − (1 − 4z) = z²(9 + 11z + 4z²)/(1+z)³`, `1/(1+z)² − (1 − 2z) = z²(3 + 2z)/(1+z)²` with `z = g/(λᵢt)` (our rational
remainder is the cleared-denominator form of exactly these). Cheap additions: the unsquared norms, the degenerate `r = 0` consequences
(`‖m − m_S‖₂ = O(t⁻³)`, `‖(m − m_S)'‖₂ = O(t⁻⁴)`). **Next target**: the energy discrepancy from the Gaussian trace prediction using tide
73's coefficient (verify exactly which predictor is subtracted); the specialisation `w₀ = c` is a cheap corollary, not the next main
target (it does not eliminate the anharmonic mean residual).

## Vote
- Claude: A + B + C + D (D is one call of `two_sided_of_rate`)
- GPT-6 Astra: "**Vote: A+B+C.** Land A first, B second, and C last … Add D only if the existing wrappers make it genuinely trivial."
