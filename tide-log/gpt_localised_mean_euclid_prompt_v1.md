You are consulted (one round) on tide 84 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders `≤ K/t^n` for `t ≥ T ≥ 1`. Your previous consult (tide 83) named the mean's squared discrepancy against
the resolvent mean as the best next target, "if meanLocResidual2 already supplies the required vector coefficient and quantitative
remainder" — it does, per frame coordinate (tide 74: `|μᵢ − Pᵢ − rᵢ/t²| ≤ K/t³`, and in physical coordinates
`localisedRotatedAnharmonic_displayed_order2_rate`).

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

## Seabed facts (landed)
- tide 74: `meanLocResidual2` (`rᵢ = B₁ + aα²/λ⁴ − aγ/(2λ³) − αa²/(2λ³)`, `B₁ = −5α³/(8λ⁵) + 2αγ/(3λ⁴)`), `meanLocCoeff2 = meanLocResidual2 +
  locLeadingCoeff2`, `locLeadingCoeff2 = αg/λ³ − g·a/λ²` (`a = g x₀`), the per-coordinate rate and the physical-coordinate displayed rate.
- tide 80: `hasDerivAt_localised_frame_pow` (`d/ds ⟨uᵢ^m⟩_loc = −Cov_loc,t[L∘A, uᵢ^m]`); tide 81: `localised_mean_coord`
  (`⟨wⱼ⟩_loc = cⱼ + ∑ᵢ Qⱼᵢ μᵢ`); tide 79: `localisedCovK_frame_lin_order2_rate` (`|t²Cov_loc[L∘A, uᵢ] − c₁ᵢ − 2c'ᵢ/t| ≤ K/t²`).
- tides 82/83: `sq_rate`, `frobenius_conj_rate` (matrix transport), `frobenius_conj_rate_cubic`, `ratio_rate`, `two_sided_of_rate`,
  `sum_rate_div`.

## Numerical check (done; two frame coordinates, λ = (1.3, .9), α = (.7, −.4), γ = (1.1, .8), g = .8, frame anchor u₀ = (.55, −.35))
sum r_i^2 = 0.02585691    4 sum c'_i^2 = 0.43430821
t=    80: t^4|mu-P|^2 = 0.02228165 (t*resid -0.28602)   t^6|Cov[L,u]-c1/t^2|^2 = 0.374310 (t*resid -4.7999)
t=   160: t^4|mu-P|^2 = 0.02399632 (t*resid -0.29770)   t^6|Cov[L,u]-c1/t^2|^2 = 0.403013 (t*resid -5.0072)
t=   320: t^4|mu-P|^2 = 0.02490756 (t*resid -0.30379)   t^6|Cov[L,u]-c1/t^2|^2 = 0.418321 (t*resid -5.1160)
t=   640: t^4|mu-P|^2 = 0.02537736 (t*resid -0.30691)   t^6|Cov[L,u]-c1/t^2|^2 = 0.426227 (t*resid -5.1717)
t=  1280: t^4|mu-P|^2 = 0.02561591 (t*resid -0.30849)   t^6|Cov[L,u]-c1/t^2|^2 = 0.430246 (t*resid -5.1999)
(both scaled residuals bounded: A and B hold numerically at rate O(1/t).)

## Questions
1. Are A, B, C, D correct as stated? Check C's closed form `∂ₜPᵢ = −αᵢ(g − tλᵢ)/(2(tλᵢ + g)³) − aᵢλᵢ/(tλᵢ + g)²` and the claim that the
   `t⁻²` coefficient of `Pᵢ` is exactly `locLeadingCoeff2ᵢ` (so that `c'ᵢ − rᵢ` is that coefficient and `∂ₜ(μᵢ − Pᵢ) = −2rᵢ/t³ + O(t⁻⁴)`).
   Any hidden hypothesis?
2. Wording against the note (eq:mean `m = m_S + O(S²)`, E3): "the O(S²) remainder of eq:mean has Euclidean norm ‖r‖/t² + O(t⁻³), and
   its time-derivative has norm 2‖r‖/t³ + O(t⁻⁴), established from the derivative expansions" — right? Is B (against the leading
   derivative `−Qc₁/t²`) worth stating alongside C?
3. Lean route: a vector transport lemma (Euclidean analogue of `frobenius_conj_rate`, `∑ⱼ (Qy)ⱼ² = ∑ᵢ yᵢ²` from `QᵀQ = 1` via
   `Matrix.dotProduct_mulVec`/`vecMul_transpose`) plus the same square/cubic wrappers — anything cheaper? For C's rational derivative,
   differentiate the closed form of `Pᵢ` with `HasDerivAt.div` or expand to `−αᵢt/2·(tλᵢ + g)⁻² + aᵢ(tλᵢ + g)⁻¹` and use `HasDerivAt.inv`/`pow`?
4. Better or additional candidates close to this seabed, and the best next target after this tide (the mean/covariance programme on
   E2 now has: entrywise expansions, the trace probe, Frobenius discrepancies and their derivatives; candidates: the energy's
   discrepancy from the Gaussian trace prediction in the same invariant form (tide 73's e₁), a joint statement bundling
   mean/covariance/energy remainders, or a statement at the anchor `w₀ = c`).
Vote: which bundle (A, A+B, A+B+C, A+B+C+D) should this tide commit to? Be concrete and terse; flag any error explicitly.
