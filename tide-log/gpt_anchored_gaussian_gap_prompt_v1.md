You are consulted (one round) on tide 94 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders. Tide 93 (your consult) landed: the exact localised anharmonic transform (E2) and E3's *centred* Gaussian
prediction `Λ^G = ∏ᵢ√((tλᵢ+g)/((1+s)tλᵢ+g))` differ by `−sC₁/((1+s)^{d/2+1}t) + O(t⁻²)`, `C₁ = ∑ᵢ(e₁ᵢ + g/(2λᵢ))`. You flagged the
centred-vs-anchored distinction: the anchored Gaussian (localiser kept at `u₀`, means `aᵢ/(tλᵢ+g)`, `aᵢ = g u₀ᵢ`) has transform
`Λ^{G,anch} = Λ^G·exp(−(st/2)∑ᵢλᵢaᵢ²/((tλᵢ+g)((1+s)tλᵢ+g)))` and shifts the gap coefficient by `−∑aᵢ²/(2λᵢ)`. This tide is that.

## Seabed
Sampler side: `tiltedExpectation P v φ = (∫ φ u·exp(−½uᵀPu + vᵀu))/tiltedZ P v`, `tiltedZ_eq : tiltedZ P v = exp(½ mᵀPm)·gaussianZ(matCLM P)`
with `m = tiltMean P v = P⁻¹v`, `gaussianZ_matCLM : = √(2π)^d/√det P`; tide 91's `tiltedExpectation_exp_quadForm` (centred, `v = 0`):
`⟨e^{−c·½uᵀHu}⟩_Q = √det Q/√det(Q + cH)`; E3's anchored object is `localised_llc : t·tiltedExpectation (t•H + γ•1) (γ•w₀) (½uᵀHu) = ½∑tλᵢ/(tλᵢ+γ)
+ (t/2)·mᵀHm`; eigenbasis `U = orthoOf hH.1`, `Uᵀ(tH + γI)⁻¹U = diag(1/(tλᵢ+γ))` (`orthoOf_transpose_localised_inv_mul`). E2 side: tide 90's
`localisedLaplace_rate2` (`Λ = (1+s)^{−d/2}(1 + ∑(−e₁ᵢs/(1+s))/t) + O(t⁻²)`), tide 93's `gaussianTransform_rate2`, `sqrt_one_add_sub_le`,
`prod_rate_order2`, `prod_one_rate2`; `energyLocCoeff1 = λc₂'/2 + αc₃/6 + γ/(8λ²)` with `e₁ = (a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)`;
Mathlib `Real.abs_exp_sub_one_sub_id_le : |x| ≤ 1 → |exp x − 1 − x| ≤ x²`.

## Candidates v1 (Claude)

**A′ (Sampler, exact).** For `Q ≻ 0`, `Q + cH ≻ 0`, any tilt `v`:
`tiltedExpectation Q v (e^{−c·½uᵀHu}) = exp(½ m_c·(Q+cH)m_c − ½ m·Qm)·√det Q/√det(Q+cH)`, `m = Q⁻¹v`, `m_c = (Q+cH)⁻¹v` — the same integrand
identity as tide 91 (`e^{−c·½uᵀHu}·tiltedWeight Q v u = tiltedWeight (Q+cH) v u`, the linear term untouched) plus `tiltedZ_eq` twice;
equivalently `exp(½ vᵀ((Q+cH)⁻¹ − Q⁻¹)v)·√det Q/√det(Q+cH)`.
**A″ (Sampler, eigen form).** For `Q = tH + gI`, `c = st`: `½vᵀ((Q+stH)⁻¹ − Q⁻¹)v = ½∑ᵢ(Uᵀv)ᵢ²(1/((1+s)tλᵢ+g) − 1/(tλᵢ+g))` via the
quadratic-form conjugation `vᵀMv = (Uᵀv)ᵀ(UᵀMU)(Uᵀv)` and the landed diagonalisations; so
**`Λ^{G,anch}_t(s) = ∏ᵢ√((tλᵢ+g)/((1+s)tλᵢ+g))·exp(∑ᵢ(aᵢ²/2)(1/((1+s)tλᵢ+g) − 1/(tλᵢ+g)))`**, `aᵢ = (Uᵀv)ᵢ` — E3's anchored Gaussian
prediction for the scaled-energy transform.
**B (Multi, expansion).** With the E2 frame data (`aᵢ = g·u₀ᵢ`, `u₀ = affineFrame`): the exponent is `x_t = −s∑ᵢaᵢ²/(2λᵢ(1+s)t) + O(t⁻²)`
(per-term rational identity `(aᵢ²/2)(1/((1+s)tλᵢ+g) − 1/(tλᵢ+g)) = −(aᵢ²/2)·stλᵢ/((tλᵢ+g)((1+s)tλᵢ+g))`, bounded by `|s|aᵢ²/(2(1+s)λᵢt)` and
with remainder `O(t⁻²)` from `g` in the denominators), `|e^x − 1 − x| ≤ x²` for `|x| ≤ 1` (eventually), and the two-factor rule:
**`Λ^{G,anch} = (1+s)^{−d/2}(1 + s(g∑ᵢ1/(2λᵢ) − ∑ᵢaᵢ²/(2λᵢ))/((1+s)t)) + O(t⁻²)`**.
**C (Multi, the gap).** **`Λ − Λ^{G,anch} = −(1+s)^{−d/2}·s·C₁′/(1+s)/t + O(t⁻²)`** with
**`C₁′ = ∑ᵢ(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ)) = ∑ᵢ(e₀ᵢ − aᵢαᵢ/(2λᵢ²))`**, `e₀ = 5α²/(24λ³) − γ/(8λ²)` (identity by unfolding `energyLocCoeff1`):
E3's anchored Gaussian prediction captures *every* localiser effect at order `1/t` (the `g` and `a²` terms cancel exactly); the residual is
purely anharmonic — the unlocalised first correction `e₀` plus the cubic–anchor cross term `−aα/(2λ²)`; at the minimum anchor
(`a = 0`) it is `∑e₀ᵢ`, and it vanishes for the quadratic model.

## Numerical check (scipy quad, λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35); `C₁ = −0.15487`, `∑a²/(2λ) =
0.11802`, `C₁′ = −0.27289 = ∑(e₀ − aα/(2λ²))` ✓)
The anchored product-times-exp formula equals the direct Gaussian integral ratio to all digits; `t(Λ^{anch} − (1+s)^{−d/2})` → `s(g∑1/(2λ) −
∑a²/(2λ))/(1+s)^{d/2+1}` (s = 1: 0.15845 vs 0.15853); `t(Λ − Λ^{anch})` → `−sC₁′/(1+s)^{d/2+1}` (s = 1: 0.06514 → 0.06803 at t = 40 → 640 vs
0.06822; s = −0.5: −0.480 → −0.541 vs −0.546; s = 3: 0.0496 → 0.05106 vs 0.05117); `t²`-remainders converge.

## Questions
1. Are A′, A″, B, C correct — the sign and form of the exponent (`½vᵀ((Q+cH)⁻¹ − Q⁻¹)v`), the anchored expansion coefficient, and the
   identity `e₁ + g/(2λ) − a²/(2λ) = e₀ − aα/(2λ²)`? Is "the anchored Gaussian captures every localiser effect at order 1/t; the
   residual `∑(e₀ᵢ − aᵢαᵢ/(2λᵢ²))` is purely anharmonic" a correct reading (the cross term `−aα/(2λ²)` involves the anchor but only through
   the cubic coefficient)?
2. Bundle and route: for B, the exponent's `1/t` expansion plus `Real.abs_exp_sub_one_sub_id_le` (needs `|x_t| ≤ 1` eventually, threshold
   `t ≥ |s|∑aᵢ²/(2λᵢ(1+s))`) and `prod_rate_order2` for the two factors — any slicker route? For A″, is the quadratic-form conjugation
   lemma `vᵀMv = (Uᵀv)ᵀ(UᵀMU)(Uᵀv)` the right tool, or is there a landed lemma (`sum_mul_apply_eq_trace`, `dotProduct_mulVec` conj)?
   Should A″ be stated for general `v` (then E3's `v = γ•w₀`) or directly for `γ•w₀`?
3. Anything missed close to this seabed: e.g. the anchored analogue of tide 93 for the *energy* (`t⟨L⟩ − t·(½tr(H(tH+gI)⁻¹) + (t/2)mᵀHm)`
   with the anchored Gaussian energy `localised_llc`'s second term: is its gap coefficient also `C₁′`? — consistent with `−∂ₛ|₀`), or a
   packaging theorem "three gaps, one coefficient" for the anchored prediction; the noncentral-χ² reading of the anchored Gaussian law?
4. Wording against E3/E2: "E3's anchored Gaussian prediction reproduces the exact localised transform to order `1/t` up to the purely
   anharmonic coefficient `C₁′ = ∑(e₀ᵢ − aᵢαᵢ/(2λᵢ²))`; the centred prediction (tide 93) misses in addition the anchor term `∑aᵢ²/(2λᵢ)`" —
   fair? Qualifications?
Vote for one bundle at the end.
