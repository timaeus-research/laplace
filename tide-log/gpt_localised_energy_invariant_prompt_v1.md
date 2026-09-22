You are consulted (one round) on tide 85 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders. Your previous consult (tide 84) named "the energy discrepancy from the Gaussian trace prediction,
using tide 73's coefficient after verifying exactly which predictor was subtracted" as the best next target. The predictor subtracted in
tide 73 is `½ tr(tH S(t))`, `S = (tH + gI)⁻¹` (E3's Gaussian-prior trace), and the landed first-order coefficient is
`∑ᵢ (e₁ᵢ + g/(2λᵢ))` with `e₁ + g/(2λ) = energyCoeff1 + a²/(2λ) − aα/(2λ²)`, `a = g u₀` the frame anchor times `g`.

## Candidates v1 (Claude)

Setting (E2, as in tides 68–84): `⟨L∘A⟩_loc(t)` the exact localised energy, `S(t) = (tH + gI)⁻¹`, `e₁ᵢ = energyLocCoeff1ᵢ` (tide 73),
`E₁ = ∑ᵢ energyCoeff1ᵢ` the unlocalised anharmonic energy correction (`energyCoeff1 = −γ/(8λ²) + 5α²/(24λ³)`), `m₁ = Q(−αᵢ/(2λᵢ²))` the
unlocalised first-order mean shift (physical coordinates), `aᵢ = g u₀ᵢ`, `u₀ = Qᵀ(w₀ − c)`. Landed (tide 73):
`|t⟨L∘A⟩_loc − ½tr(tH S(t)) − (∑ᵢ (e₁ᵢ + g/(2λᵢ)))/t| ≤ K/t²` (`localisedRotatedAnharmonic_llc_sub_trace_rate`) with
`e₁ + g/(2λ) = energyCoeff1 + a²/(2λ) − aα/(2λ²)` per coordinate (`energyLocCoeff1_add_eq`).

**A. The invariant form of the energy's anchor correction** (tide 73's coefficient, coordinate-free):
`∑ᵢ (e₁ᵢ + g/(2λᵢ)) = E₁ + (g²/2)(w₀ − c)ᵀH⁻¹(w₀ − c) + g ⟨w₀ − c, m₁⟩`, hence
`t⟨L∘A⟩_loc − ½tr(tH S) = [E₁ + (g²/2)(w₀ − c)ᵀH⁻¹(w₀ − c) + g⟨w₀ − c, m₁⟩]/t + O(t⁻²)`: the discrepancy from the Gaussian trace
prediction is the unlocalised anharmonic correction plus a quadratic form in the anchor displacement (the anchored Gaussian's
squared-mean energy) plus the coupling of the anchor displacement to the unlocalised mean shift. Pure algebra on landed results
(`∑ aᵢ²/λᵢ = g² (w₀−c)ᵀ Q diag(1/λ) Qᵀ (w₀−c)`, `∑ aᵢαᵢ/(2λᵢ²) = −g ⟨w₀ − c, m₁⟩` via `affineFrame`, `dotProduct`/`mulVec`).

**B. The derivative reading of the LLC.** Exactly `∂ₜ⟨L∘A⟩_loc = −Var_loc(L∘A)` (tide 77's derivative identity with `ψ = L∘A`),
`Var_loc(L∘A) = ∑ᵢ Var_loc(ℓᵢ)` (the frame family is a product measure), and per coordinate `|t² Var_loc(ℓᵢ) − ½| ≤ K/t`, hence
`|t²(−∂ₜ⟨L∘A⟩_loc) − d/2| ≤ K/t`: **the LLC `d/2` is the leading coefficient of `−∂ₜ⟨L∘A⟩_loc`** (and of `t²Var_loc(L∘A)`), the
derivative reading of `t⟨L∘A⟩_loc → d/2`. New analytic input: the leading localised energy variance
`t²(⟨ℓ²⟩_loc − ⟨ℓ⟩_loc²) → ½` — `ℓ² = λ²x⁴/4 + λαx⁵/6 + (λγ/24 + α²/36)x⁶ + αγx⁷/72 + γ²x⁸/576`, so it needs the localised fourth
moment to leading order (`3/(λt)²`, landed) and even-moment envelopes through degree 8 (`⟨x²ᵏ⟩_loc ≤ Cₖ/tᵏ`; the machinery of tides
73/76/78 reaches degree 14), plus the leading energy `t⟨ℓ⟩_loc → ½` (landed).

**C (cheap).** The squared discrepancy: `|t⁴ (⟨L∘A⟩_loc − ½tr(H S))² − (∑ᵢ (e₁ᵢ + g/(2λᵢ)))²| ≤ K/t` (`sq_rate` on tide 73's rate) — the
scalar analogue of tides 82–84.

**D (optional, if B lands).** The derivative discrepancy from the trace prediction's derivative:
`−∂ₜ[½tr(tHS)] = −½∑ᵢ λᵢg/(tλᵢ + g)²`… i.e. `∂ₜ[½ ∑ tλᵢ/(tλᵢ + g)] = ½∑ λᵢg/(tλᵢ+g)²`, and `|t²(−∂ₜ⟨L∘A⟩_loc − ∂ₜ[½tr(tHS)]) − d/2| ≤ K/t`
(the trace prediction's derivative is `O(t⁻²)` with coefficient `g∑1/(2λᵢ)`… this only shifts the `1/t` term of `t²(−∂ₜ⟨L⟩)`, which B does
not resolve; so D would just restate B — drop unless B reaches second order).

Sizing: A ~120 lines (mulVec/dotProduct algebra + the coefficient identity); B ~400 lines (energy variance per coordinate: pointwise
expansion of `ℓ²`, eight even-moment envelopes, ratio bookkeeping; product-measure variance splitting; derivative identity
instantiation); C ~20. Target A + B + C.

## Seabed facts (landed)
- tide 73 (`LocalisedLLCCoeff`): `localisedEnergy_order2_rate` (1D: `|t⟨ℓ⟩_loc − ½ − e₁/t| ≤ K/t²`), `localisedEnergy_sub_trace_rate`,
  `localisedRotatedAnharmonic_llc_order2_rate`, `localisedRotatedAnharmonic_llc_sub_trace_rate`, `energyLocCoeff1_add_eq`,
  `trace_scalar_remainder`; the localised moments `locSecondMoment_loc_rate2`, `locThirdMoment_loc_rate2`, `locFourthMoment_loc_rate2`
  (second order), even-moment envelopes via `locWeight_le` (`φ ≤ e^{gx₀²/2}`) and the unlocalised `evenMoment_bound k`.
- tide 77 (`LocalisedDerivative`): `hasDerivAt_localised_separable` — `d/ds ⟨ψ⟩_loc(s) = −Cov_loc,t[L, ψ]` for a continuous probe with
  the two integrability hypotheses (`L·ψ·e^{−tL_loc}` and `ψ·e^{−tL_loc}`); tide 80/81 instantiate it for frame monomials.
- separability on the frame family: `gibbsCov_addSeparable_fst_snd_eq_zero`-type lemmas, `gibbsCov_energy_*_separable` (tide 76),
  `separableAnharmonic_eq_sum`.
- tides 82–84: `sq_rate`, `sum_rate_div`, transports.

## Numerical check (done; 2D, rotation θ = 0.6, λ = (1.3, .9), α = (.7, −.4), γ = (1.1, .8), g = .8, anchor off the minimum)
(a) sum(e1 + g/2lam) = -0.0399991114   E1 + g^2/2 <w0-c,Hinv(w0-c)> + g<w0-c,m1> = -0.0399991114
t=   40: -d<L>/dt = 6.0113801038e-04  Var_loc(L) = 6.0113743192e-04   t^2 Var = 0.961820 (t*resid -1.5272)   per coord: 0.48523, 0.47659
t=   80: -d<L>/dt = 1.5321156000e-04  Var_loc(L) = 1.5321140975e-04   t^2 Var = 0.980553 (t*resid -1.5558)   per coord: 0.49244, 0.48811
t=  160: -d<L>/dt = 3.8679227984e-05  Var_loc(L) = 3.8679189684e-05   t^2 Var = 0.990187 (t*resid -1.5700)   per coord: 0.49618, 0.49401
t=  320: -d<L>/dt = 9.7175034401e-06  Var_loc(L) = 9.7174937704e-06   t^2 Var = 0.995071 (t*resid -1.5772)   per coord: 0.49808, 0.49699
t=  640: -d<L>/dt = 2.4353787093e-06  Var_loc(L) = 2.4353762799e-06   t^2 Var = 0.997530 (t*resid -1.5807)   per coord: 0.49904, 0.49849
((a) the invariant identity holds to 10 digits; (b) the exact derivative identity holds to finite-difference precision; (c)
`t²Var_loc(L∘A) → 1 = d/2` with `t·resid ≈ −1.58` bounded, per coordinate → ½.)

## Questions
1. Are A, B, C correct as stated? In A, check the sign of the coupling term `g⟨w₀ − c, m₁⟩` (`m₁ = Q(−α/(2λ²))`, so
   `−∑ aᵢαᵢ/(2λᵢ²) = +g⟨w₀−c, m₁⟩`). In B, is the leading energy variance `t²Var_loc(ℓ) → ½` right for the localised 1D measure with
   anchor off the minimum (the localiser and anchor enter only at `O(1/t)`)? What is the `1/t` coefficient of `t²Var_loc(L∘A)` (numerically
   ≈ −1.58 here) — is it `2∑ᵢ e₁ᵢ` (the formal derivative of tide 73's expansion `t⟨L⟩ = d/2 + ∑e₁/t` gives `−∂ₜ⟨L⟩ = d/(2t²) + 2∑e₁/t³`;
   here `2∑e₁ = 2·(−0.04 − ∑g/(2λ)) = 2·(−0.04 − 0.752) ≈ −1.58` — consistent), and is reaching it in this tide realistic (it needs the
   second-order fourth moment, landed, and fifth/sixth moments to leading order, landed in tide 78)?
2. Wording against the note (E3: the localiser as a Gaussian prior; the LLC `λ = d/2` as `t⟨L⟩`'s limit): is "the discrepancy of the
   localised energy from the Gaussian trace prediction has the invariant first-order coefficient `E₁ + (g²/2)(w₀−w*)ᵀH⁻¹(w₀−w*) +
   g⟨w₀−w*, m₁⟩`: the unlocalised anharmonic correction, the anchored Gaussian's squared-mean energy, and the anchor–mean-shift
   coupling" right, and is B's "the LLC is the leading coefficient of `−∂ₜ⟨L⟩_loc = Var_loc(L)`" a statement worth making (it is the
   exact fluctuation–response identity `−∂ₜ⟨L⟩ = Var(L)` plus the leading variance)?
3. Lean route for B's variance: expand `ℓ² − ⟨ℓ⟩²`? Or use the Stein/IBP identity from tide 77 (`t²Cov_loc[ℓ, xⁿ]` reduction) with
   `ψ = ℓ` written as a polynomial to get `t²Var_loc(ℓ) = (λ/2)t²Cov[ℓ,x²] + (α/6)t²Cov[ℓ,x³] + (γ/24)t²Cov[ℓ,x⁴]` and reuse tide 76/78's
   landed `t²Cov_loc[ℓ, x²] → 1/λ`, `t²Cov_loc[ℓ, x³] → 0`?, `t²Cov_loc[ℓ, x⁴] → 0`? (then `t²Var → (λ/2)(1/λ) = ½` immediately) — which
   covK rates are needed and are they landed (tide 76 has `localisedCovK_frame_sq_rate` (`→ 1/λ`) and `_lin_rate`; cubic/quartic probes?)?
4. Better or additional candidates close to this seabed, and the best next target after this tide?
Vote: which bundle (A, A+C, A+B+C) should this tide commit to? Be concrete and terse; flag any error explicitly.
