# Tide: localised-laplace-correction

**Direction (user):** auto mode — "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." / "Continue with what you think best, don't stop". Claude's choice for tide 90: the first correction to the Laplace transform of the localised energy (tide 89's A2), tying it to the energy coefficient e₁.
**Seabed:** laplace, commit dcb6dd5 (tide 89 landed)
**Started:** 2026-09-23T01:06Z

## Candidates v1 (Claude)

Setting as in tides 68–89 (E2 exact localised measure, per frame coordinate `ℓ = λx²/2 + αx³/6 + γx⁴/24`, anchor `a = gx₀`,
`e₁ = energyLocCoeff1 = (a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)`, tide 73's first correction `t⟨ℓ⟩_loc = ½ + e₁/t + O(t⁻²)`).
Landed second-order inputs: `J0_delta_order3`: `|J₀(u) − √(2π)(1 + j₁/u)| ≤ K/u²` for `u ≥ 1`, with `j₁ = 15A²/2 − 3B`,
`A = α/(6λ√λ)`, `B = γ/(24λ²)` (so `j₁ = 5α²/(24λ³) − γ/(8λ²)`); `locDenominator_rate2`: `|D(u) − 1 − d₁/u| ≤ K/u²` with
`d₁ = locD1 = −aα/(2λ²) + (a²/2 − g/2)/λ`; the second-order quotient lemma `ratio_rate_order2`
(`|X − (a + b/t)| ≤ KX/t²`, `|Y − (c + d/t)| ≤ KY/t²`, `c/2 ≤ Y` ⟹ `|X/Y − a/c − (bc − ad)/c²/t| ≤ K/t²`); `prod_rate` (first order).

**A. The first correction to the Laplace transform (1D).** With `A := 1 + s`: `J₀(At)/J₀(t) = 1 + j₁(1/(At) − 1/t) + O(t⁻²) = 1 −
j₁ s/(A t) + O(t⁻²)`, likewise `D(At)/D(t) = 1 − d₁ s/(A t) + O(t⁻²)`, hence
**`|Λ_t(s) − (1+s)^{−1/2} + s·e₁/((1+s)^{3/2} t)| ≤ K_s/t²`** — the `1/t` coefficient of the transform is `−s e₁/(1+s)^{3/2}`, with
**`e₁ = j₁ + d₁`** exactly (sympy: `e₁ − (j₁ + d₁) = 0` from the landed coefficient definitions `energyLocCoeff1 = λc₂'/2 + αc₃/6 +
γ/(8λ²)`, `c₂' = locSecondCoeff2 = N₂ − d₁/λ`, `c₃ = locThirdCoeff`). So the transform's first correction is governed by the energy's
first correction: consistent with `−∂ₛΛ_t|₀ = t⟨ℓ⟩_loc = ½ + e₁/t + …` (a consistency check, not a derivation — we do not differentiate
in `s`). Stated pointwise in `s > −1`, or uniformly over `s ≥ −1 + δ` with `K_δ` (the constants are again monotone in `1/(1+s)`).

**B. On E2.** `∏ᵢ Λ_{t,i}(s) = (1+s)^{−d/2} ∏ᵢ(1 − s e₁ᵢ/((1+s)t) + O(t⁻²))`, hence
**`|⟨e^{−st·L∘A}⟩_loc − (1+s)^{−d/2} + s(∑ᵢe₁ᵢ)/((1+s)^{d/2+1} t)| ≤ K/t²`** — needs a second-order finite-product lemma
(`|∏ᵢ(1 + xᵢ/t + rᵢ) − 1 − ∑xᵢ/t| ≤ C/t²` when `|xᵢ| ≤ X`, `|rᵢ| ≤ R/t²`, `t` large), by induction as in tide 89's `prod_one_rate`.
`∑ᵢe₁ᵢ` is tide 73's E2 coefficient (`t⟨L∘A⟩_loc = d/2 + ∑e₁ᵢ/t + O(t⁻²)`).

**C. The coefficient identity as a standalone lemma** `energyLocCoeff1 = j₁ + d₁` (`laplaceCoeff_eq_energyLocCoeff1`), and the
remark that `−∂ₛ` of the two-term expansion at `s = 0` reproduces tide 73's `½ + e₁/t` and `∂ₛ²` reproduces tide 87's
`t²⟨ℓ²⟩ = ¾ + (… )/t`? — we would only formalise the identity, not the `s`-derivatives.

## Numerical check (scipy quad, λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35); e₁ = (−0.3593, −0.5478))
`t·(Λ_t(s) − (1+s)^{−1/2})` → `−s e₁/(1+s)^{3/2}`: s = −0.5: −0.5066, −0.7715 at t = 640 vs predicted −0.50806, −0.77465; s = 1:
0.12687, 0.19335 vs 0.12701, 0.19366; s = 3: 0.13461, 0.20517 vs 0.13472, 0.20541. `t²·(Λ − (1+s)^{−1/2} + s e₁/((1+s)^{3/2}t))`
converges (s = 1: −0.0892 → −0.0904; s = −0.5: 0.872 → 0.904), i.e. the remainder is `Θ(t⁻²)`. E2 (d = 2): `t·(∏ − (1+s)^{−1})` →
`−s∑e₁/(1+s)²` (s = 1: 0.22647 vs 0.22675), `t²`-remainder → −0.178.

## Questions put to GPT-6 Astra
1. Are A and B correct as stated, including `e₁ = j₁ + d₁` and the sign/power `(1+s)^{−3/2}`, `(1+s)^{−d/2−1}`? Is `ratio_rate_order2`
   directly applicable to `J₀(At)/J₀(t)` (X = J₀(At) with expansion `√(2π) + (√(2π) j₁/A)/t`, Y = J₀(t) with `√(2π) + √(2π)j₁/t`; the
   quotient coefficient `(bc − ad)/c² = j₁/A − j₁ = −j₁ s/A`)? Any subtlety in the `u ≥ 1` threshold at `u = At` for `s < 0`?
2. Which bundle (A+B+C) is right for one tide; is the second-order product lemma the main cost, and is there a slicker route (e.g. log
   of the product, or two-factor `prod_rate_order2` iterated)?
3. Anything missed close to this seabed — e.g. is the `1/t` coefficient of the E2 transform *the same* linear functional `∑e₁ᵢ` that
   appears in tide 73 (energy), tide 87 (variance, `2∑e₁ᵢ`) — worth stating as "one coefficient governs mean, variance-correction and
   transform correction"? Is the second-order transform enough to identify the `1/t` correction to the *law* (Edgeworth-type
   correction to Gamma(½,1))? If so, what is it (a Gamma with shifted shape/rate? `Gamma(½, 1)` plus `e₁/t·(…)`)?
4. Wording against the note (§14 Gamma law): what qualifications for "the first finite-temperature correction to the Gamma law of `tK`
   is governed by `e₁`"?
Vote for one bundle at the end.

(The numerical check script is `numcheck_localised_laplace_correction.py` in this directory; full output in the tide's SRI note.
Symbolic check: `e₁ − (j₁ + d₁) = 0` in sympy from the landed coefficient definitions.)

## GPT-6 Astra v1

Verbatim in `gpt_localised_laplace_correction_v1.md`. Summary: A, B, C correct (sign and powers `(1+s)^{−3/2}`, `(1+s)^{−d/2−1}` right;
`e₁ = j₁ + d₁` a genuine algebraic identity between landed definitions); `ratio_rate_order2` applies directly with `a = c = √(2π)`,
`b = √(2π)j₁/(1+s)`, `d = √(2π)j₁`, coefficient `(bc − ad)/c² = −j₁s/(1+s)`; thresholds `t ≥ max(U, U/(1+s))`. Recommended order:
C → two-factor second-order product lemma → normalised 1D expansion → iterate over the finite set → rescale; prefers the normalised
*uniform* (`s ≥ −1 + δ`) form and warns that uniformity must be carried through the quotient lemma's constant (bound `b` uniformly);
avoid logarithms. Records that one coefficient `E = ∑e₁ᵢ` governs the mean (`k + E/t`), variance (`k + 2E/t`) and transform
(`(1+s)^{−k} − (E/t)s(1+s)^{−k−1}`) corrections, `k = d/2`; identifies the transform-level correction as that of the signed measure
`(E/t)(Γ(k+1,1) − Γ(k,1))`, density `g_k(y)[1 + (E/t)(y/k − 1)]` (1D: `g_{1/2}(y)[1 + (e₁/t)(2y − 1)]`), equivalent to first order to
`Gamma(k, rate 1 − E/(kt))`; this is *not* a proved distributional/density-level expansion. Wording: transform-level correction for the
exact localised measure, fixed parameters/dimension, eventual bounds, separation from `s = −1`; `d = 0` separately (`δ₀`, `E = 0`).

## Vote
- Claude: A+B+C (pointwise in `s > −1` this tide; the uniform-in-`s ≥ −1 + δ` normalised form as a follow-up strengthening)
- GPT-6 Astra: A+B+C, "with a normalized uniform 1D theorem and an iterated two-factor second-order product lemma; leave the
  signed-law expansion as an identified interpretation"

Agreed: A+B+C (architectural divergence noted: pointwise vs uniform in `s`; Step 3 does pointwise).

## Result

Commit `35b12f2` on `tide/localised-laplace-correction`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/LocalisedLaplaceCorrection.lean` (     308 lines).
A + B + C as voted (pointwise in `s > −1`; the uniform-in-`s` normalised form left as a follow-up).
Generic: `prod_rate_order2` (two factors `1 + x/t + O(t⁻²)`), `scaled_ratio_rate2` (`F((1+s)t)/F(t) = 1 − f₁s/((1+s)t) + O(t⁻²)` via
`ratio_rate_order2`), `prod_one_rate2` (finite product, existential constants by `Finset.induction_on`).
1D: `cubicScale_sq`, `energyLocCoeff1_eq_J1_add_D1` (`e₁ = j₁ + d₁`), `locLaplace_scaled_rate2`, `locLaplace_rate2`.
E2: `localisedLaplace_rate2`.

Surprises: `e₁ = j₁ + d₁` closes by `field_simp; ring` after one `cubicScale_sq` rewrite (`√λ² = λ`) — the whole first correction of
the transform is the energy's first correction, coordinate by coordinate.
