# Tide: localised-energy-invariant

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); GPT's next target after tide 84: the energy discrepancy from the Gaussian trace prediction in invariant form (tide
73's coefficient), plus the fluctuation–response reading of the LLC.
**Seabed:** laplace, commit 91570d5 (worktree `laplace-tide-localised-energy-invariant`, branch
`tide/localised-energy-invariant` off `main`)
**Started:** 2026-09-22T20:19Z

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

## Numerical check

`numcheck_localised_energy_invariant.py` (2D, rotation `θ = 0.6`, anchor off the minimum): (a) `∑ᵢ(e₁ᵢ + g/(2λᵢ)) = −0.0399991114 =
E₁ + (g²/2)⟨w₀ − c, H⁻¹(w₀ − c)⟩ + g⟨w₀ − c, m₁⟩` to 10 digits; (b) `−d⟨L⟩/dt` by central differences equals `Var_loc(L)` to 6 digits at
`t = 40 … 640`; (c) `t²Var_loc(L) = 0.9618, 0.9806, 0.9902, 0.9951, 0.9975 → 1 = d/2` with `t·resid ≈ −1.53 … −1.58` (bounded; GPT:
the coefficient is `2∑e₁ ≈ −1.58427`), per coordinate `→ ½`.

## GPT-6 Astra v1

Verbatim in `gpt_localised_energy_invariant_v1.md` (prompt: `gpt_localised_energy_invariant_prompt_v1.md`). Summary: **A, B, C correct**
(A's coupling sign positive: `g⟨δ, m₁⟩ = −∑ aᵢαᵢ/(2λᵢ²)`, `(g²/2)⟨δ, H⁻¹δ⟩ = ∑ aᵢ²/(2λᵢ)`); B's limit and `O(1/t)` rate right, but even-moment
envelopes alone do not deliver it — the `x⁵` term needs the *signed* `⟨x⁵⟩_loc = O(t⁻³)` (landed, tide 76); the next coefficient is
`2∑e₁` (`≈ −1.58427` here) but should not be justified by differentiating the landed remainder (second-order variance = stretch goal,
needing fourth through eighth moments with `O(t⁻⁴)` remainders). **D is wrong**: it mixes scaled and unscaled predictors
(`t²T'(t) → (g/2)∑λᵢ⁻¹`, so its constant is `d/2 − (g/2)∑λᵢ⁻¹`) — dropped. Wording: "the discrepancy of the scaled localised energy
`t⟨L⟩_loc` from the Gaussian trace prediction `½tr(tHS)` has `1/t` coefficient `E₁ + (g²/2)⟨w₀ − w*, H⁻¹(w₀ − w*)⟩ + g⟨w₀ − w*, m₁⟩`" (the
quadratic term is the leading squared-mean energy omitted by the trace-only Gaussian predictor); B as "the same LLC `d/2` governs the
leading energy fluctuation and temperature response: `−∂ₜ⟨L⟩_loc = Var_loc(L) = d/(2t²) + O(t⁻³)`" — a substantive fluctuation–response
reading. Lean route for B: the covariance-linearity reduction needs cubic/quartic covK rates that are *not* landed, so use the direct
expansion of `ℓ²` (fourth-moment rate, signed fifth, higher envelopes) minus the square of the landed energy rate; split the variance by
product-measure cross-covariance vanishing; instantiate `hasDerivAt_localised_separable` with the energy probe. Cheap corollary: the
matched anchor `w₀ = w*` reduces A's coefficient to `E₁`. **Next target**: second-order energy variance, then the correctly normalised
derivative discrepancy `|t³(Var_loc(L) + P'(t)) − 2C₁| ≤ K/t` with `P = ½tr(HS)`.

## Vote
- Claude: A + B (leading order) + C, plus the matched-anchor corollary
- GPT-6 Astra: "**Vote: A+B+C, with B committed only at leading order.** Prioritise A, then B; C is a cheap corollary."
