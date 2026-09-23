# Tide: localised-laplace-gaussian-gap

**Direction (user):** auto mode — "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." / "Continue with what you think best, don't stop". Claude's choice for tide 93: close the E2/E3 loop at the transform level — the gap between the exact localised anharmonic transform (tide 90) and E3's Gaussian prediction (tide 91) is governed by the invariant coefficient C₁ of tides 85/87.
**Seabed:** laplace, commit c26a4c9 (tide 92 landed)
**Started:** 2026-09-23T01:58Z

## Candidates v1 (Claude)

**A. The Gaussian (E3) prediction's own finite-temperature correction.** For fixed `s > −1`, `g ≥ 0`, `λᵢ > 0`:
`√((tλ + g)/((1+s)tλ + g)) = (1+s)^{−1/2}·√(1 + g/(tλ))/√(1 + g/((1+s)tλ))` and, with `|√(1+x) − 1 − x/2| ≤ x²/2` for `|x| ≤ ½`
(elementary: `1 + x/2 − x²/2 ≤ √(1+x) ≤ 1 + x/2`), each square root is `1 + (g/(2λ))/u + O(u⁻²)` at `u = t` resp. `u = (1+s)t`; the quotient
(`ratio_rate_order2`) is `1 + (g s/(2λ(1+s)))/t + O(t⁻²)`; the finite product (`prod_one_rate2`) gives
**`|∏ᵢ√((tλᵢ + g)/((1+s)tλᵢ + g)) − (1+s)^{−d/2}(1 + s·g∑ᵢ1/(2λᵢ)/((1+s)t))| ≤ K/t²`** — the Gaussian localised transform has its own
`1/t` correction, `+s(g∑1/(2λᵢ))/((1+s)^{d/2+1}t)`, coming purely from the localiser (it vanishes at `g = 0`, where the Gaussian law is
exactly `Gamma(d/2, 1)`).

**B. The transform-level discrepancy is governed by `C₁`.** Combining A with tide 90:
**`|⟨e^{−st·L∘A}⟩_loc − ∏ᵢ√((tλᵢ + g)/((1+s)tλᵢ + g)) + s·C₁/((1+s)^{d/2+1}t)| ≤ K/t²`**, `C₁ = ∑ᵢ(e₁ᵢ + g/(2λᵢ))`: the exact anharmonic
localised law and E3's Gaussian prediction have the same Gamma(d/2, 1) limit and differ at order `1/t` by `−sC₁/(1+s)^{d/2+1}`; the *same*
`C₁` as in the energy (`⟨L⟩ − P = C₁/t`) and its derivative (`2C₁/t³`) discrepancies of tides 85/87. Since `−∂ₛ|₀` of the transform
difference is `t·(⟨L⟩ − P)`, the coefficient is consistent with tide 85 (a check, not a derivation). Stated pointwise in `s`.

**C. Remarks (prose, not Lean).** `C₁ = ∑e₁ᵢ + g∑1/(2λᵢ)`: the anharmonic part `∑e₁ᵢ` can have either sign, the localiser part `g∑1/(2λᵢ)` is
positive; the Gaussian prediction is "wrong" by exactly the anharmonic and anchor corrections `e₁ᵢ + g/(2λᵢ) = (a²/2λ − aα/(2λ²) −
γ/(8λ²) + 5α²/(24λ³))`, i.e. `e₀ + a²/(2λ) − aα/(2λ²)` with the unlocalised `e₀`; at the minimum anchor `a = 0` it is `∑e₀ᵢ`, independent of `g`.

## Numerical check (scipy quad, λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35); `C₁ = −0.15487`,
`∑e₁ = −0.90701`, `g∑1/(2λ) = 0.75214`)
`t(Λ − Λ^G)`: s = 1: 0.03617 → 0.03856 (t = 40 → 640) vs `−sC₁/(1+s)² = 0.03872`; s = −0.5: −0.259 → −0.306 vs −0.3097; s = 3: 0.0276 →
0.02895 vs 0.02904; `t(Λ^G − (1+s)^{−d/2})` → `s·g∑1/(2λ)/(1+s)^{d/2+1}` (s = 1: 0.18792 vs 0.18803); `t²`-remainders converge.

## Questions put to GPT-6 Astra
1. Are A and B correct (signs, the `(1+s)^{−d/2−1}` power, the two-sided `√(1+x)` bound and its validity range, the transfer of
   `|x| ≤ ½` to a threshold `t ≥ 2g/λ_min`)? Is `C₁ = ∑(e₁ᵢ + g/(2λᵢ))` exactly tides 85/87's coefficient (there `P = ½tr(H·locS)`,
   `locS = (tH + gI)⁻¹`, with `−∂ₜ⟨L⟩ + P' = 2C₁/t³`)?
2. Bundle and route: is the `√(1+x)` two-sided bound + `ratio_rate_order2` the cleanest way to get A's per-factor expansion with explicit
   constants, or is there a slicker route (e.g. `√((tλ+g)/((1+s)tλ+g))⁻² = ((1+s)tλ+g)/(tλ+g)` — work with the *squared* ratio which is
   rational, then a `√`-rate lemma `|√y − √y₀| ≤ |y − y₀|/(2√y_min)`)? A is pure real analysis on `∏`s of `λᵢ`; B is a `linarith`
   combination of A and `localisedLaplace_rate2` (both `(1+s)^{−d/2}(1 + c/t) + O(t⁻²)` forms).
3. Anything missed close to this seabed — e.g. is it worth stating the "three-coefficient" statement (energy discrepancy `C₁/t`,
   variance-derivative discrepancy `2C₁/t³`, transform discrepancy `−sC₁/((1+s)^{d/2+1}t)`) as one theorem/definition of `C₁`; is there an
   E3-side quantity in the note ("the LLC shrinks as ½ t tr(H(tH+γI)⁻¹)") whose *transform* version we should name?
4. Wording against E2/E3: "the exact localised law and the Gaussian prediction differ, at the transform level, by `−sC₁/((1+s)^{d/2+1}t)`;
   `C₁` is the invariant anharmonic-plus-anchor correction that also governs the energy and its temperature derivative" — fair?
   Qualifications (fixed `g, u₀`, pointwise in `s`, the Gaussian prediction as an explicit product not as a matrix expectation)?
Vote for one bundle at the end.

(The numerical check script is `numcheck_localised_laplace_gaussian_gap.py` in this directory; full output in the tide's SRI note.)

## GPT-6 Astra v1

Verbatim in `gpt_localised_laplace_gaussian_gap_v1.md`. Summary: A and B correct (signs, `(1+s)^{−d/2−1}`); two corrections adopted —
the *unscaled* energy gap is `⟨L⟩_loc − P = C₁/t²` (the `C₁/t` belongs to the scaled `t⟨L⟩ − tP`; consistent with `−∂ₜ⟨L⟩ + P' = 2C₁/t³`),
and the prediction is the *centred* Gaussian (the anchored Gaussian, mean `aᵢ/(tλᵢ+g)`, would shift `C₁` by `−∑aᵢ²/(2λᵢ)`). The
two-sided bound is valid but unnecessary: the exact identity `√(1+x) − 1 − x/2 = −x²/(2(√(1+x)+1)²)` holds for all `x ≥ −1`, so the
cleaner route is one rational perturbation `√((tλ+g)/((1+s)tλ+g)) = (1+s)^{−1/2}√(1 + z)`, `z = sg/((1+s)tλ+g)`, with
`|z − sg/((1+s)λt)| ≤ |s|g²/((1+s)²λ²t²)` and per-factor constant `g²(|s| + s²)/(2(1+s)^{5/2}λ²)` (no smallness threshold; my
two-root threshold `t ≥ 2g/λ_min` did not handle `−1 < s < 0`); then `prod_one_rate2`, then the prefactor. Shared-`C₁` corollary only as
lightweight packaging; name the object "localised Gaussian scaled-energy Laplace transform" (`−∂ₛ|₀ = tP`). Wording: "for fixed
localiser strength and anchor, and each fixed `s > −1`, the exact localised scaled-energy transform differs from the centred Gaussian
trace-based prediction by `−sC₁/((1+s)^{d/2+1}t) + O(t⁻²)`; the same invariant anharmonic-plus-anchor coefficient `C₁` governs the `t⁻²`
unscaled energy discrepancy and the `2C₁t⁻³` variance discrepancy"; constants depend on `s`; the localiser contribution is nonnegative
(`g = 0` allowed); at the minimum anchor `C₁ = ∑e₀ᵢ`.

## Vote
- Claude: A + B (single-perturbation route adopted; docstrings corrected to the scaled energy gap and the centred Gaussian)
- GPT-6 Astra: "bundle A+B, using the single-rational-perturbation square-root route, with an explicit centered-Gaussian
  qualification and corrected energy normalization"

Agreed: A + B.
