# Tide 67 consult: eq:mean's O(S²) remainder on the exact localised anharmonic measure

One-round consult on a Lean 4 / Mathlib formalisation step in the `laplace` seabed (Laplace/Hessian-route formulas of a note on
SGLD sanity checks). Available (real theorem names):

- 1D anharmonic `ℓ = λx²/2 + αx³/6 + γx⁴/24`, `λ, γ > 0`, `α² < 3λγ`, Gibbs measure `e^{−tℓ}`; rates: `mean_anharmonic_O2_rate`
  (`|t⟨x⟩ + α/(2λ²)| ≤ K/t`), `evenMoment_anharmonic_rate k` (`|tᵏ⟨x^{2k}⟩ − (2k−1)‼/λᵏ| ≤ K/t`), `oddMoment_anharmonic_rate k`
  (`|t^{k+1}⟨x^{2k+1}⟩ + α(2k+3)‼/(6λ^{k+2})| ≤ K/t`), `secondMoment_anharmonic_order2_rate` (second moment to `t⁻²` with closed
  coefficient). No second-order *mean* coefficient in the seabed.
- Tide 65 (`Laplace/Multi/LocalisedAnharmonic.lean`): localised weight `φ = e^{g x₀ x − (g/2)x²} ≤ e^{g x₀²/2}`,
  `|φ − 1 − g x₀ x| ≤ C₁x² + C₂x⁴`, `⟨x⟩_loc = ⟨xφ⟩/⟨φ⟩`, `|⟨φ⟩ − 1| ≤ K/t` (`locDenominator_rate`), `|t⟨x⟩_loc − c| ≤ K/√t`
  (`localisedMean_anharmonic_rate`, `c = −α/(2λ²) + g x₀/λ`), `locLeading = P_t = −αt/(2(tλ+g)²) + g x₀/(tλ+g)`,
  `|P_t − c/t| ≤ K/t²` (`locLeading_sub_le`), `|⟨x⟩_loc − P_t| ≤ K/(t√t)`.
- Tide 66 (`Laplace/Multi/LocalisedAnharmonicMulti.lean`): E2's rotated oscillator with isotropic localiser is separable in the
  eigenframe; `⟨wⱼ⟩_loc = cⱼ + ∑ᵢ Qⱼᵢ localisedMean(λᵢ, αᵢ, γᵢ, g, aᵢ, t)` (`a = Qᵀ(w₀ − c)`), the displayed right-hand side
  `meanShiftLoc + g(tH + gI)⁻¹(w₀ − c) = Q (P_{t,i})ᵢ` (`displayed_mean_rot`), `sum_rate_div_sqrt`, and the `K/(t√t)` theorem
  `localisedRotatedAnharmonic_displayed_rate`.
- Mathlib: `Real.exp_bound (hx : |x| ≤ 1) (hn : 0 < n) : |exp x − ∑_{m<n} x^m/m!| ≤ |x|^n · (n+1)/(n!·n)`.

## Candidates (Claude, v1) and numerical check

## Candidates v1 (Claude)

Setting as in tides 65–66: `ℓ = λx²/2 + αx³/6 + γx⁴/24` (`λ, γ > 0`, `α² < 3λγ`), localiser strength `g ≥ 0`, anchor `x₀`, weight
`φ(x) = e^{y}`, `y = g x₀ x − (g/2)x²`, `c = −α/(2λ²) + g x₀/λ`, `P_t = −αt/(2(tλ + g)²) + g x₀/(tλ + g)` (`locLeading`). Tide 65 gave
`|t⟨x⟩_loc − c| ≤ K/√t` and `|⟨x⟩_loc − P_t| ≤ K/(t√t)` because the first-order expansion of `φ` left odd absolute moments, bounded
through even ones by a `t`-dependent Young inequality at the cost of a half power.

- **A (1D, sharp).** `|t⟨x⟩_loc − c| ≤ K/t` and hence `|⟨x⟩_loc − P_t| ≤ K/t²` — eq:mean's `O(S²)` remainder for the exact
  localised anharmonic measure in one dimension (`S = 1/(tλ + g) = O(1/t)`).
  Route: `|e^y − 1 − y − y²/2| ≤ (e^M + 3)|y|³` for `y ≤ M` (`Real.exp_bound` at `n = 3` gives `(2/9)|y|³` on `|y| ≤ 1`; for
  `|y| > 1` each of `e^y, 1, |y|, y²/2` is `≤ (const)·|y|³`). With `y²/2 = (g²x₀²/2)x² − (g²x₀/2)x³ + (g²/8)x⁴`,
  `xφ = x + g x₀ x² + c₂ x³ + R(x)`, `c₂ = (g²x₀² − g)/2`, `R = x(φ − 1 − y − y²/2) − (g²x₀/2)x⁴ + (g²/8)x⁵`, and
  `|y|³ ≤ 4(|g x₀|³|x|³ + (g/2)³x⁶)` gives `|R| ≤ A x⁴ + B x⁶ + C x⁸` (odd absolute powers `|x|⁵ ≤ (x⁴ + x⁶)/2`,
  `|x|⁷ ≤ (x⁶ + x⁸)/2` — no `t`-dependence needed). So `⟨R⟩ = O(1/t²)` by the even-moment rates, `t⟨x³⟩ = O(1/t)` by the seabed's
  signed `oddMoment_anharmonic_rate` (`t²⟨x³⟩ → −5α/(2λ³)`), and `t⟨xφ⟩ = t⟨x⟩ + g x₀ t⟨x²⟩ + O(1/t) = c + O(1/t)`. The denominator
  already has `|⟨φ⟩ − 1| ≤ K/t` (`locDenominator_rate`), and the ratio bookkeeping of tide 65 goes through with `1/t` in place of
  `1/√t`. Against `P_t`: `|⟨x⟩_loc − c/t| ≤ K/t²` and `|P_t − c/t| ≤ K/t²` (`locLeading_sub_le`).
- **B (E2, `d` dimensions, sharp).** For every ambient coordinate of E2's rotated oscillator with the isotropic localiser,
  `|(⟨w⟩_loc − c − meanShiftLoc t g H T − g (tH + gI)⁻¹(w₀ − c))ⱼ| ≤ K/t²` — eq:mean's displayed right-hand side *with its `O(S²)`
  remainder* on the exact localised measure. Route: tide 66's exact reduction `⟨wⱼ⟩_loc − cⱼ = ∑ᵢ Qⱼᵢ localisedMean(λᵢ, αᵢ, γᵢ, g, aᵢ, t)`
  and `displayed_mean_rot`, with A coordinatewise and a `1/t²` version of `sum_rate_div_sqrt`. Also the frame version
  `|t⟨(Qᵀ(w − c))ᵢ⟩_loc − vᵢ| ≤ K/t`.
- **C (optional).** The second-order coefficient itself, `t⟨x⟩_loc = c + c'/t + O(1/t²)` with `c'` in closed form: needs the
  second-order mean and second-moment coefficients (`mean` at order 2 is not in the seabed; the second moment is,
  `secondMoment_anharmonic_order2_rate`) — deferred unless GPT sees a short route.

Rationale: closes the one gap GPT named in tides 65 and 66 ("does not certify the `O(S²)` remainder"), with the same
infrastructure; the only new analysis is the cubic Taylor bound and the parity-free remainder control.

## Numerical check

`numcheck_localised_mean_sharp.py` (`λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`): `t(t⟨x⟩_loc − c) = 0.046, 0.067, 0.073, 0.075,
0.075` and `t²(⟨x⟩_loc − P_t) = 0.027, 0.041, 0.046, 0.047, 0.047` at `t = 10, 40, 160, 640, 2560` — both converge, so
`|t⟨x⟩_loc − c| = O(1/t)` and `|⟨x⟩_loc − P_t| = O(1/t²)` as claimed (tide 66's `d = 2` check gave `t²·|error| → 0.92` for B).

## Questions

1. Are A and B correct as stated, including the algebra `xφ − x − g x₀ x² − ((g²x₀² − g)/2)x³ = x(φ − 1 − y − y²/2) − (g²x₀/2)x⁴ +
   (g²/8)x⁵` and the claim that the remainder is controlled by *even* moments only (so the rate is a full `1/t`, no parity loss)?
   Is the third-moment input right: `oddMoment_anharmonic_rate` at `k = 1` gives `t²⟨x³⟩ → −5‼α/(6λ³) = −5α/(2λ³)`, hence
   `|t⟨x³⟩| ≤ M/t`?
2. Does B really certify the note's `O(S²)` claim for eq:mean on this family (with `S = (tH + gI)⁻¹ = O(1/t)`, `O(S²) = O(1/t²)`)?
   Any caveat in how to word it (e.g. constants depend on `g, w₀, Q`; not uniform; only E2's separable-in-a-frame family)?
3. Is C (the closed-form second-order coefficient `c'` of `t⟨x⟩_loc`) reachable cheaply from the existing second-order second
   moment plus something short, or does it need a second-order mean expansion that is not in the seabed? If the latter, defer.
4. Any better/cleaner route (e.g. an exact integration-by-parts identity `λ⟨x⟩ + (α/2)⟨x²⟩ + (γ/6)⟨x³⟩ = 0` for the unlocalised
   measure to replace `oddMoment_anharmonic_rate`)? Vote on the bundle.
