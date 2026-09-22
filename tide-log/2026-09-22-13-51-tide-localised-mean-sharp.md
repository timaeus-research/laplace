# Tide: localised-mean-sharp

**Direction (user):** auto mode ("Continue with what you think best"); chosen direction: eq:mean's `O(S²)` remainder on the exact localised anharmonic measure — expand the localised weight to second order, control the remainder by even moments and the signed third-moment rate, sharpen the 1D localised mean to `|t⟨x⟩_loc − c| ≤ K/t` and `|⟨x⟩_loc − P_t| ≤ K/t²`, and transfer to E2's `d`-dimensional localised measure against the displayed right-hand side with `S = (tH + gI)⁻¹`.
**Seabed:** laplace, commit b9d26cd (branch `tide/localised-mean-sharp` off `main`)
**Started:** 2026-09-22T13:51Z

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

## GPT-6 Astra v1

Verbatim in `gpt_localised_mean_sharp_v1.md` (prompt `gpt_localised_mean_sharp_prompt_v1.md`). Summary: A and B correct — the
algebra `xφ − x − ax² − bx³ = x(φ − 1 − y − y²/2) − (g²x₀/2)x⁴ + (g²/8)x⁵` (`a = g x₀`, `b = (a² − g)/2`), the global bound
`|e^y − 1 − y − y²/2| ≤ (e^M + 3)|y|³`, the even-power remainder `A₄x⁴ + A₆x⁶ + A₈x⁸` (`A₄ = 4D|a|³ + g²|x₀|/2 + g²/16`,
`A₆ = Dg³/4 + g²/16`, `A₈ = Dg³/4`, `D = e^M + 3`), and the third-moment input `t²⟨x³⟩ → −5‼α/(6λ³) = −5α/(2λ³)`; "keeping this
term *signed* until after integration is the essential improvement". B follows from tide 66's exact reduction with
`Kⱼ = ∑ᵢ|Qⱼᵢ|Kᵢ`. Wording for the `O(S²)` claim: for fixed parameters the exact localised mean differs from the displayed expression
by `O(t⁻²)` coordinatewise, and since `‖S_t‖_op = 1/(tλ_min(H) + g) = Θ(1/t)` this *is* an `O(‖S_t‖²)` remainder — `S_t = O(1/t)`
alone would not give the equivalence; constants depend on `g, w₀, Q, d`; not uniform; separable-in-a-frame family only. C (the
second-order coefficient `c'`) has a short analytical bridge — the integration-by-parts identity
`λ⟨x⟩ + (α/2)⟨x²⟩ + (γ/6)⟨x³⟩ = 0` gives the second-order mean `B₁ = −5α³/(8λ⁵) + 2αγ/(3λ⁴)` from the second-moment coefficient
`B₂ = 5α²/(4λ⁴) − γ/(2λ³)`, and `c' = B₁ + aα²/λ⁴ − aγ/(2λ³) + αg/λ³ − αa²/(2λ³) − ag/λ²` — but the `O(t⁻²)` remainder of
`t⟨x⟩_loc` would need a degree-five expansion, the signed fifth moment, `Z = 1 + d₁/t + O(t⁻²)` and another order of ratio
bookkeeping: defer, record as follow-up.

## Vote
- Claude: A + B
- GPT-6 Astra: A + B (defer C; record the integration-by-parts bridge and `c'` as a follow-up)
