# Tide `localised-mean-1d` (laplace seabed, local): candidates for GPT-6 Astra

## Context

The note's eq:mean reads `⟨w⟩ − w* = −½ S (tT:S) + γ S (w₀ − w*) + O(S²)` with `S = (tH + γI)⁻¹`; E3 tests the localisation term.
The seabed certifies the `γ S (w₀ − w*)` term only for Gaussian targets (`localised-bias`, exact) and the reviewer summary lists
"eq:mean's localisation term for the anharmonic localised measure has not been analysed" as an open caveat. In one dimension the
seabed has, for `ℓ(x) = λx²/2 + αx³/6 + γx⁴/24` (`λ, γ > 0`, `α² < 3λγ`, `ℓ ≥ 0`): the moments with rates
(`|t⟨x⟩ + α/(2λ²)| ≤ K/t`, `|t⟨x²⟩ − 1/λ| ≤ K/t`, `|t²⟨x⁴⟩ − 3/λ²| ≤ K/t`, sixth moment `t³⟨x⁶⟩ → 15/λ³`), integrability of
polynomials against `e^{−tℓ}`, and the positivity of `Z(t)`. Write `g` for the localisation strength (the note's `γ`, to avoid the
quartic coefficient `γ`) and `x₀` for the anchor.

The localised measure is `e^{−tℓ(x) − (g/2)(x − x₀)²}`, and its mean is a ratio of anharmonic Gibbs expectations of the bounded
weight `φ(x) = e^{g x₀ x − (g/2)x²}` (the constant `e^{−g x₀²/2}` cancels): `⟨x⟩_loc = ⟨xφ⟩_t / ⟨φ⟩_t`, `0 < φ ≤ e^{g x₀²/2}`.
Numerically (`numcheck_localised_mean.py`, `λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`): `⟨x⟩_loc − [−αt/(2(tλ+g)²) + g x₀/(tλ+g)]
= 0.047/t²` and `⟨x⟩_loc − [−α/(2λ²t) + g x₀/(λt)] = O(t⁻²)` as well.

## Candidates

**A. The weight's expansion.** With `y = g x₀ x − (g/2)x²`, `|e^y − 1 − y| ≤ y² e^{max(y,0)}/2 ≤ C(x² + x⁴)` (`y ≤ g x₀²/2`, so
`e^{max(y,0)}` is bounded), hence `|φ(x) − 1 − g x₀ x| ≤ C₁ x² + C₂ x⁴` for all `x` with explicit `C₁, C₂` (absorbing the `(g/2)x²`
of `y`). Lean: Mathlib's `Real.abs_exp_sub_one_sub_id_le` is for `|y| ≤ 1`; for `y ≤ 0` use `Real.exp_bound'`/convexity
(`e^y ≥ 1 + y` and `e^y ≤ 1 + y + y²/2` for `y ≤ 0`), for `0 ≤ y ≤ g x₀²/2` the bounded-derivative Taylor estimate.

**B. The moment inputs.** `⟨x φ⟩ = ⟨x⟩ + g x₀ ⟨x²⟩ + R₁`, `|R₁| ≤ C₁⟨|x|³⟩ + C₂⟨|x|⁵⟩`, and `⟨φ⟩ = 1 + g x₀⟨x⟩ + R₀`, `|R₀| ≤ C₁⟨x²⟩ +
C₂⟨x⁴⟩`. Odd absolute moments via Young with a `t`-dependent weight: `|x|³ ≤ (ε x² + x⁴/ε)/2` with `ε = t^{−1/2}` gives
`⟨|x|³⟩ ≤ K t^{−3/2}`, similarly `|x|⁵ ≤ (ε x⁴ + x⁶/ε)/2` gives `K t^{−5/2}`. So `R₁ = O(t^{−3/2})`, `R₀ = O(1/t)`.

**C. The theorem.** `localised_mean_anharmonic_rate`: `∃ K T, ∀ t ≥ T, |t ⟨x⟩_loc − (−α/(2λ²) + g x₀/λ)| ≤ K/√t`, i.e. eq:mean's
localisation term `g S (x₀ − x*)` at leading order (`S ≈ 1/(λt)`) for the exact anharmonic localised measure, with a `t^{−1/2}`
relative remainder (the true remainder is `O(1/t)` relative, by parity; not attempted here). Also the identity
`⟨x⟩_loc = ⟨xφ⟩/⟨φ⟩` and integrability of `xᵏ φ e^{−tℓ}` from `φ ≤ e^{g x₀²/2}`.

## Questions

1. Is this the right first step on the anharmonic localised measure, or is there a cleaner route (e.g. treating
   `tℓ + (g/2)(x − x₀)²` as an anharmonic potential with `t`-dependent coefficients and shifted minimum, and reusing the existing
   theorems — problematic because the existing rates' constants depend on the coefficients; or a `g`-derivative argument
   `d/dg ⟨x⟩_loc = −½ Cov_loc[x, (x − x₀)²]` integrated from `g = 0`)?
2. For A: the cleanest global bound on `|e^y − 1 − y|` in Lean for `y` bounded above (not below), and whether to bound
   `|φ − 1 − g x₀ x|` by `C(x² + x⁴)` or by `C x²(1 + x²)`.
3. For B: is the `ε = t^{−1/2}` Young trick the right way to get `⟨|x|³⟩ = O(t^{−3/2})` from even moments in the seabed (which has
   only signed moments), or does the seabed's `abs_moment_scaling`/rescaling machinery give absolute moments directly?
4. Which form of C is most useful to the note (E3 is Gaussian; the anharmonic localised case is not an experiment in the note but
   the formula is stated generally), and the vote (A+B+C)?
