# Tide: localised-laplace-transform

**Direction (user):** auto mode — "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." / "Continue with what you think best, don't stop". Claude's choice for tide 89: the Laplace transform of the localised energy (the Gamma(d/2, t) law of tK as a transform statement), after the cumulant tides 85–88 and GPT's remark that four cumulants do not identify a law.
**Seabed:** laplace, commit 85317e6 (tide 88 landed)
**Started:** 2026-09-22T23:28Z

## Candidates v1 (Claude)

Setting (E2, tides 68–88): per frame coordinate the localised measure has density `exp(−tℓ(x) − g(x − x₀)²/2)` with
`ℓ = λx²/2 + αx³/6 + γx⁴/24`, `λ > 0`, `γ > 0`, `α² < 3λγ`, `g ≥ 0`; in Lean it is the Gibbs measure of the t-dependent potential
`locPotential1(t) = ℓ + (g/(2t))(x − x₀)²` at temperature t, so `t·locPotential1(t)(x) = tℓ(x) + g(x − x₀)²/2` is the fixed localiser
form. On E2 the product over frame coordinates `uᵢ = (Qᵀ(w − c))ᵢ` of a rotated separable quartic `L∘A = ∑ᵢℓᵢ(uᵢ)` with the isotropic
localiser `g|w − w₀|²/2` (Lean: `localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t`, equal to the rotation of the separable family
`locFamily`). Landed: `Z_loc(u) := ∫ exp(−u·locPotential1(u)) = Z(u)·D(u)` with `D(u) = ⟨φ⟩_u` the unlocalised expectation of the
localiser weight `φ = exp(gx₀x − gx²/2)` (`|D(u) − 1| ≤ K/u`, `locDenominator_rate`); the unlocalised `Z(u) = J₀(u)/√(λu)` with
`|J₀(u) − √(2π)| ≤ K/u` for `u ≥ 1` (`J0_delta_order1`, `I_n_J_n_relation`); rotation and separable-product identities for partition
functions (`partitionFunction_rotated`, `partitionFunction_separable`); the quotient rate lemma `ratio_rate` (`|a/b − a₀/L| ≤ … /t` given
`L/2 ≤ b` and rates for `a`, `b`) and `prod_rate`.

**A. The Laplace transform of the localised energy (1D), exactly and asymptotically.** For `s > −1` define
`Λ_t(s) := ⟨exp(−s·t·ℓ)⟩_loc(t)`. Exactly **`Λ_t(s) = Z_loc((1+s)t)/Z_loc(t)`** (integrand identity
`e^{−stℓ}·e^{−t·locPotential1(t)} = e^{−(1+s)t·locPotential1((1+s)t)}`), hence
`Λ_t(s) = (1+s)^{−1/2} · [J₀((1+s)t)/J₀(t)] · [D((1+s)t)/D(t)]` and **`|Λ_t(s) − (1+s)^{−1/2}| ≤ K_s/t`** eventually
(`t ≥ T_s`, thresholds `≥ max(1, 1/(1+s))·T`), with `K_s` explicit from the two `ratio_rate` applications. This is the Laplace transform
of `tℓ` converging to that of `Gamma(½, 1)`, `(1+s)^{−1/2}`, on the whole domain `s > −1` of the Gamma MGF, with an `O(1/t)` rate.

**B. On E2.** `⟨exp(−s·t·L∘A)⟩_loc(t) = Z_locRot((1+s)t)/Z_locRot(t)` (same integrand identity in `d` dimensions, the localiser
`t·localiser(t) = g|w − w₀|²/2` fixed), `Z_locRot(u) = ∏ᵢ Z_loc,ᵢ(u)` (rotation + separable product), hence
**`⟨exp(−s·t·L∘A)⟩_loc = ∏ᵢ Λ_{t,i}(s)`** exactly and **`|⟨exp(−s·t·L∘A)⟩_loc − (1+s)^{−d/2}| ≤ K_s/t`**, via a finite-product rate lemma
(`|∏ᵢRᵢ − 1| ≤ 2^{d}(∑ᵢKᵢ)/t` when `|Rᵢ − 1| ≤ Kᵢ/t ≤ 1`). The Laplace transform of `t·(L∘A)` under the localised measure converges to
that of `Gamma(d/2, 1)`: the "Gamma law of tK" of the note's §14, now as a transform statement with a rate (weak convergence follows by the
continuity theorem for Laplace transforms on `s ≥ 0`, which we would state in prose, not in Lean).

**C. Consistency with the cumulant tides.** `−∂ₛ log Λ_t(s)|₀ = t⟨ℓ⟩`, `∂ₛ² log Λ|₀ = t²Var`, … — the cumulant hierarchy of tides
85–88 is the Taylor expansion of `log Λ_t` at `s = 0`, and `log(1+s)^{−1/2} = −½∑(−1)^{n+1}sⁿ/n` reproduces `κₙ → (n−1)!/2`. We would
*not* formalise C (differentiating in `s` under the integral is a new infrastructure piece); it is a remark. Instead, an optional **C'**:
the transform identity at `s = −1/2` … no — optional C'': monotonicity/positivity facts `0 < Λ_t(s) ≤ 1` for `s ≥ 0` (trivial) and the exact
scaling `Λ_t(s) = Z_loc((1+s)t)/Z_loc(t)` as a reusable lemma for any future "temperature-change" statement.

## Numerical check (scipy quad, λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35))
The ratio `Z_loc((1+s)t)/Z_loc(t)` equals the direct integral `⟨e^{−stℓ}⟩_loc` to all printed digits (s = 0.5, 1, 3); `t·(Λ_t(s) −
(1+s)^{−1/2})` converges to a constant (s = 1: 0.1248 → 0.1269 for t = 40 → 640; s = −0.5: −0.486 → −0.507; s = 3: 0.133 → 0.135), i.e.
the error is `Θ(1/t)` with a nonzero coefficient; the E2 product `∏Λᵢ` converges to `(1+s)^{−1}` with `t·(∏ − target)` → 0.2265 (s = 1).

## Questions put to GPT-6 Astra
1. Are A and B correct as stated — in particular the exact partition-ratio identity for the *t-dependent* localised potential (the
   localiser is fixed in the `t·locPotential1(t)` normalisation, so the temperature change `t → (1+s)t` keeps `g, x₀`), the domain `s > −1`,
   and the `O(1/t)` rate from `J₀` and `D` rates at `(1+s)t` and `t`? Is the first-order coefficient of `Λ_t(s) − (1+s)^{−1/2}` computable
   from the landed second-order data (`J₀(u) = √(2π)(1 + j₁/u + …)`, `D(u) = 1 + d₁/u + …`): `(1+s)^{−1/2}·(j₁ + d₁)(1/((1+s)t) − 1/t) =
   −(1+s)^{−1/2}(j₁ + d₁)·s/((1+s)t)`? (This would make the `1/t` coefficient explicit, if `j₁`, `d₁` are landed — `d₁` is tide 71's
   `locDenominator` coefficient; `j₁ = 15A²/2·… − 3B` from `J0_delta_order3`.) Worth including as **A2** if so.
2. Which bundle is the strongest reasonably reachable single tide (A+B, A+A2+B)? Any pitfalls with the finite-product rate lemma, or a
   Mathlib lemma that already does `|∏aᵢ − ∏bᵢ| ≤ …`?
3. Anything missed close to this seabed — e.g. is the characteristic function (imaginary `s`) or the full MGF domain worth more than the
   real Laplace transform; is there a cheap uniform-in-`s` statement on compacts `s ∈ [−1 + δ, S]` (the constants are explicit and
   monotone in `s`, so maybe)?
4. Wording against the note's §14 ("two regimes", Gamma law of `tK`): is "the Laplace transform of `t·(L∘A)` under the localised measure
   converges, for every `s > −1`, to the Gamma(d/2, 1) transform `(1+s)^{−d/2}` at rate `O(1/t)`; by the continuity theorem `t·(L∘A)
   ⇒ Gamma(d/2, 1)`" a fair gloss, and what qualifications (fixed `g, x₀`, parameters; localised measure, not the posterior; pointwise in
   `s`)?
Vote for one bundle at the end.

(The numerical check script is `numcheck_localised_laplace_transform.py` in this directory; full output in the tide's SRI note.)

## GPT-6 Astra v1

Verbatim in `gpt_localised_laplace_transform_v1.md` (prompt: `gpt_localised_laplace_transform_prompt_v1.md`). Summary: A and B correct for
fixed `s > −1`, `t > 0`; one normalisation correction — with `φ = exp(gx₀x − gx²/2)` the actual identity is
`Z_loc(u) = e^{−gx₀²/2} Z(u) D(u)` (the constant cancels in every temperature ratio; the landed Lean lemma `gibbsExpectation_locPotential1`
already carries `exp(−gx₀²/2)`); the numerator must use `locPotential1(at)` at temperature `at` (not `locPotential1(t)` at `at`); the
rates transfer as `|J₀(at) − √(2π)| ≤ (K_J/a)/t`, `|D(at) − 1| ≤ (K_D/a)/t`, thresholds `max(1, 1/a)·T`; `s > −1` is the open domain of the
limiting transform (at `s = −1` the finite-`t` transform is still finite when `g > 0`). A2 (first correction `−s c₁/(a^{3/2} t)`,
`c₁ = j₁ + d₁`, `j₁ = 5α²/(24λ³) − γ/(8λ²)`, `d₁ = (g²x₀² − g)/(2λ) − gx₀α/(2λ²)`) correct but deferred. Recommended order: exact 1D
temperature-change identity → normalised `R = √a·Λ`, `|R − 1| ≤ K/t` → exact rotated/separable factorisation → finite-product rate
(`2^d ∑K/t` safe) → `(a^{−1/2})^d`. Nearby: uniformity over all `s ≥ −1 + δ` for fixed `δ > 0` is cheap (`1/(at) ≤ 1/(δt)`,
`a^{−d/2} ≤ δ^{−d/2}`, `t ≥ max(1, 1/δ)T`); characteristic functions are not the cheap route; the cumulant remark must not suggest the
`O(1/t)` transform statement justifies differentiation. Wording: transform identity + quantitative transform convergence formalised,
weak convergence to `Γ(d/2, rate 1)` (for `d ≥ 1`) cited in prose via the continuity theorem; fixed parameters and localiser; the exact
localised Gibbs measure, not the posterior; the observable is the unlocalised energy `t(L∘A)`; this is the fixed-localiser large-`t` Gamma
regime, not a two-regime or crossover theorem.

## Vote
- Claude: A+B, with the uniform-in-`s ≥ −1 + δ` form as the main statement (pointwise `s > −1` as a corollary)
- GPT-6 Astra: A+B, "treat uniformity away from `s = −1` as an optional strengthening"

Agreed: A+B.
