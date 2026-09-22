You are consulted (one round) on tide 87 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders. Your tide-85 and tide-86 consults named the second-order energy variance as the next substantial
target, "requiring the missing second-order fifth/sixth moments". Tide 86 landed the signed `|t⁴m₇| ≤ K` and `|t⁴m₈| ≤ K` bounds; with the
Stein–covariance reduction the second-order variance needs NO second-order fifth/sixth moments — only leading rates and these bounds.

## Candidates v1 (Claude)

Setting (E2, as in tides 68–86): the exact localised measure per frame coordinate (`ℓ = λx²/2 + αx³/6 + γx⁴/24`, anchor `a = g u₀`);
`e₁ = energyLocCoeff1 = (a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)` (tide 73), `c₂' = locSecondCoeff2` (`t m₂ = 1/λ + c₂'/t + …`),
`c₃ = locThirdCoeff`, `c₅ = locFifthCoeff`. Landed: the localised Stein–covariance reduction (tide 77)
`t²Cov[ℓ, xⁿ] = (n/2) t mₙ − (α/12) t²Cov[x³, xⁿ] − (γ/24) t²Cov[x⁴, xⁿ] − (g/2) t Cov[x², xⁿ] + (a/2) t Cov[x, xⁿ]`;
`t²Cov[ℓ, x²] = 1/λ + 2c₂'/t + O(t⁻²)` (tide 78); the moment rates `t m₁, t m₂` (second order), `t²m₃, t²m₄, t³m₅, t³m₆` (leading, `O(1/t)`
remainders), and tide 86's `|t⁴m₇| ≤ K`, `|t⁴m₈| ≤ K`; tide 85's exact `−∂ₜ⟨L∘A⟩_loc = Var_loc(L∘A) = ∑ᵢ Var_loc,ᵢ(ℓᵢ)`.

**A. The second-order localised energy variance (1D).** `Var_loc(ℓ) = Cov[ℓ, ℓ] = (λ/2)Cov[ℓ,x²] + (α/6)Cov[ℓ,x³] + (γ/24)Cov[ℓ,x⁴]`
(bilinearity), and by the reduction with `n = 3, 4` and the landed rates:
`t²Cov[ℓ, x³] = C₃'/t + O(t⁻²)`, `C₃' = (3/2)c₃ − 5α/(4λ³) + 3a/(2λ²) = −5α/λ³ + 6a/λ²` (the terms `t²Cov[x⁴,x³]`, `t Cov[x²,x³]` are
`O(t⁻²)` because `t⁴m₇`, `t³m₅` are bounded); `t²Cov[ℓ, x⁴] = 6/(λ² t) + O(t⁻²)` (all other terms `O(t⁻²)`, using `|t⁴m₈| ≤ K`). Hence
**`|t² Var_loc(ℓ) − ½ − 2e₁/t| ≤ K/t²`**: the `1/t` coefficient is exactly `2e₁` (`λc₂' + (α/6)C₃' + γ/(4λ²) = 2e₁`, checked
symbolically), i.e. the variance's second-order term is the derivative reading of the energy's first correction.

**B. On E2.** `|t² Var_loc(L∘A) − d/2 − 2(∑ᵢ e₁ᵢ)/t| ≤ K/t²`, equivalently **`−∂ₜ⟨L∘A⟩_loc = d/(2t²) + 2(∑ᵢe₁ᵢ)/t³ + O(t⁻⁴)`** — the
coefficientwise derivative of tide 73's `t⟨L∘A⟩_loc = d/2 + ∑e₁/t + O(t⁻²)`, established from moments (a consistency check with the
formal derivative, not obtained from it).

**C. The correctly normalised derivative discrepancy from the Gaussian trace prediction** (GPT's tide-85 target). With
`P(t) = ½ tr(H S(t)) = ½∑ᵢ λᵢ/(tλᵢ + g)`, exactly `P'(t) = −½∑ᵢ λᵢ²/(tλᵢ + g)²`, and per coordinate
`|½λ²t³/(tλ + g)² − t/2 + g/λ| = g²(3λt + 2g)/(2λ(tλ + g)²) ≤ g²(3λ + 2g)/(2λ³t)`; hence
**`|t³ (Var_loc(L∘A) + P'(t)) − 2C₁| ≤ K/t`**, `C₁ = ∑ᵢ (e₁ᵢ + g/(2λᵢ))` — twice tide 85's invariant trace-discrepancy coefficient, recovered
from genuine fluctuation estimates. (`−∂ₜ(⟨L⟩_loc − P) = 2C₁/t³ + O(t⁻⁴)`, the derivative reading of `t(⟨L⟩ − P) = C₁/t + O(t⁻²)`.)

Sizing: A ~350 lines (bilinearity of the 1D covariance in the second slot with the polynomial probe, the two reductions with ~10 moment
products each to `O(t⁻²)`, assembly, the coefficient identity), B ~60, C ~120 (`HasDerivAt` of the trace prediction through
`hasDerivAt_locS_entry`/`trace_mul_conj_diagonal`, the rational coordinate bound, assembly). Target A + B + C.

## Numerical / symbolic check (done; two frame coordinates, λ = (1.3, .9), α = (.7, −.4), γ = (1.1, .8), g = .8, u₀ = (.55, −.35))
2 e1 = [-0.7185022  -1.09551349]   C3' = [-0.0309513   0.66941015]   6/lam^2 = [3.55029586 7.40740741]
t=   80: t(t^2 Var - 1/2) = -0.70429, -1.06466   t^3 Cov(ell,x^3) = 0.00457, 0.54676   t^3 Cov(ell,x^4) = 3.43001, 7.03874
t=  160: t(t^2 Var - 1/2) = -0.71135, -1.07991   t^3 Cov(ell,x^3) = -0.01269, 0.60573   t^3 Cov(ell,x^4) = 3.48954, 7.21999
t=  320: t(t^2 Var - 1/2) = -0.71491, -1.08767   t^3 Cov(ell,x^3) = -0.02169, 0.63695   t^3 Cov(ell,x^4) = 3.51977, 7.31293
t=  640: t(t^2 Var - 1/2) = -0.71670, -1.09158   t^3 Cov(ell,x^3) = -0.02629, 0.65303   t^3 Cov(ell,x^4) = 3.53499, 7.35997
t= 1280: t(t^2 Var - 1/2) = -0.71760, -1.09354   t^3 Cov(ell,x^3) = -0.02861, 0.66118   t^3 Cov(ell,x^4) = 3.54264, 7.38364
2 C1 = -0.309742
t=   80: t^3 (Var_loc(L) + P'(t)) = -0.286312
t=  160: t^3 (Var_loc(L) + P'(t)) = -0.297869
t=  320: t^3 (Var_loc(L) + P'(t)) = -0.303767
t=  640: t^3 (Var_loc(L) + P'(t)) = -0.306745
symbolic v2 - 2 e1 = 0
(`t(t²Var − ½) → 2e₁` per coordinate, `t³Cov[ℓ,x³] → C₃'`, `t³Cov[ℓ,x⁴] → 6/λ²`, `t³(Var + P') → 2C₁`; the identity
`λc₂' + (α/6)C₃' + γ/(4λ²) = 2e₁` is exact in sympy.)

## Questions
1. Are A, B, C correct as stated? Check the bookkeeping of the `n = 3` and `n = 4` reductions: which products contribute at `1/t` and
   which are `O(t⁻²)` given the landed rates (`t m₁, t m₂` second order; `t²m₃, t²m₄, t³m₅, t³m₆` leading with `O(1/t)` remainders;
   `t⁴m₇, t⁴m₈` bounded). Any term I have misjudged?
2. Is the identity `λc₂' + (α/6)C₃' + γ/(4λ²) = 2e₁` the expected "derivative reading" (the `1/t` coefficient of `t²Var` is twice the `1/t`
   coefficient of `t⟨ℓ⟩`), and is it worth stating as such against the note (E3, the LLC)? Wording for B and C?
3. Lean route: prove the two reductions' second-order rates as separate 1D lemmas (`|t²Cov[ℓ,x³] − C₃'/t| ≤ K/t²`, `|t²Cov[ℓ,x⁴] − 6/(λ²t)| ≤
   K/t²`) using a small "bounded × O(1/t)" product lemma and the landed `prod_rate`/`order2_to_order1`; bilinearity via the 1D
   `gibbsCov_add_right`/`gibbsCov_smul_right` with `integrable_pow_locPotential1`; for C, `HasDerivAt` of `½∑λᵢ/(sλᵢ + g)` and the exact rational
   coordinate identity. Pitfalls?
4. Better or additional candidates, and the best next target after this tide (e.g. the second-order third cumulant `t³κ₃ = 1 + κ₃'/t`, which
   would need `t⁴m₇`'s limit and second-order `m₆`; or the fourth cumulant at leading order; or moving to the sampler side)?
Vote: which bundle (A, A+B, A+B+C) should this tide commit to? Be concrete and terse; flag any error explicitly.
