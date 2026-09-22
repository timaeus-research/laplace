# Tide 71 consult: eq:covK to second order for the anharmonic oscillator

One-round consult on a Lean 4 / Mathlib formalisation step in the `laplace` seabed (Laplace/Hessian-route formulas of a note on
SGLD sanity checks; eq:covK: `Cov[K, ψ] ≈ ½tr(HSBS) + …`, E2 says the relative error is `∝ 1/t`). Real theorem names are given in
the candidates below; `cs = cubicScale = α/(6λ^{3/2})`, `qs = quarticScale = γ/(24λ²)`.

## Candidates v1 (Claude)

Setting: the 1D anharmonic Gibbs measure `e^{−tℓ}`, `ℓ = λx²/2 + αx³/6 + γx⁴/24`. Available: even moments to second order with a
`K/t²` remainder (`evenMoment_anharmonic_order2_rate k`: `|tᵏ⟨x^{2k}⟩ − (2k−1)‼/λᵏ − evenMomentCoeff k/(λᵏt)| ≤ K/t²`,
`evenMomentCoeff 2 = 450cs² − 96qs`), the second moment at order three, odd moments at leading order with rate
(`oddMoment_anharmonic_rate k`: `|t^{k+1}⟨x^{2k+1}⟩ + α(2k+3)‼/(6λ^{k+2})| ≤ K/t`), tide 70's mean to second order
(`mean_anharmonic_order2_rate`, `B₁ = −5α³/(8λ⁵) + 2αγ/(3λ⁴)`) and the Stein identity `k⟨x^{k−1}⟩ = t⟨x^kℓ'⟩` (`ibp_anharmonic`);
eq:covK at leading order with rate (`covK_sq_rate`, `covK_lin_rate`, `covK_anharmonic_rate`: `|t²Cov[ℓ, ψ] − C| ≤ K/t`), and the
decomposition `Cov[ℓ, ψ] = (λ/2)Cov[x², ψ] + (α/6)Cov[x³, ψ] + (γ/24)Cov[x⁴, ψ]` (`gibbsCov_anharmonic_left`).

- **A (the third moment to second order).** `|t²⟨x³⟩ + 5α/(2λ³) − B₃/t| ≤ K/t²` with `B₃ = −15α³/(2λ⁶) + 25αγ/(4λ⁵)`.
  Route: `ibp_anharmonic` at `k = 2`, `2⟨x⟩ = t(λ⟨x³⟩ + (α/2)⟨x⁴⟩ + (γ/6)⟨x⁵⟩)`, so
  `t²⟨x³⟩ = (2·t⟨x⟩ − (α/2)·t²⟨x⁴⟩ − (γ/6)·t²⟨x⁵⟩)/λ`; with `t⟨x⟩ = −α/(2λ²) + B₁/t + O(t⁻²)`, `t²⟨x⁴⟩ = 3/λ² + C₄'/t + O(t⁻²)`
  (`C₄' = 25α²/(2λ⁵) − 4γ/λ⁴` from `evenMomentCoeff 2`) and `t²⟨x⁵⟩ = (t³⟨x⁵⟩)/t = −35α/(2λ⁴t) + O(t⁻²)`:
  `B₃ = (2B₁ − (α/2)C₄' + (35αγ)/(12λ⁴))/λ`. The recursion turns the seabed's *even* second-order coefficients into *odd* ones.
- **B (eq:covK to second order, 1D).** `|t²Cov[ℓ, x²] − 1/λ − C'_sq/t| ≤ K/t²` with `C'_sq = 5α²/(2λ⁴) − γ/λ³`, and
  `|t²Cov[ℓ, x] + α/(2λ²) − C'_lin/t| ≤ K/t²` with `C'_lin = −5α³/(4λ⁵) + 4αγ/(3λ⁴)`; hence for the probe `ψ = (B/2)x² + bx`,
  `t²Cov[ℓ, ψ] = B/(2λ) − bα/(2λ²) + (B C'_sq/2 + b C'_lin)/t + O(t⁻²)`. Route: `gibbsCov_anharmonic_left` and `gibbsCov_pow_pow`,
  `gibbsCov_pow_id`, then each `t²(⟨x^{m+n}⟩ − ⟨x^m⟩⟨x^n⟩)` from the moment expansions (second-order inputs: `t⟨x²⟩`, `t²⟨x⁴⟩`,
  `t⟨x⟩`, `t²⟨x³⟩` (A); leading-order-with-rate inputs suffice for `t²⟨x⁵⟩`, `t²⟨x⁶⟩`, `t²⟨x³⟩⟨x²⟩`, `t²⟨x⁴⟩⟨x²⟩`, `t²⟨x⁴⟩⟨x⟩`).
- **C (E2).** The rotated-frame version for E2's oscillator through the seabed's `covK_rotatedAnharmonic_quadratic` route
  (tide 47) — `t²Cov[L∘A, ψ] = C_d + C'_d/t + O(t⁻²)` with `C'_d = ∑ᵢ ((QᵀBQ)ᵢᵢ C'_sq,i/2 + (Qᵀb)ᵢ C'_lin,i)` plus the off-diagonal
  pair terms, which contribute at `O(1/t)` relative (tide 54 bounded them by `(AⱼDᵢ + AᵢDⱼ)/t`; their coefficient would need the
  product of the mean and covK leading terms). Optional; the 1D statements are the content.

Rationale: completes the "second order" arc (two-loop energy §61, eq:mean second order §75) for the third of the note's four
Hessian-route formulas, eq:covK; the note's E2 says its relative error is `∝ 1/t` — B identifies the coefficient of that `1/t` for
the quadratic and linear probes. The recursion-derived odd coefficients (A) are new in the seabed.

## Numerical check

`numcheck_covK_order2.py` (sympy Wick expansion in `ε = 1/√t` to `ε⁶`, plus quadrature at `λ = 1.3, α = 0.7, γ = 1.1`): the
expansion reproduces `B₁`, `B₂` and gives `t²⟨x³⟩ = −5α/(2λ³) + (−15α³/(2λ⁶) + 25αγ/(4λ⁵))/t`, `t²⟨x⁴⟩ = 3/λ² + (25α²/(2λ⁵) − 4γ/λ⁴)/t`,
`t²Cov[ℓ, x²] = 1/λ + (5α²/(2λ⁴) − γ/λ³)/t`, `t²Cov[ℓ, x] = −α/(2λ²) + (−5α³/(4λ⁵) + 4αγ/(3λ⁴))/t`; the IBP formula for `B₃` agrees
with the expansion; quadrature: `t²Cov[ℓ, x²] = 0.767047, 0.768757, 0.769117` vs predicted `0.767436, 0.768782, 0.769119` and
`t²Cov[ℓ, x] = −0.201096, −0.205581, −0.206720` vs `−0.201001, −0.205576, −0.206719` at `t = 40, 160, 640` (differences `O(t⁻²)`).

## Questions

1. Are A and B correct, including the closed forms `B₃ = −15α³/(2λ⁶) + 25αγ/(4λ⁵)`, `C'_sq = 5α²/(2λ⁴) − γ/λ³`,
   `C'_lin = −5α³/(4λ⁵) + 4αγ/(3λ⁴)` and the bookkeeping that every product term needs only the listed orders? Please recompute
   `C'_sq` and `C'_lin` independently (e.g. from `t²Cov[ℓ, x²] = (λ/2)(t²⟨x⁴⟩ − (t⟨x²⟩)²) + (α/6)(t²⟨x⁵⟩ − t²⟨x³⟩⟨x²⟩) + (γ/24)(t²⟨x⁶⟩ −
   t²⟨x⁴⟩⟨x²⟩)`).
2. Is there a cleaner route to B than expanding all six pair covariances (e.g. a Stein-identity shortcut: `Cov[ℓ, ψ] = ⟨ℓψ⟩ − ⟨ℓ⟩⟨ψ⟩` with
   `t⟨x^k ℓ'⟩ = k⟨x^{k−1}⟩` — note `ℓ'` is not `ℓ`), or a way to get eq:covK's second order directly from eq:mean's (tide 70) and
   eq:cov's second order via the derivative identity `Cov[L, ψ] = −∂ₜ⟨ψ⟩` (tide 61/64: `covKFormula = −∂ₜ(½tr(BS) + b·meanShift)`)? If
   `t²Cov[ℓ, x] = −∂ₜ(t²... )`… more precisely `Cov_t[ℓ, x] = −d⟨x⟩_t/dt` exactly, and `⟨x⟩ = a/t + B₁/t² + O(t⁻³)` gives
   `Cov[ℓ, x] = a/t² + 2B₁/t³ + …` — does that reproduce `C'_lin = 2B₁`? (Check: `2B₁ = −5α³/(4λ⁵) + 4αγ/(3λ⁴)` — yes!) And
   `C'_sq = 2B₂`? (`2B₂ = 5α²/(2λ⁴) − γ/λ³` — yes!) So B may follow from differentiating the *asymptotic expansions* — but termwise
   differentiation of an asymptotic expansion is not automatic; is there a rigorous route (e.g. the rate statements plus the exact
   derivative identity plus a mean-value/Taylor argument), or is the direct moment route the honest one?
3. Wording against the note; pitfalls; vote.
