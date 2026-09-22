# Tide 70 consult: integration by parts for the anharmonic Gibbs measure and eq:mean to second order

One-round consult on a Lean 4 / Mathlib formalisation step in the `laplace` seabed (Laplace/Hessian-route formulas of a note on
SGLD sanity checks). Real theorem names available: `anharmonicPotential lam alpha gamma x = lam/2 x² + alpha/6 x³ + gamma/24 x⁴`;
`integrable_pow_mul_exp_neg_t_anharmonic (m) : Integrable (x^m e^{−tℓ})`; `partitionFunction_anharmonic_pos`;
`mean_anharmonic_O2_rate` (`|t⟨x⟩ + α/(2λ²)| ≤ K/t`); `secondMoment_anharmonic_order2_rate` (`|t⟨x²⟩ − 1/λ − (45·cubicScale² − …)/t| ≤ K/t²`
with the seabed's `cubicScale`; the coefficient is `B₂ = 5α²/(4λ⁴) − γ/(2λ³)` in plain form); `thirdMoment_anharmonic_rate_sharp`
(`|t²⟨x³⟩ + 5α/(2λ³)| ≤ K/t`); `oddMoment_anharmonic_rate k`, `evenMoment_anharmonic_rate k`; E2 transport
`gibbsExpectation_coord_rotatedAnharmonic : ⟨wⱼ⟩ = cⱼ + ∑ᵢ Qⱼᵢ ⟨uᵢ⟩_{ℓᵢ}`, `meanShift_rot : meanShift t H T = Q(−αᵢ/(2λᵢ²t))`,
finite-sum rate lemmas `sum_rate_div`, `sum_rate_div_sq`. Mathlib: `integral_eq_zero_of_hasDerivAt_of_integrable`.
The note's eq:mean is first order: `⟨w⟩ − w* = −½S(tT:S) + O(S²)`.

## Candidates v1 (Claude)

Setting: the 1D anharmonic Gibbs measure `e^{−tℓ}`, `ℓ = λx²/2 + αx³/6 + γx⁴/24` (`λ, γ > 0`, `α² < 3λγ`), `ℓ'(x) = λx + (α/2)x² + (γ/6)x³`;
the seabed has all polynomial moments integrable (`integrable_pow_mul_exp_neg_t_anharmonic`), `Z > 0`, the second moment to second
order (`secondMoment_anharmonic_order2_rate`: `|t⟨x²⟩ − 1/λ − B₂/t| ≤ K/t²`) and the third moment at leading order with rate
(`thirdMoment_anharmonic_rate_sharp`: `|t²⟨x³⟩ + 5α/(2λ³)| ≤ K/t`), and the mean at leading order (`mean_anharmonic_O2_rate`:
`|t⟨x⟩ + α/(2λ²)| ≤ K/t`); no second-order mean. Mathlib: `integral_eq_zero_of_hasDerivAt_of_integrable (hderiv : ∀ x, HasDerivAt f
(f' x) x) (hf' : Integrable f') (hf : Integrable f) : ∫ f' = 0` (no boundary terms to control).

- **A (integration by parts / Stein identity).** For `t > 0` and every `k : ℕ`: `k⟨x^{k−1}⟩ = t⟨x^k ℓ'(x)⟩`, i.e. the moment
  recursion `k⟨x^{k−1}⟩ = t(λ⟨x^{k+1}⟩ + (α/2)⟨x^{k+2}⟩ + (γ/6)⟨x^{k+3}⟩)`; at `k = 0`: `λ⟨x⟩ + (α/2)⟨x²⟩ + (γ/6)⟨x³⟩ = 0`
  (`ibp_anharmonic_zero`). Route: `F = x^k e^{−tℓ}`, `F' = (k x^{k−1} − t x^k ℓ') e^{−tℓ}`, both integrable (polynomial × Boltzmann),
  `integral_eq_zero_of_hasDerivAt_of_integrable`, divide by `Z`. Exact identities; no asymptotics.
- **B (eq:mean to second order, 1D).** `|t⟨x⟩ + α/(2λ²) − B₁/t| ≤ K/t²` with `B₁ = −5α³/(8λ⁵) + 2αγ/(3λ⁴)`: from A at `k = 0`,
  `⟨x⟩ = −(α/(2λ))⟨x²⟩ − (γ/(6λ))⟨x³⟩`, so `t⟨x⟩ = −(α/(2λ))(1/λ + B₂/t + O(t⁻²)) − (γ/(6λ))(−5α/(2λ³t) + O(t⁻²))`, i.e.
  `B₁ = −αB₂/(2λ) + 5αγ/(12λ⁴)` with `B₂ = 5α²/(4λ⁴) − γ/(2λ³)` (the seabed's second-moment coefficient, to be matched to its
  `cubicScale` form). This is the second-order term of eq:mean's `⟨w⟩ − w*` (the note stops at first order; a suggested addition
  like the two-loop energy of tide 56).
- **C (E2, `d` dimensions).** `|t(⟨wⱼ⟩ − cⱼ) − (Q(−αᵢ/(2λᵢ²))ᵢ)ⱼ − (Q(B₁,ᵢ)ᵢ)ⱼ/t| ≤ K/t²` on E2's rotated oscillator, via the seabed's
  exact `⟨wⱼ⟩ = cⱼ + ∑ᵢ Qⱼᵢ⟨uᵢ⟩_{ℓᵢ}` and a `1/t²` finite-sum lemma; with `meanShift_rot` the first term is `t·meanShift`, so this
  is "eq:mean = meanShift + meanShift₂/t² + O(t⁻³)" with `meanShift₂ = Q(B₁,ᵢ)ᵢ`. Optional: express `B₁` through the note's tensors
  (`T`, `Q₄`, `S`) — not attempted here.

Rationale: GPT (tides 67, 69) twice named the integration-by-parts identity as the bridge to the missing second-order mean; it is
an exact structural statement (the Stein/Gibbs identity, new in the seabed), and it closes eq:mean's second order for E2 at no
new analytic cost. Follow-ups it enables: the second-order localised mean coefficient (tide 67's C) and the first anharmonic
correction of the localised LLC (tide 69's follow-up).

## Numerical check

`numcheck_gibbs_ibp.py` (`λ = 1.3, α = 0.7, γ = 1.1`): `⟨ℓ'⟩`, `2⟨x⟩ − t⟨x²ℓ'⟩`, `3⟨x²⟩ − t⟨x³ℓ'⟩` all `< 3e-17` at `t = 10, 40, 160, 640`
(exact identities); `t²(⟨x⟩ + α/(2λ²t)) = 0.1166, 0.1207, 0.1217, 0.1219` against `B₁ = 0.12199` — converging as `O(1/t)`, as B claims.

## Questions

1. Are A, B, C correct? Check `B₁ = −αB₂/(2λ) + 5αγ/(12λ⁴) = −5α³/(8λ⁵) + 2αγ/(3λ⁴)` with `B₂ = 5α²/(4λ⁴) − γ/(2λ³)`, and the sign
   conventions (`⟨x³⟩ = −5α/(2λ³t²) + O(t⁻³)`). Is the remainder in B really `O(t⁻²)` given the inputs (second moment to `t⁻²`
   *remainder* `K/t²` after multiplying by `t`; third moment `K/t` after `t²`), i.e. `t⟨x⟩ = −α/(2λ²) + B₁/t + O(t⁻²)`?
2. Is there a cleaner or more general statement worth taking (e.g. the Stein identity for arbitrary `C¹` observables with
   polynomial growth, or the full moment recursion as a theorem family), and is B₁ expressible in the note's tensor language
   (`T = α`, `Q₄ = γ`, `S = 1/(λt)`) in a way that would read naturally as eq:mean's second-order term? Any known closed form to
   compare against?
3. Pitfalls in Lean: `HasDerivAt` of `x^k · exp(−tℓ(x))` (product/chain rule), the `k = 0` case (`x^{0−1}` in ℕ), integrability of
   `F' = (k x^{k−1} − t x^k ℓ')e^{−tℓ}` as a finite combination of monomials. Vote on the bundle.
