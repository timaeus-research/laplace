# Tide `var-order2-rate` (seabed: laplace, off tide/gibbs-rotation) — candidates v1

Context. E7 of the Sanity-on-Sampling note: "For the anharmonic oscillators the remainder drops from `O(t⁻¹)` to `O(t⁻²)` in relative terms:
at `t = 100` the worst directional error falls from `2.5×10⁻³` to `2.6×10⁻⁵` (`a = 0.5`)". Tides `separable-exact`/`gibbs-rotation` proved, for
the exact Gibbs measure of the note's separable anharmonic oscillator, the *limit* `t(λᵢ t Var − 1) → a² − 1/2` along every eigendirection
(the one-loop constant). Nothing yet quantifies the remainder *after* the one-loop term.

Seabed (Lean 4 / Mathlib, all proved). One-dimensional explicit rates for `ℓ = λx²/2 + αx³/6 + γx⁴/24`, `λ, γ > 0`, `α² < 3λγ`, with
`A = cubicScale λ α = α/(6λ√λ)`, `B = quarticScale λ γ = γ/(24λ²)`:
`secondMoment_anharmonic_order2_rate : ∃ K T, 0 ≤ K ∧ 1 ≤ T ∧ ∀ t ≥ T, |t⟨x²⟩ − 1/λ − (45A² − 12B)/(λt)| ≤ K/(t√t)`;
`mean_anharmonic_O2_rate : ∃ K T, …, |t⟨x⟩ + α/(2λ²)| ≤ K/t`; the limit `var_anharmonic_second_order : t²(Var − 1/(λt)) → α²/λ⁴ − γ/(2λ³)`;
the separable and rotated identities `gibbsCov_separableAnharmonic`, `gibbsCov_rotatedAnharmonic_eq` reducing `Var_L[uᵢ]` to the 1D variance.

Candidates.

A. **The one-dimensional variance at second order with an explicit rate** (`var_order2_coeff`, `var_anharmonic_order2_rate`):
   `(45A² − 12B)/λ − (α/(2λ²))² = α²/λ⁴ − γ/(2λ³)` and
   `∃ K T, 0 ≤ K ∧ 1 ≤ T ∧ ∀ t ≥ T, |t Var_t[x] − 1/λ − (α²/λ⁴ − γ/(2λ³))/t| ≤ K/(t√t)`,
   from `t Var = t⟨x²⟩ − (t⟨x⟩)²/t` and `|(t⟨x⟩)² − m₀²| = |t⟨x⟩ − m₀||t⟨x⟩ + m₀| ≤ (K₁/t)(2|m₀| + K₁)`, `m₀ = −α/(2λ²)`, `1/t² ≤ 1/(t√t)` for `t ≥ 1`.
B. **Relative form and the note's parametrisation** (`var_relative_rate_order2`, `var_relative_rate_order2_note`):
   `|t(λ t Var − 1) − (α²/λ³ − γ/(2λ²))| ≤ λK/√t`, and for `α² = a²λ³`, `γ = λ²`: `|t(λ t Var − 1) − (a² − ½)| ≤ K'/√t` — the exact relative
   error is `(a² − ½)/t + O(t^{−3/2})`.
C. **Transport to the E2 oscillator** (`separableAnharmonic_var_order2_rate_note`, `rotatedAnharmonic_var_order2_rate_note`): the same bound
   along every coordinate / every column of `Q`, by the covariance identities (valid for `t ≥ T ≥ 1 > 0`).

Numerical check done (`numcheck45.py`): the coefficient identity to 1e-16 for `λ = 1, 3`; exact quadrature gives
`|t(λtVar − 1) − (a² − ½)| = 1.6e-2, 2.6e-3, 2.7e-4, 2.7e-5` at `t = 10, 100, 1000, 10000`, i.e. `≈ 0.27/t` — the true remainder is `O(t⁻¹)` in this
quantity (relative `O(t⁻²)`, as the note says), while the bound we can prove from the seabed's rates is `O(t^{−1/2})` (relative `O(t^{−3/2})`).

Questions. (1) Is A correct, and is the `K/(t√t)` rate the best available from the listed ingredients (the `O(t^{-1/2})` loss comes from the
mean's `K₁/t` rate entering squared — is there a slicker decomposition that keeps `K/(t√t)` for the variance without needing a better mean
rate, or is the variance rate genuinely `O(t^{-3/2})` from these inputs)? (2) How should the note's "`O(t⁻²)` in relative terms" be worded
against a theorem that certifies only `O(t^{−3/2})`: "the one-loop prediction is exact to `o(1/t)` relative, with an explicit `t^{−3/2}`
certificate", or should we push for the `t⁻²` rate (which would need third-order moment expansions not in the seabed)? (3) Anything close by:
e.g. the analogous second-order rate for the mean (`mean_anharmonic_O2_rate` already gives `⟨x⟩ = −α/(2λ²t) + O(t⁻²)`) or for the energy
`t⟨ℓ⟩ = ½ + c/t + O(t^{−3/2})` from the moment rates (the constant `c` would be E2's finite-`t` LLC deviation to first order: is
`t⟨ℓ⟩ − ½ ≈ c/t` with `c = (λ/2)C₂ + (α/6)(−5α/(2λ³)) + (γ/24)(3/λ²)` right?). Please end with a vote on A–C (+ any addition).
