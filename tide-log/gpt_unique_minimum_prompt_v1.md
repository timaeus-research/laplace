# Tide `unique-minimum` (laplace seabed): candidates for GPT-6 Astra

## Context

The note (Setup, "Potentials"): "`anharm`: `L(w) = ∑ᵢ (λᵢ/2 uᵢ² + αᵢ/6 uᵢ³ + gᵢ/24 uᵢ⁴)`, `αᵢ = a λᵢ^{3/2} sᵢ`, `gᵢ = λᵢ²`, `sᵢ ∈ {±1}` … The
dimensionless anharmonicity `a` of the separable potential is the same in every direction by construction, and `a² < 3` keeps the
minimum unique." The seabed carries the hypothesis `hdisc : α² < 3λγ` on every anharmonic theorem (it is what makes the
`e^{−tℓ}` integrals behave uniformly) but has no theorem *about* the minimum. `anharmonicPotential λ α γ x = λx²/2 + αx³/6 +
γx⁴/24`; `anhD1 = ℓ'`, `anhD2 = ℓ''` are in `RotatedDerivatives`; the `d`-dimensional `rotatedAnharmonic Q c λ α γ w = ∑ᵢ ℓᵢ((Qᵀ(w −
c))ᵢ)`.

## Candidates (`numcheck_unique_minimum.py`, sympy)

**A. `a² < 3` is exactly the unique-global-minimum condition (one dimension).** For `λ, γ > 0`:
`ℓ(x) = x² q(x)`, `q(x) = λ/2 + αx/6 + γx²/24`, `disc q = α²/36 − λγ/12`, so
`anharmonic_pos_of_disc : α² < 3λγ → x ≠ 0 → 0 < ℓ(x)` (hence `0` is the unique global minimiser: `ℓ 0 = 0 < ℓ x`), and the
converse/sharpness `anharmonic_not_unique_of_disc_eq : α² = 3λγ → ℓ(−2α/γ) = 0` (a second global minimiser) and
`anharmonic_neg_of_disc_gt : 3λγ < α² → ∃ x, ℓ(x) < 0` (`0` is not even a global minimiser). In the note's parametrisation
`α² = a²λ³`, `γ = λ²`: `a² < 3`.

**B. Extra critical points appear earlier, at `a² ≥ 8/3`.** `ℓ'(x) = x (λ + αx/2 + γx²/6)`, `disc = α²/4 − 2λγ/3`, so
`∃ x ≠ 0, ℓ'(x) = 0 ↔ 8λγ/3 ≤ α²` (`anharmonic_crit_iff`), i.e. `8/3 ≤ a²`. For `8/3 ≤ a² < 3` the potential has a local maximum
and a second local minimum (with `ℓ > 0` there) but `0` is still the unique global minimiser. Numerics at `λ = γ = 1`: `a² = 2.8`
has nonzero critical points `x ≈ −1.6, −3.4` with `ℓ > 0` everywhere but `0`; `a² = 3.2` has `ℓ(−2a) < 0`.

**C. The `d`-dimensional statement.** For `QᵀQ = 1`, `λᵢ, γᵢ > 0`, `αᵢ² < 3λᵢγᵢ`:
`rotatedAnharmonic_pos : w ≠ c → 0 < rotatedAnharmonic Q c λ α γ w` (sum of nonnegative terms, one positive since `Qᵀ(w − c) ≠ 0`),
so `c` is the unique global minimiser of E2's potential (`rotatedAnharmonic_center : L(c) = 0`).

## Questions

1. Are A, B correct as stated (in particular the exact thresholds `3` and `8/3`, and `x₀ = −2α/γ` at equality)? Is "keeps the
   minimum unique" best read as "unique global minimiser" (true for `a² < 3`) — while "unique critical point" would need `a² < 8/3`?
   Should the staging note flag that for `8/3 ≤ a² < 3` the potential is not unimodal, and does E2's `a ∈ {0.5, 1}` (`a² = 0.25, 1`)
   stay clear of both thresholds?
2. Lean: `0 < q(x)` from `α² < 3λγ` and `γ > 0` — completing the square `q(x) = (γ/24)(x + 2α/γ)² + (λ/2 − α²/(6γ))` and
   `nlinarith`/`positivity`, or `nlinarith [sq_nonneg (γ x + 2α), …]` directly? For `∃ x, ℓ(x) < 0` when `α² > 3λγ`, the witness
   `x = −2α/γ` gives `ℓ = (4α²/γ²)(λ/2 − α²/(3γ) + α²/(6γ)) = (4α²/γ²)(λ/2 − α²/(6γ)) < 0` ✓?
3. Anything else cheap and relevant (e.g. `ℓ'' (0) = λ > 0`, strict convexity near `0`; the minimiser is nondegenerate — "All are Morse
   at `w*`" in the note)?
4. Scope and vote (A+B+C)?
