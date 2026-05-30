# Tide: anharmonic third cumulant κ₃

**Direction (user):** The third connected cumulant of `u = -(t x)`:
`κ₃ = K'''(0) = ∂²_h⟨u⟩_h|_0`, the second derivative of the perturbed mean,
in closed form `(G_3 G_0² - 3 G_1 G_2 G_0 + 2 G_1³)/G_0³ = ⟨u³⟩₀ - 3⟨u²⟩₀⟨u⟩₀ + 2⟨u⟩₀³`.
Survey v4 #2 (next rung after κ₂; capstone toward κ₄).

**Seabed:** lean/laplace, commit 03fdaae (main, post general-h susceptibility).
**Started:** 2026-05-30

## Seabed snapshot

- `weightedPartition_hasDerivAt n {|h₀|<1}`: HasDerivAt (G n) (G (n+1) h₀) h₀.
- `anharmonic_mean_hasDerivAt_general {|h₀|<1}`: deriv of the mean `M = G_1/G_0`
  at `h₀` is the susceptibility `S(h₀) = (G_2 G_0 - G_1²)/G_0²` — so
  `deriv M =ᶠ[𝓝 0] S` on `ball 0 1`.
- `weightedPartition_zero_zero_pos`: `G_0(0) > 0`.
- Mathlib `HasDerivAt.mul/.sub/.pow/.div`, `iteratedDeriv_succ/_one`,
  `Filter.EventuallyEq.deriv_eq`.

## Candidate (agreed) — proceed-without-GPT

`iteratedDeriv 2 (fun h => G_1 h / G_0 h) 0
   = (G_3(0)·G_0(0)² − 3·G_1(0)·G_2(0)·G_0(0) + 2·G_1(0)³)/G_0(0)³`.

Proof: `κ₃ = M''(0) = deriv(deriv M)(0)`; `deriv M =ᶠ S` near 0 (tide #7), so
`= deriv S 0`; and `HasDerivAt S κ₃-value 0` by the compound quotient rule
(`(G_2·G_0 − G_1²)/G_0²` differentiated via `.mul/.sub/.pow/.div`), the raw
output `convert`ed to the clean form by `field_simp`/`ring`.

**Proceed-without-GPT:** mechanical — established `HasDerivAt` combinators +
`EventuallyEq.deriv_eq` chaining (as in tide #3) + an atom-`ring` identity in
`G_0..G_3`. The cumulant-from-moments formula is standard; signs hand-checked
(`M''(0) = (G_3 G_0² − 3 G_1 G_2 G_0 + 2 G_1³)/G_0³`, matching
`⟨u³⟩−3⟨u²⟩⟨u⟩+2⟨u⟩³`).

## Numerical check

Not feasible / not needed: structural (cumulant identity); the `G_n(0)`
integrals were validated in the higher-deriv tide, and the algebraic
moments→cumulants step is checked by `ring`.

## Result

New file `Laplace/OneD/AnharmonicThirdCumulant.lean`: `anharmonic_third_cumulant`
— iteratedDeriv 2 of the mean G_1/G_0 at 0 = (G_3 G_0² - 3 G_1 G_2 G_0 + 2 G_1³)/G_0³.
Compound HasDerivAt (mul/sub/pow/div) + convert/ring + EventuallyEq.deriv_eq
chaining through tide #7. ~70 lines, **first-try build**, no sorries.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-third-cumulant.tex`
