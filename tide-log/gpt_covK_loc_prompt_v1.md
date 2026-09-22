# Tide `covK-derivative-loc` (laplace seabed, local; the GitHub seabed moved to a monorepo mid-run): candidates for GPT-6 Astra

## Context

Tide `covK-derivative` proved, at `γ = 0` (`S = (tH)⁻¹`, `H` invertible, no symmetry), `covKFormula t H T B b = −d/ds[½ tr(B(sH)⁻¹) +
b⬝meanShift s H T]` with `meanShift s H T = −½ S (s T:S)`, via `(sH)⁻¹ = s⁻¹H⁻¹` (the function is `c/s`). The note's eq:covK is
displayed with `S = P⁻¹ = (tH + γI)⁻¹`: `Cov[K, ψ] = ½ tr(HSBS) + ½ (Sb)ᵀ(T:S) − (t/2) bᵀSHS(T:S) − (t/2)(Sb)ᵀ(T:(SHS))`, and eq:mean's
cubic term is `−½ S(tT:S)`. Your previous answer: for symmetric `S` this is exactly `−∂ₜ[½ tr(BS) − ½ (Sb)ᵀ(tT:S)]` with `∂ₜS = −SHS`,
`∂ₜ(tT:S) = T:S − tT:(SHS)`; and the derivative of the inverse along the line needs either the ring-inverse Fréchet derivative (Mathlib:
`hasFDerivAt_ringInverse (x : Rˣ) : HasFDerivAt Ring.inverse (−mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x` for `[NormedRing R]
[HasSummableGeomSeries R] [NormedAlgebra 𝕜 R]`; `Matrix.linftyOpNormedRing`/`linftyOpNormedAlgebra` are *local* instances; `Matrix.inv`
is `Ring.inverse` by `Matrix.nonsing_inv_eq_ringInverse`) or an elementary route.

## Candidates

**A. The `γ` formula.** `covKFormulaLoc t γ H T B b` := the four displayed terms with `S := (t • H + γ • 1)⁻¹`, and
`meanShiftLoc s γ H T := −½ • (S *ᵥ (s • contractT T S))`. Then `covKFormulaLoc_zero : covKFormulaLoc t 0 H T B b = covKFormula t H T B b`.

**B. Differentiating the resolvent, entrywise and elementary.** For `A(s) := s • H + γ • 1` with `IsUnit (A t).det`:
(i) `resolvent_identity : S(s) − S(t) = −(s − t) • (S(s) * H * S(t))` whenever both are invertible (pure algebra from
`Matrix.mul_nonsing_inv`/`nonsing_inv_mul`); (ii) `IsUnit (A s).det` for `s` near `t` (continuity of `det`, `Continuous.matrix_det`);
(iii) `ContinuousAt (fun s => S s) t` via `Matrix.inv_def : A⁻¹ = A.det⁻¹ʳ • A.adjugate` and `Continuous.matrix_adjugate`,
`ContinuousAt.inv₀`; (iv) entrywise `HasDerivAt (fun s => S s i j) (−(S t * H * S t) i j) t` from (i)–(iii) by
`hasDerivAt_iff_tendsto_slope`. This avoids any norm on matrices.

**C. The scalar identity.** `hasDerivAt_firstOrderLoc : HasDerivAt (fun s => ½ (B * S s).trace + b ⬝ᵥ meanShiftLoc s γ H T)
(−covKFormulaLoc t γ H T B b) t` for symmetric `H` (`Hᵀ = H`, hence `S` symmetric), assembled from (iv) by `HasDerivAt.sum`/`.mul`
over the finite sums defining `trace`, `mulVec`, `dotProduct`, `contractT`; then `covKFormulaLoc_eq_neg_deriv`. This makes the
note's displayed eq:covK (with `γ`) exactly `−∂ₜ` of its displayed eq:cov/eq:mean cubic prediction.

## Questions

1. Is B(iv) the least painful route in Lean, or is the `Ring.inverse` route with `attribute [local instance]
   Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra` viable (does `HasSummableGeomSeries (Matrix (Fin d) (Fin d) ℝ)` follow from
   completeness under that local norm, and would `HasDerivAt` in the matrix normed space then transfer to entries by `hasDerivAt_pi`)?
   Any third route (e.g. `Matrix.inv_def` and differentiating `det`/`adjugate` as polynomials directly, `HasDerivAt` of `det` via
   `Matrix.det_apply` sums)?
2. For C, is it better to prove `HasDerivAt` for the *matrix-valued* `S` under the local sup-norm instance (`Matrix.normedAddCommGroup`,
   `Matrix.normedSpace`, both local instances) and then compose with the continuous linear functionals `trace`, `mulVec`, `contractT`
   (via `LinearMap.toContinuousLinearMap` in finite dimension), or to stay entrywise with `HasDerivAt.sum` over `Finset.univ`?
3. Confirm the algebra: with `S` symmetric, `−∂ₜ[½ tr(BS) − ½ bᵀS(tT:S)] = ½ tr(HSBS) + ½ (Sb)ᵀ(T:S) − (t/2) bᵀSHS(T:S) −
   (t/2)(Sb)ᵀ(T:(SHS))`, term by term, where `∂ₜ tr(BS) = −tr(BSHS) = −tr(HSBS)` (cyclicity) and `∂ₜ[bᵀS(tT:S)] = −bᵀSHS(tT:S) +
   bᵀS(T:S) − bᵀS(tT:(SHS))`. Which hypotheses are genuinely needed (symmetry of `H`; `IsUnit (tH + γ1).det`; nothing on `t, γ` signs)?
4. Scope and vote (A+B+C)?
