# Tide `covK-separable` (seabed: laplace, off tide/covK-anharmonic) — candidates v1

Context. Tide `covK-anharmonic` verified the note's eq:covK for the exact one-dimensional anharmonic measure:
`t² Cov[ℓ, (B/2)x² + bx] → B/(2λ) − bα/(2λ²)`. The note's E2 runs the "canonical experiment" on the separable anharmonic oscillator in `d = 10`
(`L(u) = ∑ᵢ ℓᵢ(uᵢ)`, in the rotated frame `u = Qᵀ(w − w*)`) with probes `ψ` that are random quadratics; eq:covK in the eigenframe (`H`, `S`, `T`
diagonal) reads `∑ᵢ Bᵢᵢ/(2λᵢt²) − ∑ᵢ bᵢαᵢ/(2λᵢ²t²)`: only the diagonal of `B` enters at leading order.

Seabed (Lean 4 / Mathlib, all proved). `separableAnharmonic`, `gibbsExpectation_prod_separable : ⟨∏ᵢ φᵢ(uᵢ)⟩_L = ∏ᵢ ⟨φᵢ⟩_{ℓᵢ}` (no
hypotheses), `gibbsExpectation_coord_separable` (`Zᵢ ≠ 0`), `gibbsCov_coord_separable` (`Cov[uᵢ, uⱼ] = δᵢⱼ Var`), the d-dimensional
bilinearity lemmas of `AmbientMoments` (`gibbsCov_finsetSum_left/right`, `gibbsCov_const_mul_left`, `gibbsCov_linear_combination`, all under
integrability), `integrable_monomial_separableAnharmonic` (every `∏ uₖ^{eₖ} e^{−tL}`), `integrable_coord_energy_separableAnharmonic`
(`ℓₖ(uₖ) e^{−tL}`), the 1D `covK_anharmonic_sq/lin` limits and `gibbsCov_anharmonic_left`, the frame change `gibbsCov_rotated`, and the
matrix-level Frobenius/eigenframe algebra.

Candidates.

A. **Two-coordinate factorisation of covariances** (`gibbsCov_coord_fun_separable`): for observables of single coordinates,
   `Cov_L[f(uₖ), g(uᵢ)] = 0` when `k ≠ i` (product factorisation `⟨f(uₖ)g(uᵢ)⟩ = ⟨f⟩_{ℓₖ}⟨g⟩_{ℓᵢ}` and coordinate reduction) and
   `Cov_L[f(uₖ), g(uₖ)] = Cov_{ℓₖ}[f, g]`, given `Zᵢ ≠ 0` for all `i`.
B. **covK for the separable oscillator with a diagonal probe** (`covK_separable_diag`): for `ψ(u) = ∑ᵢ (Bᵢ/2)uᵢ² + bᵢuᵢ`,
   `Cov_L[L, ψ] = ∑ₖ∑ᵢ Cov_L[ℓₖ(uₖ), ψᵢ(uᵢ)] = ∑ᵢ Cov_{ℓᵢ}[ℓᵢ, (Bᵢ/2)x² + bᵢx]` by A and bilinearity, hence
   `t² Cov_L[L, ψ] → ∑ᵢ (Bᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²))` by the 1D theorem; identification with eq:covK's value for diagonal `H = diag(λ)`,
   `S = diag(1/(λᵢt))`, `T = diag(αᵢ)` (`covKDiag`, `covKDiag_eq`); the rotated-frame version `Cov_{L∘A}[L∘A, ψ∘A] = Cov_L[L, ψ]` (one
   rewrite with `gibbsCov_rotated`).
C. **Off-diagonal probe terms vanish at leading order** (`covK_separable_offdiag`): for `i ≠ j`, `t² Cov_L[L, uᵢuⱼ] → 0`: for `k ∉ {i, j}`
   the covariance is exactly zero (three-factor product); for `k = i`, `Cov_L[ℓᵢ(uᵢ), uᵢuⱼ] = ⟨uⱼ⟩ Cov_{ℓᵢ}[ℓᵢ, x]`, and
   `t²⟨uⱼ⟩Cov[ℓᵢ, x] = (t⟨uⱼ⟩)(t Cov[ℓᵢ, x]) → m₀ · 0`. With C, the full-quadratic-probe theorem `t² Cov_L[L, ½uᵀBu + bᵀu] → ∑ᵢ Bᵢᵢ/(2λᵢ) − …`
   follows (`covK_separable`), matching the note's random probes.

Numerical check done (`numcheck49.py`, `d = 2`, `λ = (1, 3)`, `a = ½`, `B = [[2, 0.7],[0.7, 1.5]]`, `b = (0.8, −0.4)`, quadrature): at
`t = 800`, `t² Cov[L, ψ]` for the full probe and for its diagonal part agree with each other and with eq:covK's eigenframe value to three digits,
and the off-diagonal `t² Cov[L, u₁u₂]` is `O(10⁻²)` and shrinking.

Questions. (1) Are A–C correct, in particular the exact vanishing of `Cov_L[ℓₖ(uₖ), uᵢuⱼ]` for `k ∉ {i,j}` (the product `⟨ℓₖ⟩⟨uᵢ⟩⟨uⱼ⟩` appears
in both terms) and the reduction `Cov_L[ℓᵢ(uᵢ), uᵢuⱼ] = ⟨uⱼ⟩_{ℓⱼ} Cov_{ℓᵢ}[ℓᵢ, x]` for `i ≠ j`? (2) What is the least painful Lean route for the
case analysis in A/C — a general lemma for a product observable `∏ₘ φₘ(uₘ)` where all but at most three `φₘ` are `1` (using
`gibbsExpectation_prod_separable` with `fun m x => if m = k then f x else if m = i then g x else 1`), or separate lemmas per pattern? (3) Is
B (diagonal probes) a coherent, note-relevant tide on its own if C turns out long, or is C required to make the E2 claim ("random
quadratics") honest? Please end with a vote on A–C.
