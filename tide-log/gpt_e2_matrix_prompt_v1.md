# Tide `e2-matrix` (laplace seabed, on top of `tide/e7-matrix`): candidates for GPT-6 Astra

## Context

The Sanity-on-Sampling note states four Laplace predictions in matrix notation (`S = (tH)⁻¹`, `T = D³L(w*)`, `(T:S)ₗ = Tₗₘₙ Sₘₙ`):

```
eq:mean   ⟨w⟩ − w* = −½ S (t T:S) + γ S (w₀ − w*) + O(S²)
eq:covK   Cov[K, ψ] = ½ tr(H S B S) + ½ (Sb)ᵀ(T:S) − (t/2) bᵀ S H S (T:S) − (t/2) (Sb)ᵀ (T:(SHS))
```
(`ψ(w) = ½ (w−w*)ᵀB(w−w*) + bᵀ(w−w*)`, `K = tL`.) E2 checks them against exact quadrature for the rotated separable anharmonic
oscillator `L∘A`, `A(w) = Qᵀ(w − c)`, `ℓᵢ(x) = λᵢx²/2 + αᵢx³/6 + γᵢx⁴/24`. The seabed already has the exact limits in the eigenframe:

```lean
-- Laplace/Multi/AmbientMoments.lean
theorem rotatedAnharmonic_ambient_mean_asymptotic (hQ : Qᵀ * Q = 1) (c) (hlam) (hgamma) (hdisc) (j : ι) :
    Tendsto (fun t => t * (gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) - c j)) atTop
      (𝓝 (∑ i, Q j i * (-alpha i / (2 * lam i ^ 2))))
theorem gibbsExpectation_coord_rotatedAnharmonic … (j) : ⟨w j⟩ = c j + ∑ i, Q j i * ⟨u i⟩_{separable}
-- Laplace/Multi/VarianceOrder2.lean
theorem mean_anharmonic_rate_div (hlam) (hgamma) (hdisc) : ∃ K T, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t}, T ≤ t →
    |⟨x⟩_t - (-alpha / (2 * lam ^ 2)) / t| ≤ K / t ^ 2                       -- one-dimensional
-- Laplace/Multi/CovKSeparable.lean (tide covK-separable)
theorem covK_rotatedAnharmonic_quadratic (hQ) (c) (hlam) (hgamma) (hdisc) (B : ι → ι → ℝ) (b : ι → ℝ) :
    Tendsto (fun t => t ^ 2 * gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) + ∑ i, b i * affineFrame Q c w i)) atTop
      (𝓝 (∑ i, (B i i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2))))     -- affineFrame Q c w = Qᵀ (w − c)
-- Laplace/OneD/CovKAnharmonic.lean (tide covK-anharmonic): covKOneDim, covKOneDim_eq — the four terms of eq:covK in 1D sum to
--   (B/(2λ) − bα/(2λ²))/t²
-- Laplace/Multi/OneLoopRotated.lean (tide e7-matrix, this morning; indices Fin d)
def rotT Q alpha i j k := ∑ l, alpha l * Q i l * Q j l * Q k l ;  def rotQ …
theorem contractT_rot (hQ) (alpha s) (l) : contractT (rotT Q alpha) (Q * diagonal s * Qᵀ) l = ∑ p, alpha p * s p * Q l p
theorem conj_mul_conj (hQ) (M N) : (Q * M * Qᵀ) * (Q * N * Qᵀ) = Q * (M * N) * Qᵀ
theorem smul_conj_diagonal_inv (hQ) (hlam : ∀ i, lam i ≠ 0) (ht : t ≠ 0) : (t • (Q * diagonal lam * Qᵀ))⁻¹ = Q * diagonal (fun i => 1 / (lam i * t)) * Qᵀ
theorem conj_diagonal_apply (Q s i j) : (Q * diagonal s * Qᵀ) i j = ∑ p, s p * Q i p * Q j p
theorem col_orthonormal (hQ) (p q) : ∑ k, Q k p * Q k q = if p = q then 1 else 0
```

## Candidates

**A. eq:mean in matrix form.** Define `meanShift t H T := -(t/2) • ((t • H)⁻¹ *ᵥ contractT T (t • H)⁻¹)` (the `γ = 0` case of eq:mean).
For the rotated tensors, `meanShift t (Q diag λ Qᵀ) (rotT Q alpha) = Q *ᵥ (fun i => -alpha i / (2 * lam i ^ 2 * t))`, hence
`t • meanShift` is the constant vector `Q *ᵥ (−α/(2λ²))`, and the exact mean satisfies, for every ambient coordinate `j`,
`|⟨wⱼ⟩ − cⱼ − meanShift j| ≤ K/t²` for `t ≥ T` (from `gibbsExpectation_coord_rotatedAnharmonic`, `mean_anharmonic_rate_div` per
coordinate and `∑ᵢ |Qⱼᵢ| Kᵢ`), and `t(⟨wⱼ⟩ − cⱼ − meanShift j) → 0` (the seabed's limit restated). So eq:mean's leading term is exact to
relative `O(1/t)`, as E2 measures.

**B. eq:covK in matrix form.** Define on `Fin d`
`covKMatrix t H T B b := ½ (H * S * B * S).trace + ½ (S *ᵥ b) ⬝ᵥ contractT T S − (t/2) b ⬝ᵥ ((S * H * S) *ᵥ contractT T S) − (t/2) (S *ᵥ b) ⬝ᵥ contractT T (S * H * S)`
with `S = (t • H)⁻¹`. For the rotated tensors: `S H S = Q diag(λ s²) Qᵀ = Q diag(1/(λt²)) Qᵀ`, `tr(H S B S) = ∑ᵢ (QᵀBQ)ᵢᵢ/(λᵢ t²)`,
`(Sb)ᵀ(T:S) = ∑ᵢ (Qᵀb)ᵢ αᵢ/(λᵢ² t²)`, `bᵀ SHS (T:S) = ∑ᵢ (Qᵀb)ᵢ αᵢ/(λᵢ² t³)`, `(Sb)ᵀ(T:(SHS)) = ∑ᵢ (Qᵀb)ᵢ αᵢ/(λᵢ² t³)`, so
`covKMatrix = (∑ᵢ ((QᵀBQ)ᵢᵢ/(2λᵢ) − (Qᵀb)ᵢ αᵢ/(2λᵢ²)))/t²` (`covKMatrix_rot`); the two `b`-terms with the minus sign each equal the
positive one, leaving `−(Qᵀb)ᵢαᵢ/(2λᵢ²t²)`, exactly as in the one-dimensional `covKOneDim_eq`. Then, for the ambient probe
`ψ(w) = ½ (w−c)ᵀB(w−c) + bᵀ(w−c)` (which equals `½ uᵀ(QᵀBQ)u + (Qᵀb)ᵀu` in `u = Qᵀ(w − c)` since `QQᵀ = 1`),
`t² · Cov[L∘A, ψ] → t² · covKMatrix` i.e. `Tendsto (fun t => t² (Cov_t[L∘A, ψ] − covKMatrix t)) atTop (𝓝 0)` and
`Tendsto (t² Cov_t[L∘A, ψ]) atTop (𝓝 (∑ᵢ …))` (`covK_rotatedAnharmonic_quadratic` transported through the probe identity).

**C (optional).** The corresponding statements in the note's parametrisation (`αᵢ² = a²λᵢ³`, `γᵢ = λᵢ²`), and a remark that eq:mean's
`γ S (w₀ − w*)` term is the localisation term (not covered: `γ = 0` here).

## Numerical check (`numcheck_e2_matrix.py`, `d = 3`, `λ = (1, 2, 5)`, `a = ½`, random `Q`, `c`, symmetric `B`, `b`)

`‖meanShift − Q(−α/(2λ²t))‖ = 1.8e-17` at `t = 9`; `t² covKMatrix = −0.97104` against the diagonal formula `−0.97104`; exact `t² Cov[L, ψ]`
at `t = 50, 200, 800`: `−0.9500, −0.9657, −0.9697`, against `t² covKMatrix` (constant) — converging like `1/t`; `t‖Q⟨u⟩ − Q(−α/(2λ²t))‖` decays like `1/t`.

## Questions

1. Are A and B correct, in particular the four-term evaluation of eq:covK on the rotated tensors and the probe identity
   `½(w−c)ᵀB(w−c) + bᵀ(w−c) = ½ uᵀ(QᵀBQ)u + (Qᵀb)ᵀu`? Is `meanShift` the right reading of eq:mean at `γ = 0` (sign and factor)?
2. Lean strategy: for `tr(H S B S)` with `H, S` conjugated diagonals, is `Matrix.trace_mul_cycle` + `conj_mul_conj` + `QᵀQ = 1` +
   `Matrix.trace` of `diagonal(λs) * (QᵀBQ) * diagonal(s)` via `Matrix.diagonal_mul`/`mul_diagonal` the clean route? For the
   `mulVec`/`dotProduct` terms, `Matrix.mulVec_mulVec`, `Matrix.dotProduct_mulVec`, and `mulVec` of `Q * diagonal s * Qᵀ` against
   `Q *ᵥ v` — any pitfalls with `Matrix.mulVec` associativity lemmas (`Matrix.mulVec_mulVec : M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`)?
3. Statement shape: should B's headline be the limit `Tendsto (t²(Cov − covKMatrix)) → 0` or a rate? (The seabed's covK limit is
   `o(1)` relative, no rate; a rate would need the moment rates for `Cov[ℓ, x²]`, `Cov[ℓ, x]` — not available.) Anything to add so
   that "all four Laplace predictions of E2 in the note's matrix notation" is a fair description of the seabed after this tide
   (eq:cov = `(tH)⁻¹` and its one-loop correction are done, eq:llc = `t⟨L⟩ → d/2` is done)?
4. Scope and vote (A+B, with C optional)?
