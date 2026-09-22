# Tide `covK-rate` (laplace seabed): candidates for GPT-6 Astra

## Context

E2 of the Sanity-on-Sampling note: "All four Laplace predictions converge to the exact values with relative error proportional to `1/t`
… including for the second-order quantity eq:covK." The seabed certifies eq:covK for the exact anharmonic measures only as a *limit*
(`t² Cov[ℓ, ψ] → C`, tides `covK-anharmonic`, `covK-separable`, `e2-matrix`), with no rate. The all-orders sharp moments landed this
morning make a rate reachable. Seabed (`ℓ = λx²/2 + αx³/6 + γx⁴/24`, `⟨·⟩` the Gibbs mean at temperature `t`, `Cov` its covariance):

```lean
-- Laplace/OneD/MomentsSharp.lean (tide moments-sharp)
theorem evenMoment_anharmonic_rate (k) : ∃ K T, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t}, T ≤ t → |t ^ k * ⟨x^(2k)⟩ - (2k−1)‼/λ^k| ≤ K / t
theorem evenMoment_anharmonic_order2_rate (k) : … |t ^ k * ⟨x^(2k)⟩ - (2k−1)‼/λ^k - C_k/(λ^k t)| ≤ K / t ^ 2
theorem oddMoment_anharmonic_rate (k) : … |t ^ (k+1) * ⟨x^(2k+1)⟩ + α(2k+3)‼/(6λ^(k+2))| ≤ K / t
-- Laplace/OneD/CovKAnharmonic.lean (tide covK-anharmonic)
theorem gibbsCov_pow_pow (L t m n) : Cov[x^m, x^n] = ⟨x^(m+n)⟩ − ⟨x^m⟩⟨x^n⟩
theorem gibbsCov_anharmonic_left (ht : 0 < t) (ψ) (hψ2 hψ3 hψ4 : integrability of x^j ψ e^{−tℓ}) : Cov[ℓ, ψ] = (λ/2)Cov[x², ψ] + (α/6)Cov[x³, ψ] + (γ/24)Cov[x⁴, ψ]
theorem covK_anharmonic (B b) : Tendsto (fun t => t ^ 2 * Cov[ℓ, (B/2)x² + bx]) atTop (𝓝 (B/(2λ) − bα/(2λ²)))
theorem covK_anharmonic_agree (B b) : Tendsto (fun t => t ^ 2 * (Cov[ℓ, (B/2)x² + bx] − covKOneDim lam alpha t B b)) atTop (𝓝 0)
  -- covKOneDim = the four terms of eq:covK in 1D, = (B/(2λ) − bα/(2λ²))/t² (covKOneDim_eq)
-- Laplace/Multi/CovKSeparable.lean (tide covK-separable), ι a Fintype, u the eigen-coordinates
theorem gibbsCov_energy_probe_separableAnharmonic (ht) (B b : ι → ℝ) : Cov_L[L, ∑ᵢ (Bᵢ/2)uᵢ² + bᵢuᵢ] = ∑ₖ Cov_{ℓₖ}[ℓₖ, (Bₖ/2)x² + bₖx]
theorem gibbsCov_energy_pair_separableAnharmonic (ht) (hij : i ≠ j) : Cov_L[L, uᵢuⱼ] = ⟨x⟩ⱼ Cov_i[ℓᵢ, x] + ⟨x⟩ᵢ Cov_j[ℓⱼ, x]
theorem gibbsCov_energy_coord_pow_separableAnharmonic (ht) (i m) : Cov_L[L, uᵢ^m] = Cov_{ℓᵢ}[ℓᵢ, x^m]
theorem covK_separable_quadratic (B : ι → ι → ℝ) (b) : Tendsto (fun t => t ^ 2 * Cov_L[L, ∑ᵢⱼ Bᵢⱼ/2 uᵢuⱼ + ∑ bᵢuᵢ]) atTop (𝓝 (∑ᵢ (Bᵢᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²))))
-- Laplace/Multi/E2Matrix.lean (tide e2-matrix), Fin d, rotated frame A(w) = Qᵀ(w − c)
theorem covKFormula_rot (ht : t ≠ 0) (B b) : covKFormula t H T B b = (∑ᵢ ((QᵀBQ)ᵢᵢ/(2λᵢ) − (Qᵀb)ᵢαᵢ/(2λᵢ²))) / t ^ 2
theorem probe_affineFrame : ½(w−c)ᵀB(w−c) + bᵀ(w−c) = ∑ᵢⱼ (QᵀBQ)ᵢⱼ/2 uᵢuⱼ + ∑ᵢ (Qᵀb)ᵢuᵢ
theorem covKFormula_rot_tendsto (B b) : Tendsto (fun t => t ^ 2 * (Cov[L∘A, ψ] − covKFormula t H T B b)) atTop (𝓝 0)
-- also: mean_anharmonic_rate_div : |⟨x⟩ + α/(2λ²t)| ≤ K/t²
```

## Candidates

**A. Rates for the six pair covariances.** For `t ≥ T`: `|t² Cov[x², x²] − 2/λ²| ≤ K/t`, `|t² Cov[x³, x²]| ≤ K/t`,
`|t² Cov[x⁴, x²]| ≤ K/t`, `|t² Cov[x², x] + 2α/λ³| ≤ K/t`, `|t² Cov[x³, x] − 3/λ²| ≤ K/t`, `|t² Cov[x⁴, x]| ≤ K/t`.
Each is `gibbsCov_pow_pow` plus products of the sharp moment rates with explicit `1/t` factors, e.g.
`t² Cov[x³, x²] = (t³⟨x⁵⟩)/t − (t²⟨x³⟩)(t⟨x²⟩)/t`, `t² Cov[x⁴, x²] = (t³⟨x⁶⟩)/t − (t²⟨x⁴⟩)(t⟨x²⟩)/t`,
`t² Cov[x², x] = t²⟨x³⟩ − (t⟨x²⟩)(t⟨x⟩)`, `t² Cov[x³, x] = t²⟨x⁴⟩ − (t²⟨x³⟩)(t⟨x⟩)/t`, `t² Cov[x⁴, x] = (t³⟨x⁵⟩)/t − (t²⟨x⁴⟩)(t⟨x⟩)/t`,
`t² Cov[x², x²] = t²⟨x⁴⟩ − (t⟨x²⟩)²`. One generic lemma "product of two rated quantities": `|X − a| ≤ K/t`, `|Y − b| ≤ K'/t`, `t ≥ 1` ⟹
`|XY − ab| ≤ (K|b| + K'|a| + KK')/t`, and "rated quantity over `t`": `|X − a| ≤ K/t` ⟹ `|X/t| ≤ (|a| + K)/t`.

**B. The one-dimensional covK rate (E2's `1/t` for eq:covK).** `|t² Cov[ℓ, (B/2)x² + bx] − (B/(2λ) − bα/(2λ²))| ≤ K/t` for `t ≥ T`
(from `gibbsCov_anharmonic_left`, the integrability lemmas of the seabed, and A); equivalently `|Cov[ℓ, ψ] − covKOneDim(t)| ≤ K/t³`, and
the relative form `|Cov/covKOneDim − 1| ≤ K'/t` when the constant is nonzero.

**C. The separable and rotated rates.** `|t² Cov_L[L, ∑ᵢ (Bᵢ/2)uᵢ² + bᵢuᵢ] − ∑ᵢ (…)| ≤ K/t` (finite sum of B);
`|t² Cov_L[L, uᵢuⱼ]| ≤ K/t` for `i ≠ j` (from the exact identity: `⟨x⟩ⱼ = O(1/t)` and `t² Cov_i[ℓᵢ, x] = O(1)`);
`|t² Cov_L[L, ∑ᵢⱼ Bᵢⱼ/2 uᵢuⱼ + ∑ bᵢuᵢ] − ∑ᵢ (…)| ≤ K/t` (full quadratic probe); and in the note's frame
`|Cov[L∘A, ½(w−c)ᵀB(w−c) + bᵀ(w−c)] − covKFormula t H T B b| ≤ K/t³` for `t ≥ T`: eq:covK is exact to relative `O(1/t)`, E2's finding.

## Numerical check (`numcheck_covK_rate.py`, `λ = 2`, `a = ½`, `B = 3`, `b = 1.5`; and `d = 2` rotated with random `Q, c, B, b`)

`t·(t² Cov[ℓ, ψ] − C)` = `0.227, 0.243, 0.252, 0.256, 0.258` at `t = 50 … 800` (bounded); the six pair quantities `t·(t²Cov[x^m,x^n] − c_mn)`
converge to `−0.127, −1.32, 1.50, 0.666, −0.299, −1.41`; `d = 2`: `t·(t² Cov[L∘A, ψ] − C_d) = 0.102 … 0.074` (bounded).

## Questions

1. Are the pair constants in A right (`c₂₂ = 2/λ²`, `c₃₂ = c₄₂ = 0`, `c₂₁ = −2α/λ³`, `c₃₁ = 3/λ²`, `c₄₁ = 0`) and is the product-of-rates
   lemma the right organising tool, or is there a slicker route to B (e.g. directly from the moment rates through
   `Cov[ℓ, ψ] = ⟨ℓψ⟩ − ⟨ℓ⟩⟨ψ⟩` with `⟨ℓψ⟩` expanded into moments)?
2. The seabed's `t`-scalings differ by term (`t²⟨x⁴⟩`, `t³⟨x⁵⟩`, `t⟨x²⟩`, …): any pitfalls in bookkeeping the powers of `t` in Lean
   (we plan `field_simp`-free identities such as `t² ⟨x³⟩⟨x²⟩ = (t²⟨x³⟩)(t⟨x²⟩)/t`, proved by `ring` after `t ≠ 0`)?
3. Is C's `K/t³` statement for the rotated frame the right headline for E2's "including eq:covK", and is the relative form worth
   stating (it needs the constant `∑ᵢ (…)` nonzero)?
4. Scope and vote (A+B+C as one tide, or A+B with C to follow)?
