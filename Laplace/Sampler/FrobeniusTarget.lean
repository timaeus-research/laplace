/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.FrobeniusBridge

/-!
# E4 against its targets, in the original coordinates

The note's E4 measures the Frobenius error of the pooled ULA covariance `Σ̂_raw = (1/(CN)) ∑ x xᵀ`
against the ULA stationary covariance `Σ_ULA` and against the posterior covariance `Q⁻¹`.
`FrobeniusBridge` covers the *centred* error; this file adds the deterministic bias:

* `zeroStartFactor`, `zeroStartFactor_eq`, `zeroStartFactor_le`: the zero-start factor
  `aᵢ = (1/N) ∑_{k<N} ρᵢ^{2(b+1+k)}`, its geometric closed form
  `ρ^{2(b+1)} (1 − ρ^{2N}) / (N (1 − ρ²))` and the bound `aᵢ ≤ ρᵢ^{2(b+1)}`;
* `gram_ulaChain_eig`, `integral_pooledSecondMoment_ula`, `integral_pooledRaw`: the Gram table of
  the eigen-projections and the closed-form mean `E Σ̂_raw = U diag(s₂ᵢ (1 − aᵢ)) Uᵀ`;
* `frobenius_ula_target_raw_eq`: for any target `T = U diag(t) Uᵀ`,
  `E‖Σ̂_raw − T‖_F² = E‖Σ̂_raw − EΣ̂_raw‖_F² + ∑ᵢ (s₂ᵢ(1 − aᵢ) − tᵢ)²`;
* `frobenius_ula_target_raw` (`T = Σ_ULA`, bias `∑ᵢ (s₂ᵢ aᵢ)²`) and `frobenius_ula_posterior_raw`
  (`T = Q⁻¹`, bias `∑ᵢ (h/(2 − hpᵢ) − s₂ᵢ aᵢ)²`: discretisation inflation against zero-start
  deflation), with the E4 envelopes `_le` and the relative forms `_rel`.
-/

open Matrix Finset MeasureTheory ProbabilityTheory

namespace Laplace.Sampler

/-! ### The zero-start factor -/

section ZeroStart

/-- `aᵢ = (1/N) ∑_{k<N} ρ^{2(b+1+k)}`: the fraction of the stationary variance missing from the mean
of the zero-start pooled second moment over the draws `b+1, …, b+N`. -/
noncomputable def zeroStartFactor (ρ : ℝ) (N b : ℕ) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ range N, ρ ^ (2 * (b + 1 + k))

/-- Geometric closed form `aᵢ = ρ^{2(b+1)} (1 − ρ^{2N}) / (N (1 − ρ²))`. -/
theorem zeroStartFactor_eq {ρ : ℝ} (hρ : ρ ^ 2 ≠ 1) {N : ℕ} (hN : 0 < N) (b : ℕ) :
    zeroStartFactor ρ N b = ρ ^ (2 * (b + 1)) * (1 - ρ ^ (2 * N)) / (N * (1 - ρ ^ 2)) := by
  unfold zeroStartFactor
  have h1 : ∀ k, ρ ^ (2 * (b + 1 + k)) = ρ ^ (2 * (b + 1)) * (ρ ^ 2) ^ k := fun k => by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  simp_rw [h1]
  rw [← Finset.mul_sum, geom_sum_eq hρ, ← pow_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : ρ ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hρ
  have h3 : 1 - ρ ^ 2 ≠ 0 := fun h => h2 (by linarith)
  field_simp
  ring

theorem zeroStartFactor_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (N b : ℕ) : 0 ≤ zeroStartFactor ρ N b := by
  unfold zeroStartFactor
  positivity

/-- The zero-start factor is at most its first term: `aᵢ ≤ ρ^{2(b+1)}`. -/
theorem zeroStartFactor_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {N : ℕ} (hN : 0 < N) (b : ℕ) :
    zeroStartFactor ρ N b ≤ ρ ^ (2 * (b + 1)) := by
  unfold zeroStartFactor
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ k ∈ range N, ρ ^ (2 * (b + 1 + k)) ≤ ∑ _k ∈ range N, ρ ^ (2 * (b + 1)) :=
    Finset.sum_le_sum fun k _ => pow_le_pow_of_le_one hρ0 hρ1 (by omega)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  calc (1 / (N : ℝ)) * ∑ k ∈ range N, ρ ^ (2 * (b + 1 + k))
      ≤ (1 / (N : ℝ)) * (N * ρ ^ (2 * (b + 1))) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ρ ^ (2 * (b + 1)) := by field_simp

/-- The squared zero-start bias `(s aᵢ)² ≤ s² ρ^{4(b+1)}`. -/
theorem mul_zeroStartFactor_sq_le {ρ s : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {N : ℕ} (hN : 0 < N)
    (b : ℕ) : (s * zeroStartFactor ρ N b) ^ 2 ≤ s ^ 2 * ρ ^ (4 * (b + 1)) := by
  have ha0 := zeroStartFactor_nonneg hρ0 N b
  have ha1 := zeroStartFactor_le hρ0 hρ1 hN b
  calc (s * zeroStartFactor ρ N b) ^ 2 = s ^ 2 * zeroStartFactor ρ N b ^ 2 := by ring
    _ ≤ s ^ 2 * (ρ ^ (2 * (b + 1))) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 ha1 2) (sq_nonneg _)
    _ = s ^ 2 * ρ ^ (4 * (b + 1)) := by ring

end ZeroStart

/-! ### The targets in the eigenbasis -/

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Σ_ULA = U diag(1/(pᵢ(1 − h pᵢ/2))) Uᵀ`. -/
theorem ulaCov_eq_conj_diagonal {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hQ.1.eigenvalues i < 2) :
    ulaCov Q h = orthoOf hQ.1 *
      diagonal (fun i => 1 / (hQ.1.eigenvalues i * (1 - h * hQ.1.eigenvalues i / 2))) *
        (orthoOf hQ.1)ᵀ := by
  rw [← ulaCov_conj_eq_diagonal hQ.1 h hh (fun i => ⟨hQ.eigenvalues_pos i, hev i⟩)]
  have hUU' : orthoOf hQ.1 * (orthoOf hQ.1)ᵀ = 1 := orthoOf_mul_transpose hQ.1
  simp only [← Matrix.mul_assoc]
  rw [hUU', Matrix.one_mul, Matrix.mul_assoc, hUU', Matrix.mul_one]

/-- `Q⁻¹ = U diag(1/pᵢ) Uᵀ`. -/
theorem inv_eq_conj_diagonal {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) :
    Q⁻¹ = orthoOf hQ.1 * diagonal (fun i => 1 / hQ.1.eigenvalues i) * (orthoOf hQ.1)ᵀ := by
  rw [← orthoOf_transpose_inv_mul hQ]
  have hUU' : orthoOf hQ.1 * (orthoOf hQ.1)ᵀ = 1 := orthoOf_mul_transpose hQ.1
  simp only [← Matrix.mul_assoc]
  rw [hUU', Matrix.one_mul, Matrix.mul_assoc, hUU', Matrix.mul_one]

/-- The ULA discretisation bias `s₂ − 1/p = h/(2 − hp)`. -/
theorem ula_variance_sub_inv {h p : ℝ} (hh : 0 < h) (hp : 0 < p) (hev : h * p < 2) :
    2 * h / (1 - (1 - h * p) ^ 2) - 1 / p = h / (2 - h * p) := by
  have h1 : 1 - (1 - h * p) ^ 2 ≠ 0 := by nlinarith [mul_pos hh hp]
  have h2 : 2 - h * p ≠ 0 := by linarith
  field_simp
  ring

end Algebra

/-! ### The ULA chain -/

section Target

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The Gram table of the eigen-projections of the ULA chain**:
`E[⟨uᵢ, x^c_k⟩ ⟨uⱼ, x^{c'}_l⟩] = δ_{cc'} δᵢⱼ s₂ᵢ (ρᵢ^{|k−l|} − ρᵢ^{k+l})`. -/
theorem gram_ulaChain_eig {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hQ.1.eigenvalues i < 2) {C : ℕ}
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (c c' : Fin C) (i j : ι) (k l : ℕ) :
    ∫ ω, inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω) *
        inner ℝ (orthoCol hQ.1 j) (ulaChain Q h (ξ c') l ω) ∂P =
      if c = c' ∧ i = j then 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        ((1 - h * hQ.1.eigenvalues i) ^ Nat.dist k l - (1 - h * hQ.1.eigenvalues i) ^ (k + l))
      else 0 := by
  have hQt : Qᵀ = Q := by
    have := hQ.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hT := fourthMomentTable_projNoise_dir hh.le (orthonormal_orthoCol hQ.1) ξ hmeas hlaw hind
  have hwhite : ∀ c c' k l i j, ∫ ω, projNoise h (orthoCol hQ.1 i) (ξ c) k ω *
      projNoise h (orthoCol hQ.1 j) (ξ c') l ω ∂P =
      if c = c' ∧ k = l ∧ i = j then 2 * h else 0 := fun c c' k l i j => by
    simpa [Prod.ext_iff] using hT.white (c, k, i) (c', l, j)
  have hρ : ∀ i, (1 - h * hQ.1.eigenvalues i) ^ 2 ≠ 1 := fun i heq => by
    nlinarith [mul_pos hh (hQ.eigenvalues_pos i), hev i]
  have e : ∀ c i k ω, inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω) =
      realChain (1 - h * hQ.1.eigenvalues i) (fun m => projNoise h (orthoCol hQ.1 i) (ξ c) m) k ω :=
    fun c i k ω => inner_ulaChain_eq_realChain hQt h (mulVec_orthoCol hQ.1 i) (ξ c) k ω
  simp_rw [e]
  exact gram_realChain_dir (fun c k i => projNoise h (orthoCol hQ.1 i) (ξ c) k)
    (fun i => 1 - h * hQ.1.eigenvalues i) hρ
    (fun c k i => (hT.memLp (c, k, i)).mono_exponent (by norm_num)) hwhite c c' i j k l

/-- **The mean of the eigen-projected pooled second-moment matrix**:
`E Σ̂_eig,ij = δᵢⱼ s₂ᵢ (1 − aᵢ)`. -/
theorem integral_pooledSecondMoment_ula {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hQ.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (i j : ι) :
    ∫ ω, pooledSecondMoment
        (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω ∂P =
      if i = j then 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        (1 - zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b) else 0 := by
  have hL4 : ∀ c i k, k ∈ range N →
      MemLp (fun ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) (b + 1 + k) ω)) 4 P :=
    fun c i k _ => memLp_four_inner_ulaChain_Q hQ hh.le ξ hmeas hlaw hind c i (b + 1 + k)
  rw [integral_pooledSecondMoment hC hN b hL4
    (fun i k l => 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
      ((1 - h * hQ.1.eigenvalues i) ^ Nat.dist k l - (1 - h * hQ.1.eigenvalues i) ^ (k + l)))
    (gram_ulaChain_eig hQ hh hev ξ hmeas hlaw hind)]
  by_cases hij : i = j
  · subst hij
    simp only [if_true, Nat.dist_self, pow_zero, ← two_mul, zeroStartFactor]
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    field_simp
  · simp [hij]

/-- **The mean of the raw pooled covariance**: `E Σ̂_raw = U diag(s₂ᵢ (1 − aᵢ)) Uᵀ`. -/
theorem integral_pooledRaw {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hQ.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    Matrix.of (fun a a' => ∫ ω, pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' ∂P) =
      orthoOf hQ.1 * diagonal (fun i => 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        (1 - zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b)) * (orthoOf hQ.1)ᵀ := by
  have hD : Matrix.of (fun i j => ∫ ω, pooledSecondMoment
      (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω ∂P) =
      diagonal (fun i => 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        (1 - zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b)) := by
    ext i j
    rw [Matrix.of_apply, integral_pooledSecondMoment_ula hQ hh hev hC hN b ξ hmeas hlaw hind i j,
      diagonal_apply]
  ext a a'
  rw [Matrix.of_apply, integral_pooledRaw_apply hQ hh.le ξ hmeas hlaw hind N b a a', hD]

omit [DecidableEq ι] in
/-- **The Frobenius error against a deterministic target** is the centred error plus the squared
bias: `E ∑ᵢⱼ (Sᵢⱼ − Mᵢⱼ)² = E ∑ᵢⱼ (Sᵢⱼ − ESᵢⱼ)² + ∑ᵢⱼ (ESᵢⱼ − Mᵢⱼ)²`. -/
theorem integral_sum_sq_sub_eq_centred (S : ι → ι → Ω → ℝ) (M : ι → ι → ℝ)
    (h1 : ∀ i j, Integrable (S i j) P) (h2 : ∀ i j, Integrable (fun ω => S i j ω ^ 2) P) :
    ∫ ω, ∑ i, ∑ j, (S i j ω - M i j) ^ 2 ∂P =
      ∫ ω, ∑ i, ∑ j, (S i j ω - ∫ ω', S i j ω' ∂P) ^ 2 ∂P +
        ∑ i, ∑ j, (∫ ω, S i j ω ∂P - M i j) ^ 2 := by
  rw [integral_sum_sq_sub_eq S M h1 h2, integral_sum_sq_sub_eq S _ h1 h2]
  simp only [sub_self, zero_pow two_ne_zero, Finset.sum_const_zero, add_zero]

/-- **Frobenius error against a deterministic target sharing the eigenbasis**: for
`T = U diag(t) Uᵀ`, `E‖Σ̂_raw − T‖_F² = E‖Σ̂_raw − EΣ̂_raw‖_F² + ∑ᵢ (s₂ᵢ(1 − aᵢ) − tᵢ)²`. -/
theorem frobenius_ula_target_raw_eq {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hQ.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (t : ι → ℝ) :
    ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        (orthoOf hQ.1 * diagonal t * (orthoOf hQ.1)ᵀ) a a') ^ 2 ∂P =
      ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P) ^ 2 ∂P +
      ∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        (1 - zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b) - t i) ^ 2 := by
  have hL4 : ∀ c i k, k ∈ range N →
      MemLp (fun ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) (b + 1 + k) ω)) 4 P :=
    fun c i k _ => memLp_four_inner_ulaChain_Q hQ hh.le ξ hmeas hlaw hind c i (b + 1 + k)
  have hmem : ∀ i j, MemLp (pooledSecondMoment
      (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j) 2 P :=
    fun i j => (memLp_two_iff_integrable_sq
      (integrable_pooledSecondMoment hL4 i j).aestronglyMeasurable).mpr
      (integrable_pooledSecondMoment_sq hL4 i j)
  have h1 : ∀ a a', Integrable
      (fun ω => pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a') P :=
    fun a a' => integrable_pooledRaw_apply hQ hh.le ξ hmeas hlaw hind N b a a'
  have h2 : ∀ a a', Integrable
      (fun ω => pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' ^ 2) P := fun a a' => by
    have hraw : MemLp (fun ω => pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a') 2 P := by
      simp_rw [pooledRaw_apply_eq_sum hQ.1]
      exact memLp_finsetSum _ fun j _ =>
        (memLp_finsetSum _ fun i _ => (hmem i j).const_mul _).mul_const _
    exact hraw.integrable_sq
  refine (integral_sum_sq_sub_eq_centred _ _ h1 h2).trans ?_
  congr 1
  set D : Matrix ι ι ℝ := diagonal (fun i => 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
    (1 - zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b) - t i) with hD
  have hM : ∀ a a', (∫ ω, pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' ∂P) -
      (orthoOf hQ.1 * diagonal t * (orthoOf hQ.1)ᵀ) a a' =
      (orthoOf hQ.1 * D * (orthoOf hQ.1)ᵀ) a a' := by
    intro a a'
    have := congrFun (congrFun (integral_pooledRaw hQ hh hev hC hN b ξ hmeas hlaw hind) a) a'
    rw [Matrix.of_apply] at this
    rw [this, ← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  simp_rw [hM]
  have hUU : (orthoOf hQ.1)ᵀ * orthoOf hQ.1 = 1 := orthoOf_transpose_mul hQ.1
  have hc := sum_sq_conj D (orthoOf hQ.1)ᵀ (by rw [transpose_transpose]; exact hUU)
  rw [transpose_transpose] at hc
  rw [hc, hD, sum_sq_diagonal]

/-- **E4 against `Σ_ULA`, exactly**:
`E‖Σ̂_raw − Σ_ULA‖_F² = E‖Σ̂_raw − EΣ̂_raw‖_F² + ∑ᵢ (s₂ᵢ aᵢ)²`. -/
theorem frobenius_ula_target_raw {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hQ.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ulaCov Q h a a') ^ 2 ∂P =
      ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P) ^ 2 ∂P +
      ∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b) ^ 2 := by
  rw [ulaCov_eq_conj_diagonal hQ hh hev,
    frobenius_ula_target_raw_eq hQ hh hev hC hN b ξ hmeas hlaw hind]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ula_variance_eq hh (hQ.eigenvalues_pos i) (hev i)]
  ring

/-- **E4 against the posterior covariance `Q⁻¹`, exactly**:
`E‖Σ̂_raw − Q⁻¹‖_F² = E‖Σ̂_raw − EΣ̂_raw‖_F² + ∑ᵢ (h/(2 − hpᵢ) − s₂ᵢ aᵢ)²`: the discretisation
inflation `s₂ᵢ − 1/pᵢ = h/(2 − hpᵢ)` and the zero-start deflation `s₂ᵢ aᵢ` partly cancel. -/
theorem frobenius_ula_posterior_raw {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hQ.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        Q⁻¹ a a') ^ 2 ∂P =
      ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P) ^ 2 ∂P +
      ∑ i, (h / (2 - h * hQ.1.eigenvalues i) - 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b) ^ 2 := by
  rw [inv_eq_conj_diagonal hQ, frobenius_ula_target_raw_eq hQ hh hev hC hN b ξ hmeas hlaw hind]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ula_variance_sub_inv hh (hQ.eigenvalues_pos i) (hev i)]
  ring

/-- **E4 envelope against `Σ_ULA`**: the centred envelope of `frobenius_ula_le_raw` plus the
zero-start bias `∑ᵢ s₂ᵢ² ρᵢ^{4(b+1)}`. -/
theorem frobenius_ula_target_raw_le {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hstab : ∀ i, h * hQ.1.eigenvalues i ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ulaCov Q h a a') ^ 2 ∂P ≤
      ∑ i, ∑ j, (if i = j then 2 else 1) / (C * N) *
        (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
          (2 * h / (1 - (1 - h * hQ.1.eigenvalues j) ^ 2)) *
          (1 + (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) /
          (1 - (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j))) +
      ∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2)) ^ 2 *
        (1 - h * hQ.1.eigenvalues i) ^ (4 * (b + 1)) := by
  have hev : ∀ i, h * hQ.1.eigenvalues i < 2 := fun i => by linarith [hstab i]
  rw [frobenius_ula_target_raw hQ hh hev hC hN b ξ hmeas hlaw hind]
  refine add_le_add (frobenius_ula_le_raw hQ hh hstab hC hN b ξ hmeas hlaw hind)
    (Finset.sum_le_sum fun i _ => ?_)
  exact mul_zeroStartFactor_sq_le (by linarith [hstab i])
    (by linarith [mul_pos hh (hQ.eigenvalues_pos i)]) hN b

/-- **E4 envelope against `Q⁻¹`**: the centred envelope plus the discretisation bias
`∑ᵢ (h/(2 − hpᵢ))²` plus the zero-start bias `∑ᵢ s₂ᵢ² ρᵢ^{4(b+1)}`. -/
theorem frobenius_ula_posterior_raw_le {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hstab : ∀ i, h * hQ.1.eigenvalues i ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        Q⁻¹ a a') ^ 2 ∂P ≤
      ∑ i, ∑ j, (if i = j then 2 else 1) / (C * N) *
        (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
          (2 * h / (1 - (1 - h * hQ.1.eigenvalues j) ^ 2)) *
          (1 + (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) /
          (1 - (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j))) +
      ∑ i, ((h / (2 - h * hQ.1.eigenvalues i)) ^ 2 +
        (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2)) ^ 2 *
          (1 - h * hQ.1.eigenvalues i) ^ (4 * (b + 1))) := by
  have hev : ∀ i, h * hQ.1.eigenvalues i < 2 := fun i => by linarith [hstab i]
  rw [frobenius_ula_posterior_raw hQ hh hev hC hN b ξ hmeas hlaw hind]
  refine add_le_add (frobenius_ula_le_raw hQ hh hstab hC hN b ξ hmeas hlaw hind)
    (Finset.sum_le_sum fun i _ => ?_)
  have hp := hQ.eigenvalues_pos i
  have hρ0 : 0 ≤ 1 - h * hQ.1.eigenvalues i := by linarith [hstab i]
  have hd : 0 ≤ h / (2 - h * hQ.1.eigenvalues i) := div_nonneg hh.le (by linarith [hstab i])
  have hs : 0 ≤ 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) :=
    div_nonneg (by positivity) (by nlinarith [mul_pos hh hp, hstab i])
  have hy : 0 ≤ 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
      zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b :=
    mul_nonneg hs (zeroStartFactor_nonneg hρ0 N b)
  have hy' := mul_zeroStartFactor_sq_le (s := 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2)) hρ0
    (by linarith [mul_pos hh hp]) hN b
  nlinarith [mul_nonneg hd hy]

/-- E4's relative error against `Q⁻¹`, with `‖Q⁻¹‖_F² = ∑ᵢ 1/pᵢ²`. -/
theorem frobenius_ula_posterior_raw_rel {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hQ.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    (∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        Q⁻¹ a a') ^ 2 ∂P) / ∑ a, ∑ a', (Q⁻¹) a a' ^ 2 =
      (∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P) ^ 2 ∂P +
      ∑ i, (h / (2 - h * hQ.1.eigenvalues i) - 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b) ^ 2) /
      ∑ i, (1 / hQ.1.eigenvalues i) ^ 2 := by
  rw [frobenius_ula_posterior_raw hQ hh hev hC hN b ξ hmeas hlaw hind, frobenius_inv hQ]

/-- E4's relative error against `Σ_ULA`, with `‖Σ_ULA‖_F² = ∑ᵢ (1/(pᵢ(1 − hpᵢ/2)))²`. -/
theorem frobenius_ula_target_raw_rel {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hQ.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    (∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ulaCov Q h a a') ^ 2 ∂P) / ∑ a, ∑ a', ulaCov Q h a a' ^ 2 =
      (∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P) ^ 2 ∂P +
      ∑ i, (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
        zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b) ^ 2) /
      ∑ i, (1 / (hQ.1.eigenvalues i * (1 - h * hQ.1.eigenvalues i / 2))) ^ 2 := by
  rw [frobenius_ula_target_raw hQ hh hev hC hN b ξ hmeas hlaw hind, frobenius_ulaCov hQ h hh hev]

end Target

end Laplace.Sampler
