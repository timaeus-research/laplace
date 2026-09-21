/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.GaussianTable
import Laplace.Sampler.LLCSensitivity
import Laplace.Sampler.LLCMSE
import Laplace.Sampler.LocalisedLLC

/-!
# Frobenius bridges: E4 in the original coordinates

The E4 covariance theorems (`frobenius_ula_le` and its corollaries) are stated for the pooled
second-moment matrix of the eigen-projections `⟨uᵢ, x_k⟩`, with Frobenius errors written as
`∑ᵢⱼ (Σ̂ᵢⱼ − EΣ̂ᵢⱼ)²` and target norms as eigenvalue sums. This file supplies the bridges to the
coordinates the chain runs in:

* `sum_sq_eq_trace`, `sum_sq_conj`, `sum_sq_diagonal`: `∑ᵢⱼ Aᵢⱼ² = tr(AᵀA)` and its
  orthogonal invariance `∑ᵢⱼ (UᵀAU)ᵢⱼ² = ∑ᵢⱼ Aᵢⱼ²`;
* `frobenius_ulaCov`, `frobenius_inv`: `‖Σ_ULA‖_F² = ∑ᵢ (1/(pᵢ(1 − h pᵢ/2)))²`,
  `‖P⁻¹‖_F² = ∑ᵢ 1/pᵢ²`;
* `pooledRaw`, `pooledEig_eq_conj`, `pooledRaw_eq_conj`: the eigen-projected estimator is
  `Uᵀ Σ̂_raw U` pointwise; `integral_pooledRaw_apply`: `E Σ̂_raw = U (E Σ̂_eig) Uᵀ`;
  `frobenius_error_raw_eq_eig`: the centred Frobenius sums in the two bases agree;
* `frobenius_ula_le_raw`: **E4 for the raw-coordinate pooled covariance** of the ULA chain.
-/

open Matrix Finset MeasureTheory ProbabilityTheory

namespace Laplace.Sampler

/-! ### Frobenius algebra -/

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `∑ᵢⱼ Aᵢⱼ² = tr(AᵀA)`. -/
theorem sum_sq_eq_trace (A : Matrix ι ι ℝ) : ∑ i, ∑ j, A i j ^ 2 = (Aᵀ * A).trace := by
  rw [← sum_mul_apply_eq_trace]
  simp_rw [sq]

/-- **Orthogonal invariance of the Frobenius norm**: `∑ᵢⱼ (UᵀAU)ᵢⱼ² = ∑ᵢⱼ Aᵢⱼ²` for `UUᵀ = 1`. -/
theorem sum_sq_conj (A U : Matrix ι ι ℝ) (hUU' : U * Uᵀ = 1) :
    ∑ i, ∑ j, (Uᵀ * A * U) i j ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [sum_sq_eq_trace, sum_sq_eq_trace]
  have e : (Uᵀ * A * U)ᵀ * (Uᵀ * A * U) = Uᵀ * (Aᵀ * A) * U := by
    rw [transpose_mul, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᵀ, hUU', Matrix.one_mul]
  rw [e, Matrix.trace_mul_cycle, hUU', Matrix.one_mul]

/-- `∑ᵢⱼ (diag d)ᵢⱼ² = ∑ᵢ dᵢ²`. -/
theorem sum_sq_diagonal (d : ι → ℝ) : ∑ i, ∑ j, (diagonal d) i j ^ 2 = ∑ i, d i ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [diagonal_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

/-- `‖P⁻¹‖_F² = ∑ᵢ 1/pᵢ²`. -/
theorem frobenius_inv {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    ∑ i, ∑ j, (P⁻¹) i j ^ 2 = ∑ i, (1 / hP.1.eigenvalues i) ^ 2 := by
  rw [← sum_sq_conj P⁻¹ (orthoOf hP.1) (orthoOf_mul_transpose hP.1),
    orthoOf_transpose_inv_mul hP, sum_sq_diagonal]

/-- `‖Σ_ULA‖_F² = ∑ᵢ (1/(pᵢ(1 − h pᵢ/2)))²`. -/
theorem frobenius_ulaCov {P : Matrix ι ι ℝ} (hP : P.PosDef) (h : ℝ) (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) :
    ∑ i, ∑ j, (ulaCov P h) i j ^ 2 =
      ∑ i, (1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2))) ^ 2 := by
  rw [← sum_sq_conj (ulaCov P h) (orthoOf hP.1) (orthoOf_mul_transpose hP.1),
    ulaCov_conj_eq_diagonal hP.1 h hh (fun i => ⟨hP.eigenvalues_pos i, hev i⟩), sum_sq_diagonal]

end Algebra

/-! ### The estimator bridge -/

section Estimator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [DecidableEq ι] in
/-- `(Uᵀx)(Uᵀx)ᵀ = Uᵀ (x xᵀ) U`. -/
theorem vecMulVec_transpose_mulVec (U : Matrix ι ι ℝ) (x : ι → ℝ) :
    vecMulVec (Uᵀ *ᵥ x) (Uᵀ *ᵥ x) = Uᵀ * vecMulVec x x * U := by
  ext i j
  simp only [vecMulVec_apply, mulVec, dotProduct, Matrix.mul_apply, transpose_apply]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- `⟨orthoCol hQ i, v⟩ = (Uᵀ v)ᵢ`. -/
theorem inner_orthoCol_eq_mulVec {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) (i : ι)
    (v : EuclideanSpace ℝ ι) :
    inner ℝ (orthoCol hQ i) v = ((orthoOf hQ)ᵀ *ᵥ v.ofLp) i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [orthoCol, WithLp.ofLp_toLp, mulVec, dotProduct, transpose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- The raw pooled second-moment matrix `(1/(CN)) ∑_c ∑_{k<N} x xᵀ` over the draws
`b+1, …, b+N`. -/
noncomputable def pooledRaw {C : ℕ} (y : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (N b : ℕ) (ω : Ω) :
    Matrix ι ι ℝ :=
  (1 / ((C : ℝ) * N)) •
    ∑ c, ∑ k ∈ range N, vecMulVec (y c (b + 1 + k) ω).ofLp (y c (b + 1 + k) ω).ofLp

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] in
/-- The entries of `pooledRaw` are the pooled second moments of the raw coordinates. -/
theorem pooledRaw_apply {C : ℕ} (y : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (N b : ℕ) (ω : Ω)
    (a a' : ι) :
    pooledRaw y N b ω a a' = pooledSecondMoment (fun c a k ω => y c k ω a) N b a a' ω := by
  simp only [pooledRaw, pooledSecondMoment, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
    smul_eq_mul]

omit [MeasurableSpace Ω] in
/-- **The eigen-projected pooled second-moment matrix is the conjugate of the raw one**, pointwise:
`Σ̂_eig(ω) = Uᵀ Σ̂_raw(ω) U`. -/
theorem pooledEig_eq_conj {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) {C : ℕ}
    (y : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (N b : ℕ) (ω : Ω) :
    Matrix.of (fun i j =>
        pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hQ i) (y c k ω)) N b i j ω) =
      (orthoOf hQ)ᵀ * pooledRaw y N b ω * orthoOf hQ := by
  ext i j
  simp only [Matrix.of_apply, pooledSecondMoment, inner_orthoCol_eq_mulVec]
  have : ∀ c k, ((orthoOf hQ)ᵀ *ᵥ (y c (b + 1 + k) ω).ofLp) i *
      ((orthoOf hQ)ᵀ *ᵥ (y c (b + 1 + k) ω).ofLp) j =
      ((orthoOf hQ)ᵀ * vecMulVec (y c (b + 1 + k) ω).ofLp (y c (b + 1 + k) ω).ofLp * orthoOf hQ)
        i j := fun c k => by
    rw [← vecMulVec_transpose_mulVec, vecMulVec_apply]
  simp_rw [this]
  rw [pooledRaw, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]

omit [MeasurableSpace Ω] in
/-- `Σ̂_raw = U Σ̂_eig Uᵀ`. -/
theorem pooledRaw_eq_conj {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) {C : ℕ}
    (y : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (N b : ℕ) (ω : Ω) :
    pooledRaw y N b ω = orthoOf hQ * Matrix.of (fun i j =>
        pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hQ i) (y c k ω)) N b i j ω) *
      (orthoOf hQ)ᵀ := by
  rw [pooledEig_eq_conj hQ y N b ω]
  have hUU' : orthoOf hQ * (orthoOf hQ)ᵀ = 1 := orthoOf_mul_transpose hQ
  simp only [← Matrix.mul_assoc]
  rw [hUU', Matrix.one_mul, Matrix.mul_assoc, hUU', Matrix.mul_one]

omit [IsProbabilityMeasure P] in
/-- The eigen-projections of the ULA chain for a positive definite precision `Q` are in `L⁴`. -/
theorem memLp_four_inner_ulaChain_Q {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 ≤ h) {C : ℕ}
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (c : Fin C) (i : ι) (k : ℕ) :
    MemLp (fun ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) 4 P := by
  have hQt : Qᵀ = Q := by
    have := hQ.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hx : (fun ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) =
      realChain (1 - h * hQ.1.eigenvalues i)
        (fun m => projNoise h (orthoCol hQ.1 i) (ξ c) m) k := by
    funext ω
    exact inner_ulaChain_eq_realChain hQt h (mulVec_orthoCol hQ.1 i) (ξ c) k ω
  rw [hx]
  exact memLp_of_isLinComb
    (fourthMomentTable_projNoise_dir hh (orthonormal_orthoCol hQ.1) ξ hmeas hlaw hind).memLp
    (isLinComb_realChain_dir _ (fun c k i => projNoise h (orthoCol hQ.1 i) (ξ c) k) c i k k le_rfl)

omit [MeasurableSpace Ω] in
/-- The raw entries as linear combinations of the eigen entries, pointwise. -/
theorem pooledRaw_apply_eq_sum {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) {C : ℕ}
    (y : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (N b : ℕ) (ω : Ω) (a a' : ι) :
    pooledRaw y N b ω a a' = ∑ j, (∑ i, orthoOf hQ a i *
      pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hQ i) (y c k ω)) N b i j ω) *
        orthoOf hQ a' j := by
  rw [pooledRaw_eq_conj hQ y N b ω]
  simp only [Matrix.mul_apply, Matrix.of_apply, transpose_apply]

/-- The raw entries of the ULA pooled covariance are integrable. -/
theorem integrable_pooledRaw_apply {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 ≤ h) {C : ℕ}
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (N b : ℕ) (a a' : ι) :
    Integrable (fun ω => pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a') P := by
  simp_rw [pooledRaw_apply_eq_sum hQ.1]
  exact integrable_finsetSum _ fun j _ => (integrable_finsetSum _ fun i _ =>
    (integrable_pooledSecondMoment
      (fun c i k _ => memLp_four_inner_ulaChain_Q hQ hh ξ hmeas hlaw hind c i (b + 1 + k)) i j
      ).const_mul _).mul_const _

/-- `E Σ̂_raw = U (E Σ̂_eig) Uᵀ` entrywise. -/
theorem integral_pooledRaw_apply {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 ≤ h) {C : ℕ}
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (N b : ℕ) (a a' : ι) :
    ∫ ω, pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' ∂P =
      (orthoOf hQ.1 * Matrix.of (fun i j => ∫ ω, pooledSecondMoment
        (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω ∂P) *
          (orthoOf hQ.1)ᵀ) a a' := by
  have hL4 : ∀ c i k, k ∈ range N →
      MemLp (fun ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) (b + 1 + k) ω)) 4 P :=
    fun c i k _ => memLp_four_inner_ulaChain_Q hQ hh ξ hmeas hlaw hind c i (b + 1 + k)
  simp_rw [pooledRaw_apply_eq_sum hQ.1]
  simp only [Matrix.mul_apply, Matrix.of_apply, transpose_apply]
  rw [integral_finsetSum _ fun j _ => (integrable_finsetSum _ fun i _ =>
    (integrable_pooledSecondMoment hL4 i j).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_finsetSum _ fun i _ =>
    (integrable_pooledSecondMoment hL4 i j).const_mul _]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]

/-- **The centred Frobenius sums agree in the two bases**, pointwise:
`∑ₐₐ' (Σ̂_raw − EΣ̂_raw)ₐₐ'² = ∑ᵢⱼ (Σ̂_eig − EΣ̂_eig)ᵢⱼ²`. -/
theorem frobenius_error_raw_eq_eig {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 ≤ h) {C : ℕ}
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (N b : ℕ) (ω : Ω) :
    ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P) ^ 2 =
      ∑ i, ∑ j, (pooledSecondMoment
          (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω -
        ∫ ω', pooledSecondMoment
          (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω' ∂P) ^ 2
      := by
  set E : Matrix ι ι ℝ := Matrix.of (fun i j => pooledSecondMoment
    (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω) with hE
  set M : Matrix ι ι ℝ := Matrix.of (fun i j => ∫ ω', pooledSecondMoment
    (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω' ∂P) with hM
  have hraw : ∀ a a', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
      ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P =
      (orthoOf hQ.1 * (E - M) * (orthoOf hQ.1)ᵀ) a a' := by
    intro a a'
    rw [integral_pooledRaw_apply hQ hh ξ hmeas hlaw hind N b a a', pooledRaw_eq_conj hQ.1,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
  have heig : ∀ i j, pooledSecondMoment
      (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω -
      ∫ ω', pooledSecondMoment
        (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω' ∂P =
      (E - M) i j := fun i j => by
    rw [Matrix.sub_apply, hE, hM, Matrix.of_apply, Matrix.of_apply]
  simp_rw [hraw, heig]
  have hUU : (orthoOf hQ.1)ᵀ * orthoOf hQ.1 = 1 := orthoOf_transpose_mul hQ.1
  have := sum_sq_conj (E - M) (orthoOf hQ.1)ᵀ (by rw [transpose_transpose]; exact hUU)
  rw [transpose_transpose] at this
  exact this

/-- **E4 for the raw-coordinate pooled covariance of the ULA chain**: the bound of
`frobenius_ula_le` holds verbatim for `Σ̂_raw = (1/(CN)) ∑_c ∑_k x xᵀ`. -/
theorem frobenius_ula_le_raw {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hstab : ∀ i, h * hQ.1.eigenvalues i ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P) ^ 2 ∂P ≤
      ∑ i, ∑ j, (if i = j then 2 else 1) / (C * N) *
        (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
          (2 * h / (1 - (1 - h * hQ.1.eigenvalues j) ^ 2)) *
          (1 + (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) /
          (1 - (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j))) := by
  have e : (fun ω => ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
      ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P) ^ 2) =
      fun ω => ∑ i, ∑ j, (pooledSecondMoment
          (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω -
        ∫ ω', pooledSecondMoment
          (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω' ∂P) ^ 2 :=
    funext fun ω => frobenius_error_raw_eq_eig hQ hh.le ξ hmeas hlaw hind N b ω
  rw [e]
  exact frobenius_ula_le hQ hh hstab hC hN b ξ hmeas hlaw hind

end Estimator

end Laplace.Sampler
