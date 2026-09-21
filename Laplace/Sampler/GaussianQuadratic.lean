/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Sampler.GaussianInvariance

/-!
# Gaussian quadratic expectations and the sampler's LLC under its invariant law

For a centred Gaussian `N(0, S)` on `EuclideanSpace ℝ ι`, `∫ xᵢ xⱼ = Sᵢⱼ` and
`∫ ⟨x, H x⟩ = tr(H S)`. Applied to the invariant law `N(0, Σ_ULA)` of the ULA step on the Gaussian
target with precision `P = t H`, this identifies the sampler's local learning coefficient
`t E[½⟨x, H x⟩]` with `½ ∑ᵢ 1/(1 - h pᵢ/2)` (`trace_mul_ulaCov`), against `d/2` under the Gibbs law
`N(0, P⁻¹)`: the note's "ULA-corrected LLC" as an expectation under the actual stationary law.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Second moments of a centred Gaussian**: `∫ xᵢ xⱼ = Sᵢⱼ`. -/
theorem integral_coord_mul_multivariateGaussian {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j : ι) :
    ∫ x, x.ofLp i * x.ofLp j ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) = S i j := by
  have h := covarianceBilin_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hS
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [covarianceBilin_apply IsGaussian.memLp_two_id] at h
  simp only [id_eq, integral_id_multivariateGaussian, sub_zero, EuclideanSpace.inner_single_left,
    conj_trivial, one_mul, EuclideanSpace.single] at h
  simpa using h

/-- `⟨x, H x⟩ = ∑ᵢⱼ Hᵢⱼ xᵢ xⱼ`. -/
theorem inner_euclid_eq_sum (H : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    inner ℝ x (euclid H x) = ∑ i, ∑ j, H i j * (x.ofLp i * x.ofLp j) := by
  rw [inner_toEuclideanCLM]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem integrable_coord_mul_multivariateGaussian {S : Matrix ι ι ℝ} (i j : ι) :
    Integrable (fun x : EuclideanSpace ℝ ι => x.ofLp i * x.ofLp j)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) := by
  have h2 : MemLp id 2 (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) := IsGaussian.memLp_two_id
  have hi : MemLp (fun x : EuclideanSpace ℝ ι => x.ofLp i) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' h2
  have hj : MemLp (fun x : EuclideanSpace ℝ ι => x.ofLp j) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' h2
  exact hi.integrable_mul hj

/-- **Gaussian quadratic expectation**: `∫ ⟨x, H x⟩ ∂N(0, S) = tr(H S)`. -/
theorem integral_inner_euclid_multivariateGaussian {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (H : Matrix ι ι ℝ) :
    ∫ x, inner ℝ x (euclid H x) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) =
      (H * S).trace := by
  simp_rw [inner_euclid_eq_sum]
  rw [integral_finsetSum Finset.univ
    (f := fun i (x : EuclideanSpace ℝ ι) => ∑ j, H i j * (x.ofLp i * x.ofLp j))
    fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_coord_mul_multivariateGaussian (S := S) i j).const_mul _]
  have hin : ∀ i, ∫ x, ∑ j, H i j * (x.ofLp i * x.ofLp j)
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) = ∑ j, H i j * S i j := by
    intro i
    rw [integral_finsetSum Finset.univ
      (f := fun j (x : EuclideanSpace ℝ ι) => H i j * (x.ofLp i * x.ofLp j))
      fun j _ => (integrable_coord_mul_multivariateGaussian (S := S) i j).const_mul _]
    simp_rw [integral_const_mul, integral_coord_mul_multivariateGaussian hS]
  simp_rw [hin]
  have hsym : ∀ i j, S i j = S j i := fun i j => by
    have := hS.1.apply i j
    simpa using this.symm
  simp only [Matrix.trace, Matrix.diag, mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym i j]

/-! ### With a mean -/

/-- The coordinate functional `x ↦ xᵢ` has mean `mᵢ` under `N(m, S)`. -/
theorem integral_coord_multivariateGaussian (S : Matrix ι ι ℝ) (m : EuclideanSpace ℝ ι) (i : ι) :
    ∫ x, x.ofLp i ∂(multivariateGaussian m S) = m.ofLp i := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (μ := multivariateGaussian m S) (φ := id) IsGaussian.integrable_id
  simp only [id, integral_id_multivariateGaussian] at h
  exact h

theorem integrable_coord_multivariateGaussian (S : Matrix ι ι ℝ) (m : EuclideanSpace ℝ ι)
    (i : ι) : Integrable (fun x : EuclideanSpace ℝ ι => x.ofLp i) (multivariateGaussian m S) :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (IsGaussian.memLp_two_id
    (μ := multivariateGaussian m S))).integrable (by norm_num)

theorem integrable_coord_mul_multivariateGaussian' (S : Matrix ι ι ℝ) (m : EuclideanSpace ℝ ι)
    (i j : ι) :
    Integrable (fun x : EuclideanSpace ℝ ι => x.ofLp i * x.ofLp j) (multivariateGaussian m S) :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (IsGaussian.memLp_two_id
    (μ := multivariateGaussian m S))).integrable_mul
    ((EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' IsGaussian.memLp_two_id)

/-- **Second moments with a mean**: `∫ xᵢ xⱼ ∂N(m, S) = Sᵢⱼ + mᵢ mⱼ`. -/
theorem integral_coord_mul_multivariateGaussian' {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (m : EuclideanSpace ℝ ι) (i j : ι) :
    ∫ x, x.ofLp i * x.ofLp j ∂(multivariateGaussian m S) = S i j + m.ofLp i * m.ofLp j := by
  have h := covarianceBilin_multivariateGaussian (μ := m) hS
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [covarianceBilin_apply IsGaussian.memLp_two_id] at h
  simp only [id_eq, integral_id_multivariateGaussian, EuclideanSpace.inner_single_left,
    conj_trivial, one_mul, EuclideanSpace.single, WithLp.ofLp_sub, Pi.sub_apply] at h
  have hexp : (fun x : EuclideanSpace ℝ ι => (x.ofLp i - m.ofLp i) * (x.ofLp j - m.ofLp j)) =
      fun x => x.ofLp i * x.ofLp j - m.ofLp j * x.ofLp i - m.ofLp i * x.ofLp j
        + m.ofLp i * m.ofLp j := by
    funext x; ring
  have hI1 := integrable_coord_mul_multivariateGaussian' S m i j
  have hI2 := (integrable_coord_multivariateGaussian S m i).const_mul (m.ofLp j)
  have hI3 := (integrable_coord_multivariateGaussian S m j).const_mul (m.ofLp i)
  have hI12 : Integrable (fun x : EuclideanSpace ℝ ι => x.ofLp i * x.ofLp j - m.ofLp j * x.ofLp i)
      (multivariateGaussian m S) := hI1.sub hI2
  have hI123 : Integrable (fun x : EuclideanSpace ℝ ι =>
      x.ofLp i * x.ofLp j - m.ofLp j * x.ofLp i - m.ofLp i * x.ofLp j) (multivariateGaussian m S) :=
    hI12.sub hI3
  rw [hexp, integral_add hI123 (integrable_const _), integral_sub hI12 hI3, integral_sub hI1 hI2,
    integral_const_mul, integral_const_mul, integral_const, integral_coord_multivariateGaussian,
    integral_coord_multivariateGaussian] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  have hrhs : (PiLp.single 2 i (1 : ℝ)).ofLp ⬝ᵥ S *ᵥ (PiLp.single 2 j (1 : ℝ)).ofLp = S i j := by
    simp
  rw [hrhs] at h
  linarith

/-- **Gaussian quadratic expectation with a mean**: `∫ ⟨x, H x⟩ ∂N(m, S) = tr(H S) + ⟨m, H m⟩`. -/
theorem integral_inner_euclid_multivariateGaussian' {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (m : EuclideanSpace ℝ ι) (H : Matrix ι ι ℝ) :
    ∫ x, inner ℝ x (euclid H x) ∂(multivariateGaussian m S) =
      (H * S).trace + inner ℝ m (euclid H m) := by
  simp_rw [inner_euclid_eq_sum]
  rw [integral_finsetSum Finset.univ
    (f := fun i (x : EuclideanSpace ℝ ι) => ∑ j, H i j * (x.ofLp i * x.ofLp j))
    fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_coord_mul_multivariateGaussian' S m i j).const_mul _]
  have hin : ∀ i, ∫ x, ∑ j, H i j * (x.ofLp i * x.ofLp j) ∂(multivariateGaussian m S) =
      ∑ j, H i j * (S i j + m.ofLp i * m.ofLp j) := by
    intro i
    rw [integral_finsetSum Finset.univ
      (f := fun j (x : EuclideanSpace ℝ ι) => H i j * (x.ofLp i * x.ofLp j))
      fun j _ => (integrable_coord_mul_multivariateGaussian' S m i j).const_mul _]
    simp_rw [integral_const_mul, integral_coord_mul_multivariateGaussian' hS]
  simp_rw [hin, mul_add, Finset.sum_add_distrib]
  have hsym : ∀ i j, S i j = S j i := fun i j => by
    have := hS.1.apply i j
    simpa using this.symm
  congr 1
  simp only [Matrix.trace, Matrix.diag, mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym i j]

/-! ### The sampler's LLC under the invariant law -/

/-- **The ULA-corrected LLC as an expectation under `N(0, Σ_ULA)`.** With precision `P = t • H`,
`t E[½⟨x, H x⟩] = ½ ∑ᵢ 1/(1 - h pᵢ/2)`. -/
theorem llc_ula_invariant {H : Matrix ι ι ℝ} {t h : ℝ} (hP : (t • H).PosDef) (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) :
    t * ∫ x, 1 / 2 * inner ℝ x (euclid H x)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) (ulaCov (t • H) h)) =
      1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2) := by
  rw [integral_const_mul,
    integral_inner_euclid_multivariateGaussian (ulaCov_posDef hP h hh hev).posSemidef H,
    ← ula_llc t h hP hh hev]
  ring

/-- **The LLC under the Gibbs law `N(0, P⁻¹)` is `d/2`.** -/
theorem llc_gibbs {H : Matrix ι ι ℝ} {t : ℝ} (ht : 0 < t) (hH : H.PosDef) :
    t * ∫ x, 1 / 2 * inner ℝ x (euclid H x)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) (t • H)⁻¹) =
      Fintype.card ι / 2 := by
  have hP : (t • H).PosDef := hH.smul ht
  have hdet : IsUnit H.det := isUnit_iff_ne_zero.mpr hH.det_pos.ne'
  have hinv : (t • H)⁻¹ = t⁻¹ • H⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht.ne', one_smul,
      Matrix.mul_nonsing_inv H hdet]
  rw [integral_const_mul,
    integral_inner_euclid_multivariateGaussian (Matrix.posDef_inv_iff.mpr hP).posSemidef H, hinv,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_nonsing_inv H hdet, Matrix.trace_one,
    smul_eq_mul]
  field_simp

/-- **The LLC transient from the mode.** After `k` ULA steps from a point mass at the mode, the
quadratic expectation is `tr(P Σ_k)` with `Σ_k` the covariance iterate from `0`. -/
theorem integral_inner_euclid_gaussStep_iterate {P R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    (A : Matrix ι ι ℝ) (k : ℕ) :
    ∫ x, inner ℝ x (euclid P x)
        ∂((gaussStep A R)^[k] (multivariateGaussian (0 : EuclideanSpace ℝ ι) 0)) =
      (P * (covStep A R)^[k] 0).trace := by
  rw [gaussStep_iterate Matrix.PosSemidef.zero hR A 0 k, map_zero,
    integral_inner_euclid_multivariateGaussian
      (covStep_iterate_posSemidef Matrix.PosSemidef.zero hR A k) P]

/-- **The ULA LLC transient**: `t E_k[½⟨x, H x⟩] = ½ tr(P (Σ_ULA - A^k Σ_ULA (Aᵀ)^k))` along the chain
from the mode, with `P = t • H`. -/
theorem llc_ula_trajectory {H : Matrix ι ι ℝ} {t h : ℝ} (hP : (t • H).PosDef) (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) (k : ℕ) :
    t * ∫ x, 1 / 2 * inner ℝ x (euclid H x)
        ∂((gaussStep (ulaStep (t • H) h) ((2 * h) • (1 : Matrix ι ι ℝ)))^[k]
          (multivariateGaussian (0 : EuclideanSpace ℝ ι) 0)) =
      1 / 2 * ((t • H) * (ulaCov (t • H) h -
        ulaStep (t • H) h ^ k * ulaCov (t • H) h * (ulaStep (t • H) h)ᵀ ^ k)).trace := by
  have hPt : (t • H)ᵀ = t • H := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hev' : ∀ i, 0 < hP.1.eigenvalues i ∧ h * hP.1.eigenvalues i < 2 :=
    fun i => ⟨hP.eigenvalues_pos i, hev i⟩
  have hfix : covStep (ulaStep (t • H) h) ((2 * h) • (1 : Matrix ι ι ℝ)) (ulaCov (t • H) h) =
      ulaCov (t • H) h :=
    ulaCov_fixed (t • H) h hPt (isUnit_det_ulaDenom hP.1 h hev')
  rw [integral_const_mul, integral_inner_euclid_gaussStep_iterate
    (Matrix.PosSemidef.one.smul (by positivity)) (ulaStep (t • H) h) k,
    covStep_iterate_zero _ _ _ hfix k, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

end Laplace.Sampler
