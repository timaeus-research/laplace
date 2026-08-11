/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.QuadGaussian

/-!
# Moments of the quadratic Gaussian

Stage H2b of the multivariate programme, third installment: the first
moments of `K_H` vanish and the normalized second moments recover
`H⁻¹`. The route is the inverse whitening map `C = (√H)⁻¹`: under
`x = C·y` the coordinate observables become finite linear
combinations of the standard coordinates, so the H2a delta-form
moments contract the double sum to `Σ_a C_{ia} C_{ja} = (H⁻¹)_{ij}`.
The opaque Jacobian and the standard partition value cancel in the
normalized statement.
-/

open Real MeasureTheory Matrix
open scoped MatrixOrder

namespace Laplace.Multi

variable {d : ℕ}

/-- The inverse whitening map `C = (√H)⁻¹`. -/
noncomputable def whiteningInv (H : Matrix (Fin d) (Fin d) ℝ) :
    EuclidD d →L[ℝ] EuclidD d :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt H)⁻¹

/-- The square root's determinant is a unit. -/
theorem sqrt_det_isUnit {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) : IsUnit (CFC.sqrt H).det :=
  isUnit_iff_ne_zero.mpr (sqrt_posDef hH).det_pos.ne'

/-- The inverse whitening map undoes the whitening map. -/
theorem whiteningInv_whitening {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (x : EuclidD d) :
    whiteningInv H (whitening H x) = x := by
  unfold whiteningInv whitening
  rw [← ContinuousLinearMap.mul_apply, ← map_mul,
    Matrix.nonsing_inv_mul _ (sqrt_det_isUnit hH), map_one,
    ContinuousLinearMap.one_apply]

/-- Coordinates of the inverse whitening map as finite sums. -/
theorem whiteningInv_coord (H : Matrix (Fin d) (Fin d) ℝ)
    (y : EuclidD d) (i : Fin d) :
    whiteningInv H y i = ∑ a, (CFC.sqrt H)⁻¹ i a * y a := by
  unfold whiteningInv
  simp [Matrix.mulVec, dotProduct]

/-- Linear observables integrate to zero against the standard
kernel. -/
theorem integral_coordFn_mul_stdKernel (c : Fin d → ℝ) :
    ∫ y : EuclidD d, (∑ a, c a * y a) * stdKernel y = 0 := by
  have hpt : ∀ y : EuclidD d,
      (∑ a, c a * y a) * stdKernel y =
        ∑ a, c a * (y a * stdKernel y) := by
    intro y
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finset_sum _
      (fun a _ ↦ (stdKernel_integrable_coord a).const_mul (c a))]
  simp [integral_const_mul, integral_coord_mul_stdKernel]

/-- Products of two linear observables integrate to the contracted
Gram pairing against the standard kernel. -/
theorem integral_coordFn_mul_coordFn_stdKernel (c e : Fin d → ℝ) :
    ∫ y : EuclidD d,
        (∑ a, c a * y a) * (∑ b, e b * y b) * stdKernel y =
      (2 * π) ^ ((d : ℝ) / 2) * ∑ a, c a * e a := by
  have hpt : ∀ y : EuclidD d,
      (∑ a, c a * y a) * (∑ b, e b * y b) * stdKernel y =
        ∑ a, ∑ b, c a * e b * (y a * y b * stdKernel y) := by
    intro y
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ ↦ by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finset_sum _ (fun a _ ↦ integrable_finset_sum _
      (fun b _ ↦ (stdKernel_integrable_coord_mul a b).const_mul _))]
  have hinner : ∀ a : Fin d,
      (∑ b, ∫ y : EuclidD d,
          c a * e b * (y a * y b * stdKernel y)) =
        c a * e a * (2 * π) ^ ((d : ℝ) / 2) := by
    intro a
    have hterm : ∀ b : Fin d,
        (∫ y : EuclidD d, c a * e b * (y a * y b * stdKernel y)) =
          if a = b then c a * e b * (2 * π) ^ ((d : ℝ) / 2)
          else 0 := by
      intro b
      rw [integral_const_mul, integral_coord_mul_coord_stdKernel]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab]
      · rw [if_neg hab, if_neg hab, mul_zero]
    calc (∑ b, ∫ y : EuclidD d,
            c a * e b * (y a * y b * stdKernel y))
        = ∑ b, if a = b then
            c a * e b * (2 * π) ^ ((d : ℝ) / 2) else 0 :=
          Finset.sum_congr rfl fun b _ ↦ hterm b
      _ = c a * e a * (2 * π) ^ ((d : ℝ) / 2) := by
          rw [Finset.sum_ite_eq]
          simp
  calc (∑ a, ∫ y : EuclidD d, ∑ b,
          c a * e b * (y a * y b * stdKernel y))
      = ∑ a, c a * e a * (2 * π) ^ ((d : ℝ) / 2) := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [integral_finset_sum _ (fun b _ ↦
          (stdKernel_integrable_coord_mul a b).const_mul _)]
        exact hinner a
    _ = (2 * π) ^ ((d : ℝ) / 2) * ∑ a, c a * e a := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by ring

/-- **First moments of the quadratic Gaussian vanish.** -/
theorem integral_coord_mul_quadKernel {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (i : Fin d) :
    ∫ x : EuclidD d, x i * quadKernel H x = 0 := by
  have hpt : ∀ x : EuclidD d,
      x i * quadKernel H x =
        (fun y : EuclidD d ↦ whiteningInv H y i * stdKernel y)
          (whitening H x) := by
    intro x
    simp only []
    rw [whiteningInv_whitening hH, quadKernel_eq_stdKernel_whitening hH]
  have hmeas : AEStronglyMeasurable
      (fun y : EuclidD d ↦ whiteningInv H y i * stdKernel y)
      (volume : Measure (EuclidD d)) := by
    have hc : Continuous fun y : EuclidD d ↦ whiteningInv H y i :=
      (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i).comp
        (whiteningInv H).continuous
    exact (hc.mul stdKernel_continuous).aestronglyMeasurable
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_comp_whitening hH hmeas]
  have hexp : (fun y : EuclidD d ↦ whiteningInv H y i * stdKernel y) =
      fun y : EuclidD d ↦
        (∑ a, (CFC.sqrt H)⁻¹ i a * y a) * stdKernel y := by
    funext y
    rw [whiteningInv_coord]
  rw [hexp, integral_coordFn_mul_stdKernel, mul_zero]

/-- **Second moments of the quadratic Gaussian**: the unnormalized
value carries the opaque Jacobian and the standard partition value. -/
theorem integral_coord_mul_coord_quadKernel
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (i j : Fin d) :
    ∫ x : EuclidD d, x i * x j * quadKernel H x =
      jacInv H * (2 * π) ^ ((d : ℝ) / 2) * H⁻¹ i j := by
  have hpt : ∀ x : EuclidD d,
      x i * x j * quadKernel H x =
        (fun y : EuclidD d ↦
          whiteningInv H y i * whiteningInv H y j * stdKernel y)
          (whitening H x) := by
    intro x
    simp only []
    rw [whiteningInv_whitening hH, quadKernel_eq_stdKernel_whitening hH]
  have hmeas : AEStronglyMeasurable
      (fun y : EuclidD d ↦
        whiteningInv H y i * whiteningInv H y j * stdKernel y)
      (volume : Measure (EuclidD d)) := by
    have hci : Continuous fun y : EuclidD d ↦ whiteningInv H y i :=
      (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i).comp
        (whiteningInv H).continuous
    have hcj : Continuous fun y : EuclidD d ↦ whiteningInv H y j :=
      (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) j).comp
        (whiteningInv H).continuous
    exact ((hci.mul hcj).mul stdKernel_continuous).aestronglyMeasurable
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_comp_whitening hH hmeas]
  have hexp : (fun y : EuclidD d ↦
      whiteningInv H y i * whiteningInv H y j * stdKernel y) =
      fun y : EuclidD d ↦
        (∑ a, (CFC.sqrt H)⁻¹ i a * y a) *
          (∑ b, (CFC.sqrt H)⁻¹ j b * y b) * stdKernel y := by
    funext y
    rw [whiteningInv_coord, whiteningInv_coord]
  rw [hexp, integral_coordFn_mul_coordFn_stdKernel]
  have hgram : (∑ a, (CFC.sqrt H)⁻¹ i a * (CFC.sqrt H)⁻¹ j a) =
      H⁻¹ i j := by
    have hsymm : ((CFC.sqrt H)⁻¹)ᵀ = (CFC.sqrt H)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv]
      congr 1
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact (sqrt_posDef hH).isHermitian
    calc (∑ a, (CFC.sqrt H)⁻¹ i a * (CFC.sqrt H)⁻¹ j a)
        = ((CFC.sqrt H)⁻¹ * ((CFC.sqrt H)⁻¹)ᵀ) i j := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun a _ ↦ by
            rw [Matrix.transpose_apply]
      _ = ((CFC.sqrt H)⁻¹ * (CFC.sqrt H)⁻¹) i j := by rw [hsymm]
      _ = (CFC.sqrt H * CFC.sqrt H)⁻¹ i j := by
          rw [Matrix.mul_inv_rev]
      _ = H⁻¹ i j := by rw [sqrt_mul_sqrt hH]
  rw [hgram]
  ring

/-- **The normalized covariance of the quadratic Gaussian is
`H⁻¹`**: the Jacobian and the standard partition value cancel. -/
theorem normalized_second_moment_quadKernel
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (i j : Fin d) :
    (∫ x : EuclidD d, x i * x j * quadKernel H x) /
      (∫ x : EuclidD d, quadKernel H x) = H⁻¹ i j := by
  rw [integral_coord_mul_coord_quadKernel hH,
    integral_quadKernel hH]
  have h1 : jacInv H ≠ 0 := (jacInv_pos hH).ne'
  have h2 : (2 * π : ℝ) ^ ((d : ℝ) / 2) ≠ 0 := by positivity
  field_simp

end Laplace.Multi
