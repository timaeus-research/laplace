/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.QuadForm

/-!
# The quadratic Gaussian package by whitening

Stage H2b of the multivariate programme, second installment: the
change of variables through the whitening map (with the Jacobian kept
as an opaque positive constant `jacInv H`), and the partition value
`∫ K_H = jacInv H · (2π)^(d/2) > 0` with integrability of the kernel.
-/

open Real MeasureTheory Matrix
open scoped MatrixOrder

namespace Laplace.Multi

variable {d : ℕ}

/-- The inverse whitening Jacobian, kept opaque throughout: it
cancels in every normalized quantity and only its positivity is
used. -/
noncomputable def jacInv (H : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  |LinearMap.det ((whitening H : EuclidD d →L[ℝ] EuclidD d) :
    EuclidD d →ₗ[ℝ] EuclidD d)|⁻¹

theorem jacInv_pos {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) :
    0 < jacInv H :=
  inv_pos.mpr (abs_pos.mpr (whitening_det_ne_zero hH))

/-- Pushforward of Lebesgue volume under the whitening map. -/
theorem map_whitening_volume {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) :
    Measure.map (whitening H) volume =
      ENNReal.ofReal (jacInv H) • volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := volume) (whitening_det_ne_zero hH)
  rw [ContinuousLinearMap.coe_coe] at h
  rw [h]
  unfold jacInv
  rw [← abs_inv]

/-- **Change of variables through the whitening map.** Holds for any
almost-everywhere strongly measurable observable. -/
theorem integral_comp_whitening {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {φ : EuclidD d → ℝ}
    (hφ : AEStronglyMeasurable φ (volume : Measure (EuclidD d))) :
    ∫ x, φ (whitening H x) = jacInv H * ∫ y, φ y := by
  have hg : AEStronglyMeasurable φ
      (Measure.map (whitening H) volume) := by
    rw [map_whitening_volume hH]
    exact hφ.mono_ac Measure.smul_absolutelyContinuous
  calc ∫ x, φ (whitening H x)
      = ∫ y, φ y ∂(Measure.map (whitening H) volume) :=
        (MeasureTheory.integral_map
          (whitening H).continuous.aemeasurable hg).symm
    _ = jacInv H * ∫ y, φ y := by
        rw [map_whitening_volume hH, integral_smul_measure,
          ENNReal.toReal_ofReal (jacInv_pos hH).le, smul_eq_mul]

/-- Integrability transports through the whitening map. -/
theorem integrable_comp_whitening {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {φ : EuclidD d → ℝ} (hφ : Integrable φ) :
    Integrable (fun x ↦ φ (whitening H x)) := by
  have hg : AEStronglyMeasurable φ
      (Measure.map (whitening H) volume) := by
    rw [map_whitening_volume hH]
    exact hφ.aestronglyMeasurable.mono_ac
      Measure.smul_absolutelyContinuous
  have h2 : Integrable φ (Measure.map (whitening H) volume) := by
    rw [map_whitening_volume hH]
    exact hφ.smul_measure ENNReal.ofReal_ne_top
  exact (MeasureTheory.integrable_map_measure hg
    (whitening H).continuous.aemeasurable).mp h2

/-- The quadratic kernel is integrable. -/
theorem quadKernel_integrable {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) : Integrable (quadKernel H) := by
  refine (integrable_comp_whitening hH stdKernel_integrable).congr
    (Filter.Eventually.of_forall fun x ↦ ?_)
  exact (quadKernel_eq_stdKernel_whitening hH x).symm

/-- **All polynomial weights are integrable** against the quadratic
kernel, by operator-norm domination through the whitening map. -/
theorem quadKernel_integrable_pow {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (n : ℕ) :
    Integrable (fun x : EuclidD d ↦ ‖x‖ ^ n * quadKernel H x) := by
  have hdom : Integrable (fun x : EuclidD d ↦
      ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt H)⁻¹ :
          EuclidD d →L[ℝ] EuclidD d)‖ ^ n *
        (‖whitening H x‖ ^ n * stdKernel (whitening H x))) :=
    (integrable_comp_whitening hH (stdKernel_integrable_pow n)).const_mul _
  refine hdom.mono'
    (((continuous_norm.pow n).mul
      (quadKernel_continuous H)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  set C : EuclidD d →L[ℝ] EuclidD d :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt H)⁻¹ with hC_def
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm,
    abs_of_pos (quadKernel_pos H x),
    quadKernel_eq_stdKernel_whitening hH]
  have hCx : C (whitening H x) = x := by
    rw [hC_def]
    unfold whitening
    rw [← ContinuousLinearMap.mul_apply, ← map_mul,
      Matrix.nonsing_inv_mul _
        (isUnit_iff_ne_zero.mpr (sqrt_posDef hH).det_pos.ne'),
      map_one, ContinuousLinearMap.one_apply]
  have hx : ‖x‖ ≤ ‖C‖ * ‖whitening H x‖ := by
    conv_lhs => rw [← hCx]
    exact C.le_opNorm _
  calc ‖x‖ ^ n * stdKernel (whitening H x)
      ≤ (‖C‖ * ‖whitening H x‖) ^ n * stdKernel (whitening H x) := by
        apply mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg x) hx n)
          (stdKernel_pos _).le
    _ = ‖C‖ ^ n * (‖whitening H x‖ ^ n * stdKernel (whitening H x)) := by
        ring

/-- **The partition value**: `∫ K_H = jacInv H · (2π)^(d/2)`. -/
theorem integral_quadKernel {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) :
    ∫ x : EuclidD d, quadKernel H x =
      jacInv H * (2 * π) ^ ((d : ℝ) / 2) := by
  calc ∫ x : EuclidD d, quadKernel H x
      = ∫ x : EuclidD d, stdKernel (whitening H x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x ↦
          quadKernel_eq_stdKernel_whitening hH x)
    _ = jacInv H * ∫ y : EuclidD d, stdKernel y :=
        integral_comp_whitening hH
          stdKernel_continuous.aestronglyMeasurable
    _ = jacInv H * (2 * π) ^ ((d : ℝ) / 2) := by
        rw [integral_stdKernel]

/-- The partition value is positive. -/
theorem integral_quadKernel_pos {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) :
    0 < ∫ x : EuclidD d, quadKernel H x := by
  rw [integral_quadKernel hH]
  exact mul_pos (jacInv_pos hH) (by positivity)

end Laplace.Multi
