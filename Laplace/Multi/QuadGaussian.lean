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
