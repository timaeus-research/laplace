/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LossHessian

/-!
# The blocks and the symmetry of the loss Hessian

Corollaries of `hasDerivAt_lossGrad_line`, `D²h[X, Y] = κ₃(H, S_X, S_Y)`:

* **symmetry** `D²h[X, Y] = D²h[Y, X]` (`lossHessian_symm`), from the symmetry of `κ₃`;
* the **temperature block** `κ₃(H, H, H)` (`lossHessian_temp_temp`);
* the **mixed block** `−κ₃(H, H, V_v)` with `V_v = (C⁻¹v)·R` (`lossHessian_temp_response`);
* the **response block** `κ₃(H, V_v, V_w)` (`lossHessian_response_response`), the intrinsic mixture
  Hessian of the expected loss on the fixed-temperature exponential family.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

omit [MeasurableSpace X] in
theorem dirLoss_zero_vec (R : ι → X → ℝ) : dirLoss R 0 = fun _ ↦ (0 : ℝ) := by
  funext x
  simp [dirLoss]

theorem priorCum3_neg_left (π L φ ψ χ : X → ℝ) (t : ℝ) :
    priorCum3 μ π L (fun x ↦ -φ x) ψ χ t = -priorCum3 μ π L φ ψ χ t := by
  have e : (fun x ↦ -φ x) = fun x ↦ (-1 : ℝ) * φ x := funext fun x ↦ by ring
  rw [e, priorCum3_const_mul_left]
  ring

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  [Nonempty ι] [DecidableEq ι]
include hπm hπi hπ hπpos hL₀m hL₀ hR hnd

omit [Nonempty ι] in
/-- **The loss Hessian is symmetric**: `κ₃(H, S_X, S_Y) = κ₃(H, S_Y, S_X)`. -/
theorem lossHessian_symm (t : ℝ) (M : ι → ℝ) (τ τ' : ℝ) (v v' : ι → ℝ) :
    priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint τ v)))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint τ' v'))) 1 =
      priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint τ' v')))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint τ v))) 1 :=
  priorCum3_swap₂₃ π _ _ _ _ 1

/-- **The temperature block**: `D²h[(1,0),(1,0)] = κ₃(H, H, H)`. -/
theorem lossHessian_temp_temp {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint 1 0)))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint 1 0))) 1 =
      priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t)) (natH μ π L₀ R (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t)) 1 := by
  rw [chartScore_eq hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]
  simp only [Matrix.mulVec_zero, dirLoss_zero_vec, one_mul, sub_zero]

/-- **The mixed block**: `D²h[(1,0),(0,v)] = −κ₃(H, H, (C⁻¹v)·R)`. -/
theorem lossHessian_temp_response {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (v : ι → ℝ) :
    priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint 1 0)))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint 0 v))) 1 =
      -priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t)) (natH μ π L₀ R (tempPath μ π L₀ R M t))
        (dirLoss R ((natC μ π L₀ R (tempPath μ π L₀ R M t))⁻¹.mulVec v)) 1 := by
  rw [chartScore_eq hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM,
    chartScore_eq hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]
  simp only [Matrix.mulVec_zero, dirLoss_zero_vec, one_mul, sub_zero, zero_mul, zero_sub]
  rw [priorCum3_swap₂₃, priorCum3_swap₁₂, priorCum3_neg_left, priorCum3_swap₁₂, priorCum3_swap₂₃]

/-- **The response block**: `D²h[(0,v),(0,w)] = κ₃(H, (C⁻¹v)·R, (C⁻¹w)·R)`, the intrinsic mixture
Hessian of the expected loss on the fixed-temperature family. -/
theorem lossHessian_response_response {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (v w : ι → ℝ) :
    priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint 0 v)))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint 0 w))) 1 =
      priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t))
        (dirLoss R ((natC μ π L₀ R (tempPath μ π L₀ R M t))⁻¹.mulVec v))
        (dirLoss R ((natC μ π L₀ R (tempPath μ π L₀ R M t))⁻¹.mulVec w)) 1 := by
  rw [chartScore_eq hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM,
    chartScore_eq hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]
  simp only [zero_mul, zero_sub]
  rw [priorCum3_swap₁₂, priorCum3_neg_left, priorCum3_swap₁₂, priorCum3_swap₂₃,
    priorCum3_swap₁₂, priorCum3_neg_left, priorCum3_swap₁₂, priorCum3_swap₂₃, neg_neg]

end

end Laplace.Multi
