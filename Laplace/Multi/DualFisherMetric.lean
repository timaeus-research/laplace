/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PinskerEvent

/-!
# The dual Fisher metric: the Hessian of the rate in the intrinsic chart

On the image of the chart, the gradient of the rate is the natural coordinate
(`fderiv_rateFun_chart_eventually`: `∇𝓘(m₀ + v) = −θ(v)` as a functional on `𝕍`), and the gradient
is differentiable with derivative the inverse covariance (`hasFDerivAt_fderiv_rateFun_chart`):

  `D_v [∇𝓘(m₀ + v)(w)] [u] = −⟨w, (Dm(θ)|_𝕍)⁻¹ u⟩ = Cov_θ(⟨u', S⟩, ⟨w', S⟩)`,

where `u' = (Dm(θ)|_𝕍)⁻¹ u`, `w' = (Dm(θ)|_𝕍)⁻¹ w` (`hessian_rateFun_chart_eq`). This is the dual
Fisher metric on the responses: symmetric (`hessian_rateFun_chart_symm`) and positive definite on
`𝕍` (`hessian_rateFun_chart_pos`), so the rate is strictly convex along every visible direction of
the relative interior. In the convention `P_θ ∝ e^{−⟨θ,S⟩}ν` one has `Dm = −C`, and the Hessian is
`C_{θ(M)}⁻¹` as a bilinear form on `𝕍`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Chart

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : Type*} [Fintype J] [Nonempty J]
variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hπm hπi hπ hπpos hS

/-- **The gradient of the rate is the natural coordinate**, on a neighbourhood of every point of the
image of the chart. -/
theorem fderiv_rateFun_chart_eventually (θ₀ : dirSpan μ π S) :
    ∀ᶠ v : dirSpan μ π S in 𝓝 (chartV hπm hπi hπ hπpos hS θ₀),
      fderiv ℝ (fun v : dirSpan μ π S ↦
          (rateFun μ π (fun _ ↦ (0 : ℝ)) S 1 (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + v)).toReal) v =
        -(dotCLM (chartVInv hπm hπi hπ hπpos hS v : J → ℝ)).comp (dirSpan μ π S).subtypeL := by
  filter_upwards [eventually_mem_intrinsicInterior_chartV hπm hπi hπ hπpos hS θ₀] with v hv
  have h := hasFDerivAt_rateFun_chart hπm hπi hπ hπpos hS (chartVInv hπm hπi hπ hπpos hS v)
  rw [chartV_chartVInv hπm hπi hπ hπpos hS hv] at h
  exact h.fderiv

/-- **The Hessian of the rate**: the derivative of `v ↦ ∇𝓘(m₀ + v)(w)` at `chartV θ₀` is
`u ↦ −⟨w, (Dm(θ₀)|_𝕍)⁻¹ u⟩`. -/
theorem hasFDerivAt_fderiv_rateFun_chart (θ₀ w : dirSpan μ π S) :
    HasFDerivAt (fun v : dirSpan μ π S ↦ fderiv ℝ (fun v : dirSpan μ π S ↦
        (rateFun μ π (fun _ ↦ (0 : ℝ)) S 1 (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + v)).toReal) v w)
      (-(dotCLM (w : J → ℝ)).comp ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S)))
      (chartV hπm hπi hπ hπpos hS θ₀) := by
  have hinv := (hasStrictFDerivAt_chartVInv hπm hπi hπ hπpos hS θ₀).hasFDerivAt
  have hval : HasFDerivAt (fun v : dirSpan μ π S ↦ (chartVInv hπm hπi hπ hπpos hS v : J → ℝ))
      ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S))
      (chartV hπm hπi hπ hπpos hS θ₀) :=
    (dirSpan μ π S).subtypeL.hasFDerivAt.comp _ hinv
  -- the pairing with `w` is a fixed continuous linear functional of the natural coordinate
  have hpair := ((dotCLM (w : J → ℝ)).hasFDerivAt.comp _ hval).neg
  refine hpair.congr_of_eventuallyEq ?_
  filter_upwards [fderiv_rateFun_chart_eventually hπm hπi hπ hπpos hS θ₀] with v hv
  rw [hv]
  simp only [neg_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLM_apply,
    Function.comp_apply, Pi.neg_apply]
  rw [dotJ_comm]

/-- **The Hessian is the dual Fisher metric**: its value at `(u, w)` is the covariance of the dual
contrasts, `Cov_{θ₀}(⟨u', S⟩, ⟨w', S⟩)` with `u' = (Dm|_𝕍)⁻¹ u`, `w' = (Dm|_𝕍)⁻¹ w`. -/
theorem hessian_rateFun_chart_eq (θ₀ u w : dirSpan μ π S) :
    (-(dotCLM (w : J → ℝ)).comp ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S))) u =
      priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀)
        (dirLoss S ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm u))
        (dirLoss S ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm w)) 1 := by
  have hcd : ∀ v, chartDerivEquiv hπm hπi hπ hπpos hS θ₀ v = chartDeriv hπm hπi hπ hπpos hS θ₀ v :=
    fun v ↦ by
      rw [← coe_chartDerivEquiv hπm hπi hπ hπpos hS θ₀]
      rfl
  have hw : chartDeriv hπm hπi hπ hπpos hS θ₀ ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm w) =
      w := by
    rw [← hcd]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  simp only [neg_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLM_apply,
    ContinuousLinearEquiv.coe_coe]
  conv_lhs => rw [← hw]
  rw [dotJ_chartDeriv, neg_neg]

/-- The dual Fisher metric is symmetric. -/
theorem hessian_rateFun_chart_symm (θ₀ u w : dirSpan μ π S) :
    (-(dotCLM (w : J → ℝ)).comp ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm :
          dirSpan μ π S →L[ℝ] dirSpan μ π S))) u =
      (-(dotCLM (u : J → ℝ)).comp ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm :
          dirSpan μ π S →L[ℝ] dirSpan μ π S))) w := by
  rw [hessian_rateFun_chart_eq, hessian_rateFun_chart_eq, priorCov_comm]

/-- **The dual Fisher metric is positive definite on `𝕍`**: the rate is strictly convex along every
visible direction of the relative interior. -/
theorem hessian_rateFun_chart_pos (θ₀ : dirSpan μ π S) {u : dirSpan μ π S} (hu : u ≠ 0) :
    0 < (-(dotCLM (u : J → ℝ)).comp ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm :
          dirSpan μ π S →L[ℝ] dirSpan μ π S))) u := by
  rw [hessian_rateFun_chart_eq]
  have hu' : ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm u : J → ℝ) ≠ 0 := by
    intro h
    apply hu
    have h' : (chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm u = 0 := Subtype.ext h
    rwa [ContinuousLinearEquiv.symm_apply_eq, map_zero] at h'
  exact priorCov_dirLoss_self_pos hπm hπi hπ hπpos hS θ₀
    ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm u).2 hu'

end Chart

end Laplace.Multi
