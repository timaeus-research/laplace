/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponsePathDifferential
import Laplace.Multi.MeanSegment

/-!
# Continuity of the chart derivative and of the susceptibility

The restricted covariance operator `chartDeriv θ : 𝕍 →L 𝕍` depends continuously on `θ`
(`continuous_chartDeriv`), because the ambient Jacobian does and restriction does not increase
operator norms. Inversion is continuous on the units of the Banach algebra `𝕍 →L 𝕍`, so the
susceptibility `θ ↦ (chartDerivEquiv θ).symm` is continuous as well
(`continuous_chartDerivEquiv_symm`). This is the regularity step that turns the strictly
differentiable chart into a `C¹` chart, and it makes the curvature of the rate along a path
continuous, hence integrable.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Chart

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : Type*} [Fintype J] [Nonempty J]
variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hπm hπi hπ hπpos hS

/-- Restriction to the direction subspace does not increase the operator norm of a difference. -/
theorem norm_chartDeriv_sub_le (θ θ' : dirSpan μ π S) :
    ‖chartDeriv hπm hπi hπ hπpos hS θ - chartDeriv hπm hπi hπ hπpos hS θ'‖ ≤
      ‖meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ - meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ'‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  rw [Submodule.coe_norm, Submodule.coe_norm, sub_apply, Submodule.coe_sub, chartDeriv_apply,
    chartDeriv_apply, ← sub_apply]
  exact ContinuousLinearMap.le_opNorm _ _

/-- **The restricted covariance operator is continuous in the natural coordinates.** -/
theorem continuous_chartDeriv : Continuous (chartDeriv hπm hπi hπ hπpos hS) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hD := continuous_meanMapDeriv hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS
    one_pos
  rw [Metric.continuous_iff]
  intro θ ε hε
  have hDc := (Metric.continuous_iff.1 (hD.comp continuous_subtype_val)) θ ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hDc
  refine ⟨δ, hδ, fun θ' hθ' ↦ ?_⟩
  have := hδ' θ' hθ'
  rw [dist_eq_norm] at this ⊢
  exact lt_of_le_of_lt (norm_chartDeriv_sub_le hπm hπi hπ hπpos hS θ' θ) this

/-- The susceptibility as the ring inverse of the restricted covariance operator. -/
theorem coe_chartDerivEquiv_symm (θ : dirSpan μ π S) :
    ((chartDerivEquiv hπm hπi hπ hπpos hS θ).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S) =
      Ring.inverse (chartDeriv hπm hπi hπ hπpos hS θ) := by
  rw [← coe_chartDerivEquiv, ContinuousLinearMap.ringInverse_eq_inverse,
    ContinuousLinearMap.inverse_equiv]

/-- **The susceptibility is continuous in the natural coordinates.** -/
theorem continuous_chartDerivEquiv_symm :
    Continuous (fun θ : dirSpan μ π S ↦
      ((chartDerivEquiv hπm hπi hπ hπpos hS θ).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S)) := by
  simp_rw [coe_chartDerivEquiv_symm]
  refine continuous_iff_continuousAt.2 fun θ ↦ ?_
  have hu : IsUnit (chartDeriv hπm hπi hπ hπpos hS θ) := by
    rw [← coe_chartDerivEquiv]
    exact ((ContinuousLinearEquiv.unitsEquiv ℝ (dirSpan μ π S)).symm
      (chartDerivEquiv hπm hπi hπ hπpos hS θ)).isUnit
  obtain ⟨u, hu⟩ := hu
  have hinv : ContinuousAt (Ring.inverse : (dirSpan μ π S →L[ℝ] dirSpan μ π S) →
      (dirSpan μ π S →L[ℝ] dirSpan μ π S)) (chartDeriv hπm hπi hπ hπpos hS θ) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact hinv.comp (continuous_chartDeriv hπm hπi hπ hπpos hS).continuousAt

end Chart

end Laplace.Multi
