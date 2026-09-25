/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LossHessian
import Laplace.Multi.RelativeEntropyGeometry

/-!
# The global response chart

The slice map `θ ↦ (t, M)` (natural coordinates to temperature and response) is a
**partial homeomorphism** from the half-space `{θ | θ_none > 0}` onto the chart domain
`{(t, M) | t > 0, M ∈ int K}` (`responseChart`), with inverse `sliceInv`. Hence every positive
temperature and interior response is realised by exactly one member of the joint family
(`responseChart_bijOn`), and the loss `h(t, M)` and the relative entropy `𝒮(t, M)` are continuous
functions on the whole chart domain (`continuousOn_lossChart`, `continuousOn_relEntropy_chart`),
on which all the landed differential identities hold. The interior response space has a unique
global canonical parametrisation; the actual data distributions occupy the reachable locus inside
it (`DataReachability`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

theorem continuous_sliceMap : Continuous (sliceMap μ π L₀ R) :=
  continuous_iff_continuousAt.2 fun θ ↦
    (hasStrictFDerivAt_sliceMap hπm hπi hπ hπpos hL₀m hL₀ hR θ).continuousAt

/-- The expected loss is continuous in the natural coordinates. -/
theorem continuous_jointLoss :
    Continuous (fun θ : Option ι → ℝ ↦
      priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) L₀ 1) := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  exact continuous_iff_continuousAt.2 fun θ ↦
    (hasFDerivAt_obsMap hπm hπi hπ hπpos measurable_const h0 hS' hL₀m hL₀ one_pos θ).continuousAt

/-- The relative entropy is continuous in the natural coordinates. -/
theorem continuous_relEntropy : Continuous (relEntropy μ π L₀ R) := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have e : relEntropy μ π L₀ R = fun θ ↦
      ∑ j, θ j * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ j +
        affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ -
        affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 0 :=
    funext fun θ ↦ relEntropy_eq hπm hπi hπ hπpos hL₀m hL₀ hR θ
  rw [e]
  have hm := continuous_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS' one_pos
  have hA : Continuous (affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1) :=
    continuous_iff_continuousAt.2 fun θ ↦
      (hasFDerivAt_affLogZ hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS' one_pos
        θ).continuousAt
  refine ((continuous_finsetSum _ fun j _ ↦ (continuous_apply j).mul ?_).add hA).sub
    continuous_const
  exact (continuous_apply j).comp hm

variable (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  [Nonempty ι]
include hnd

/-- The slice map sends positive temperatures into the chart domain. -/
theorem sliceMap_mem_chartDomain {θ : Option ι → ℝ} (hθ : 0 < θ none) :
    sliceMap μ π L₀ R θ ∈ chartDomain μ π R := by
  have e : sliceMap μ π L₀ R θ = jointPoint (θ none) (meanMap μ π L₀ R (θ none) (aOf θ)) := by
    conv_lhs => rw [← natCoord_aOf hθ]
    exact sliceMap_natCoord π L₀ R _ _
  refine ⟨by simpa using hθ, ?_⟩
  simp only [e, jointPoint_some]
  rw [← range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR hθ hnd]
  exact ⟨aOf θ, rfl⟩

theorem sliceInv_mem_source {p : Option ι → ℝ} (hp : p ∈ chartDomain μ π R) :
    0 < sliceInv μ π L₀ R p none := by
  have := sliceInv_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd hp.1 hp.2
  rwa [jointPoint_eq] at this

theorem sliceMap_sliceInv' {p : Option ι → ℝ} (hp : p ∈ chartDomain μ π R) :
    sliceMap μ π L₀ R (sliceInv μ π L₀ R p) = p := by
  have := sliceMap_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd hp.1 hp.2
  rwa [jointPoint_eq] at this

/-- **The global response chart**: natural coordinates at positive temperature are homeomorphic
to the chart domain `{(t, M) | t > 0, M ∈ int K}` via the slice map, with inverse `sliceInv`. -/
noncomputable def responseChart : PartialHomeomorph (Option ι → ℝ) (Option ι → ℝ) where
  toFun := sliceMap μ π L₀ R
  invFun := sliceInv μ π L₀ R
  source := {θ | 0 < θ none}
  target := chartDomain μ π R
  map_source' _ hθ := sliceMap_mem_chartDomain hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ
  map_target' _ hp := sliceInv_mem_source hπm hπi hπ hπpos hL₀m hL₀ hR hnd hp
  left_inv' _ hθ := sliceInv_sliceMap hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ
  right_inv' _ hp := sliceMap_sliceInv' hπm hπi hπ hπpos hL₀m hL₀ hR hnd hp
  continuousOn_toFun := (continuous_sliceMap hπm hπi hπ hπpos hL₀m hL₀ hR).continuousOn
  continuousOn_invFun := by
    intro p hp
    have h := hasStrictFDerivAt_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
      (sliceInv_mem_source hπm hπi hπ hπpos hL₀m hL₀ hR hnd hp)
    rw [sliceMap_sliceInv' hπm hπi hπ hπpos hL₀m hL₀ hR hnd hp] at h
    exact h.continuousAt.continuousWithinAt

@[simp] theorem responseChart_apply (θ : Option ι → ℝ) :
    responseChart hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ = sliceMap μ π L₀ R θ := rfl

@[simp] theorem responseChart_symm_apply (p : Option ι → ℝ) :
    (responseChart hπm hπi hπ hπpos hL₀m hL₀ hR hnd).symm p = sliceInv μ π L₀ R p := rfl

@[simp] theorem responseChart_source :
    (responseChart hπm hπi hπ hπpos hL₀m hL₀ hR hnd).source = {θ | 0 < θ none} := rfl

@[simp] theorem responseChart_target :
    (responseChart hπm hπi hπ hπpos hL₀m hL₀ hR hnd).target = chartDomain μ π R := rfl

/-- **Every positive temperature and interior response is realised by exactly one member.** -/
theorem responseChart_bijOn :
    BijOn (sliceMap μ π L₀ R) {θ : Option ι → ℝ | 0 < θ none} (chartDomain μ π R) :=
  (responseChart hπm hπi hπ hπpos hL₀m hL₀ hR hnd).toPartialEquiv.bijOn

/-- The partial inverse is continuous on the chart domain. -/
theorem continuousOn_sliceInv : ContinuousOn (sliceInv μ π L₀ R) (chartDomain μ π R) :=
  (responseChart hπm hπi hπ hπpos hL₀m hL₀ hR hnd).continuousOn_invFun

/-- **The loss surface is continuous on the whole chart domain.** -/
theorem continuousOn_lossChart : ContinuousOn (lossChart μ π L₀ R) (chartDomain μ π R) :=
  (continuous_jointLoss hπm hπi hπ hπpos hL₀m hL₀ hR).comp_continuousOn
    (continuousOn_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd)

/-- **The entropy landscape is continuous on the whole chart domain.** -/
theorem continuousOn_relEntropy_chart :
    ContinuousOn (fun p ↦ relEntropy μ π L₀ R (sliceInv μ π L₀ R p)) (chartDomain μ π R) :=
  (continuous_relEntropy hπm hπi hπ hπpos hL₀m hL₀ hR).comp_continuousOn
    (continuousOn_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd)

end

end Laplace.Multi
