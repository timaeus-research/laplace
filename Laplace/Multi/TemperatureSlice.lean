/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MomentBody
import Laplace.Multi.NaturalCoordinates

/-!
# The temperature slices of the joint family

At a fixed temperature `t > 0` the posteriors `P_{t,a} ∝ e^{-t L_a} π` are the exponential family of
the contrasts `R` under the **tilted prior** `π_t = e^{-t L₀} π` with natural parameter `t a`
(`meanMap_eq_tilted`). The tilted prior has the same null sets as `π`, so the essential range and
the moment body of the contrasts do not depend on the temperature or on the base loss
(`essRange_tilted`, `momentBody_tilted`), and the moment-body theorem
gives:

  **at every temperature the mean map `a ↦ m(t, a)` is a bijection of data space onto the
  interior of the contrast moment body** (`range_meanMap_slice`, `bijOn_meanMap_slice`).

Hence in the joint family the image of the slice `{t} × ℝ^k` under the joint mean map is a graph
`η₀ = h_t(M)` over the fixed open set `int (momentBody R)` (`temperature_slice_graph`): the data
manifold "at temperature `t`" is, in response coordinates, always the same open convex body, and the
temperature only moves the height `⟨L₀⟩` of the graph above it.
-/

open MeasureTheory Filter Topology Set

-- the essential range and the moment body of `R : ι → X → ℝ` carry `Fintype ι` invisibly
set_option linter.unusedFintypeInType false

namespace Laplace.Multi

section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The tilted prior `π_t = e^{-t L₀} π`. -/
noncomputable def tiltedPrior (π L₀ : X → ℝ) (t : ℝ) : X → ℝ := fun x ↦ Real.exp (-(t * L₀ x)) * π x

omit [MeasurableSpace X] [Fintype ι] [Nonempty ι] in
theorem tiltedPrior_pos {π : X → ℝ} (hπ : ∀ x, 0 < π x) (L₀ : X → ℝ) (t : ℝ) (x : X) :
    0 < tiltedPrior π L₀ t x := by
  unfold tiltedPrior; have := hπ x; positivity

omit [Fintype ι] [Nonempty ι] in
theorem measurable_tiltedPrior {π L₀ : X → ℝ} (hπm : Measurable π) (hL₀m : Measurable L₀) (t : ℝ) :
    Measurable (tiltedPrior π L₀ t) :=
  (Real.measurable_exp.comp (hL₀m.const_mul t).neg).mul hπm

omit [Fintype ι] [Nonempty ι] in
theorem integrable_tiltedPrior {π L₀ : X → ℝ} (hπi : Integrable π μ) (hL₀m : Measurable L₀)
    {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) {t : ℝ} (ht : 0 < t) :
    Integrable (tiltedPrior π L₀ t) μ := by
  refine hπi.bdd_mul (c := Real.exp (t * M₀))
    (Real.measurable_exp.comp (hL₀m.const_mul t).neg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, Real.abs_exp]
  apply Real.exp_le_exp.2
  have := (abs_le.1 (hL₀ x)).1
  nlinarith

omit [Nonempty ι] in
theorem integral_tiltedPrior_pos [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π)
    (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀)
    {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (t : ℝ) :
    0 < ∫ x, tiltedPrior π L₀ t x ∂μ := by
  have h := (tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR 0 0 t).choose_spec.ν_pos
  refine lt_of_lt_of_eq h (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_))
  simp [baseWeight, affLoss, tiltedPrior]

omit [Nonempty ι] in
/-- **The slice is the contrast family under the tilted prior**:
`m(t, a) = m^{π_t}(1, t a)` with base loss `0`. -/
theorem meanMap_eq_tilted (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) :
    meanMap μ π L₀ R t a = meanMap μ (tiltedPrior π L₀ t) (fun _ ↦ (0 : ℝ)) R 1 (t • a) := by
  funext i
  unfold meanMap priorExp priorZ
  have e : ∀ x, Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) R (t • a) x)) * tiltedPrior π L₀ t x =
      Real.exp (-(t * affLoss L₀ R a x)) * π x := fun x ↦ by
    unfold tiltedPrior affLoss
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [Pi.smul_apply, smul_eq_mul, zero_add, Finset.mul_sum, mul_add, mul_assoc]
    ring
  simp_rw [mul_assoc, e]

omit [Nonempty ι] in
/-- The essential range of the contrasts is the same under the tilted prior. -/
theorem essRange_tilted {π L₀ : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hL₀m : Measurable L₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (t : ℝ) :
    essRange μ (tiltedPrior π L₀ t) R = essRange μ π R := by
  ext y
  rw [mem_essRange_iff (measurable_tiltedPrior hπm hL₀m t) (tiltedPrior_pos hπ L₀ t) hR,
    mem_essRange_iff hπm hπ hR]

omit [Nonempty ι] in
theorem momentBody_tilted {π L₀ : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hL₀m : Measurable L₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (t : ℝ) :
    momentBody μ (tiltedPrior π L₀ t) R = momentBody μ π R := by
  unfold momentBody
  rw [essRange_tilted hπm hπ hL₀m hR t]

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd

/-- **At every temperature the data manifold is charted onto the same moment body**:
`range (a ↦ m(t,a)) = interior (momentBody R)`. -/
theorem range_meanMap_slice :
    Set.range (meanMap μ π L₀ R t) = interior (momentBody μ π R) := by
  have hnd' : ∀ v : ι → ℝ, v ≠ 0 →
      ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, tiltedPrior π L₀ t x ≠ 0 → dirLoss R v x = c := by
    intro v hv ⟨c, hc⟩
    refine hnd v hv ⟨c, ?_⟩
    filter_upwards [hc] with x hx _
    exact hx (tiltedPrior_pos hπ L₀ t x).ne'
  have hbody := range_meanMap_eq_interior_momentBody (measurable_tiltedPrior hπm hL₀m t)
    (integrable_tiltedPrior hπi hL₀m hL₀ ht) (tiltedPrior_pos hπ L₀ t)
    (integral_tiltedPrior_pos hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR t) hR hnd'
  rw [momentBody_tilted hπm hπ hL₀m hR t] at hbody
  rw [← hbody]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨t • a, (meanMap_eq_tilted π L₀ R t a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨t⁻¹ • b, ?_⟩
    rw [meanMap_eq_tilted π L₀ R t, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

/-- The slice mean map is a bijection of data space onto the interior of the moment body. -/
theorem bijOn_meanMap_slice :
    Set.BijOn (meanMap μ π L₀ R t) Set.univ (interior (momentBody μ π R)) := by
  rw [← range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]
  exact ⟨fun a _ ↦ ⟨a, rfl⟩, fun a _ b _ h ↦
    meanMap_injective hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd h,
    fun y ⟨a, ha⟩ ↦ ⟨a, mem_univ a, ha⟩⟩

/-- **The temperature slice of the joint family is a graph over the contrast body**: every
`y` in the interior of the moment body of the contrasts is the contrast part of exactly one joint
response `η(Θ(t,a))`, whose base component is `⟨L₀⟩_{t,a}`. -/
theorem temperature_slice_graph {y : ι → ℝ} (hy : y ∈ interior (momentBody μ π R)) :
    ∃! a : ι → ℝ, (fun i ↦ meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a)
      (some i)) = y := by
  have hbij := bijOn_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
  obtain ⟨a, _, ha⟩ := hbij.surjOn hy
  refine ⟨a, ?_, fun b hb ↦ ?_⟩
  · funext i
    rw [meanMap_natCoord_some]
    exact congrFun ha i
  · apply hbij.injOn (mem_univ b) (mem_univ a)
    funext i
    have := congrFun hb i
    rw [meanMap_natCoord_some] at this
    rw [this, ← ha]

end

end Laplace.Multi
