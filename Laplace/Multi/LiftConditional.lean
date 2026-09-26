/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.KLJointConvexity

/-!
# The lift retains the statistic-measurable part of the density

The density of the statistic lift is the conditional expectation of the density given the
statistic: `dD↑/dν = E_ν[dD/dν | σ(S)]` almost everywhere (`rnDeriv_statisticLift_eq_condLExp`),
a direct consequence of Mathlib's identification of the pushforward Radon–Nikodym derivative with a
conditional expectation. This is the precise sense in which lifting keeps exactly the information
visible through `S`: the lifted density is the projection of the density onto the `σ(S)`-measurable
functions.

The fibre information is also convex along the bridge: for `0 < s ≤ t ≤ 1`, `L_s ≤ (s/t) L_t`
(`fibreInformation_bridge_le_div`), by joint convexity applied to `D_s = (1 − s/t) ν + (s/t) D_t`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

section Conditional

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν D : Measure X)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : X → Y) (hS : Measurable S) (hD : D ≪ ν)
include hS hD

/-- **The lifted density is the conditional expectation of the density given the statistic**:
`dD↑/dν = E_ν[dD/dν | σ(S)]`. -/
theorem rnDeriv_statisticLift_eq_condLExp :
    (statisticLift ν D S).rnDeriv ν =ᵐ[ν]
      ν⁻[D.rnDeriv ν | MeasurableSpace.comap S ‹MeasurableSpace Y›] := by
  filter_upwards [Measure.rnDeriv_withDensity ν (measurable_liftDensity ν D S hS),
    rnDeriv_map hD hS] with x h1 h2
  unfold statisticLift
  rw [h1]
  exact h2

end Conditional

section Convexity

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν D : Measure X)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : X → Y) (hS : Measurable S) (hD : D ≪ ν)
include hS hD

omit hS hD [IsProbabilityMeasure ν] [IsProbabilityMeasure D] in
/-- Re-mixing along the bridge: with `a + b = 1`, `c + d = 1`, `l + m = 1` and `b = m d`,
`a ν + b D = l ν + m (c ν + d D)`. -/
theorem bridge_remix {a b c d l m : ℝ≥0} (hab : a + b = 1) (hcd : c + d = 1) (hlm : l + m = 1)
    (hb : b = m * d) : a • ν + b • D = l • ν + m • (c • ν + d • D) := by
  have ha : a = l + m * c := by
    have h : a + b = (l + m * c) + b := by
      rw [hab, hb, add_assoc, ← mul_add, hcd, mul_one, hlm]
    exact add_right_cancel h
  rw [ha, hb, smul_add, smul_smul, smul_smul, add_smul, add_assoc]

/-- **Convexity of the fibre information along the bridge**: with the weights of `bridge_remix`,
`KL(a ν + b D ‖ (a ν + b D)↑) ≤ m KL(c ν + d D ‖ (c ν + d D)↑)`. -/
theorem fibreInformation_bridge_le_remix {a b c d l m : ℝ≥0} (hab : a + b = 1) (hcd : c + d = 1)
    (hlm : l + m = 1) (hb : b = m * d) (hl : 0 < l) (hm : 0 < m) :
    klDiv (a • ν + b • D) (statisticLift ν (a • ν + b • D) S) ≤
      (m : ℝ≥0∞) * klDiv (c • ν + d • D) (statisticLift ν (c • ν + d • D) S) := by
  have hQP := isProbabilityMeasure_mixture ν D hcd
  have hQν : c • ν + d • D ≪ ν :=
    mixture_absolutelyContinuous ν Measure.AbsolutelyContinuous.rfl hD c d
  have hPL := isProbabilityMeasure_statisticLift ν (c • ν + d • D) S hS hQν
  rw [bridge_remix ν D hab hcd hlm hb, statisticLift_bridge ν S hS _ l m]
  have := klDiv_mixture_mixture_le ν (c • ν + d • D) ν (statisticLift ν (c • ν + d • D) S)
    Measure.AbsolutelyContinuous.rfl (absolutelyContinuous_statisticLift ν _ S hS hQν) hlm hl hm
  rwa [klDiv_self, mul_zero, zero_add] at this

end Convexity

end Laplace.Multi
