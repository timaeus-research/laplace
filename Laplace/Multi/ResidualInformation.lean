/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.StatisticLift
import Laplace.Multi.EndpointConvergence

/-!
# The invisible information of the atlas: fibre part and marginal part

The residual split of `StatisticLift` applied to the response projection. For a data law `D` of
finite information whose response `M_D = E_D S` lies in the relative interior of the moment body,
the projection `Π_ν(M_D)` is a bounded tilt of `ν` by a function of the statistic `S`, so

  `KL(D ‖ Π_ν(M_D)) = KL(D ‖ D↑) + KL(S_*D ‖ S_*Π_ν(M_D))`
                                    (`klDiv_responseProjection_eq_statisticLift_add_map`)

with `D↑ = statisticLift ν D S` the law with the same `S`-distribution as `D` and density a function
of `S`. The **fibre part** `KL(D ‖ D↑)` is the information in `D` not carried by `S` at all; it does
not depend on the tilt. The **marginal part** `KL(S_*D ‖ S_*Π_ν(M_D))` is the information in the
distribution of `S` beyond its prescribed mean.

Nested statistics give an exact **information tower** (`klDiv_statisticLift_tower`): for
`T = h ∘ S`, `KL(D ‖ D↑ᵀ) = KL(D ‖ D↑ˢ) + KL(D↑ˢ ‖ D↑ᵀ)` — the invisible information at a coarser
statistic is the invisible information at the finer one plus the information the finer statistic
carries beyond the coarser one. No conditional kernels are used.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Clamp

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν D : Measure X)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : X → Y) (hS : Measurable S) (hD : D ≪ ν)
include hS hD

/-- **The residual split for tilts by functions of `S` that are bounded along `S`**. -/
theorem klDiv_tilted_comp_eq_statisticLift_add_map' {f : Y → ℝ} (hfm : Measurable f) {L : ℝ}
    (hL : ∀ x, |f (S x)| ≤ L) (hfin : klDiv D ν ≠ ⊤) :
    klDiv D (ν.tilted fun x ↦ f (S x)) =
      klDiv D (statisticLift ν D S) + klDiv (D.map S) ((ν.tilted fun x ↦ f (S x)).map S) := by
  obtain ⟨g, hg⟩ : ∃ g : Y → ℝ, g = fun y ↦ max (-L) (min L (f y)) := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact measurable_const.max (measurable_const.min hfm)
  have hgb : ∀ y, |g y| ≤ |L| := by
    intro y
    rw [hg, abs_le]
    refine ⟨?_, max_le (neg_le_abs L) ((min_le_left _ _).trans (le_abs_self L))⟩
    exact (neg_le_neg (le_abs_self L)).trans (le_max_left _ _)
  have e : (fun x ↦ f (S x)) = fun x ↦ g (S x) := by
    funext x
    rw [hg]
    have := abs_le.1 (hL x)
    simp only
    rw [min_eq_right this.2, max_eq_right this.1]
  rw [e]
  exact klDiv_tilted_comp_eq_statisticLift_add_map ν D S hS hD ⟨hgm, |L|, hgb⟩ hfin

end Clamp

section Projection

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The invisible information splits into a fibre part and a marginal part**: for a data law of
finite information with response in the relative interior,
`KL(D ‖ Π_ν(M_D)) = KL(D ‖ D↑) + KL(S_*D ‖ S_*Π_ν(M_D))`. -/
theorem klDiv_responseProjection_eq_statisticLift_add_map (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤)
    (hrel : (fun i ↦ ∫ x, S i x ∂D) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv D (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)) =
      klDiv D (statisticLift ν D (statPoint S)) +
        klDiv (D.map (statPoint S))
          ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)).map (statPoint S)) := by
  obtain ⟨θ, hθ⟩ := responseProjection_eq_tilted hS ν hrel
  have hDν : D ≪ ν := (klDiv_ne_top_iff.1 hDkl).1
  have hpt : ∀ x, dirLoss S θ x = dotJ θ (statPoint S x) := fun x ↦ by
    simp only [dirLoss, dotJ, statPoint]
  have hf : (fun x ↦ -(1 : ℝ) * dirLoss S θ x) =
      fun x ↦ (fun y : J → ℝ ↦ -(1 : ℝ) * dotJ θ y) (statPoint S x) := by
    funext x
    simp only [hpt]
  obtain ⟨-, L, hL⟩ := Bdd.const_mul (-1) (bdd_dirLoss hS θ)
  have hL' : ∀ x, |(fun y : J → ℝ ↦ -(1 : ℝ) * dotJ θ y) (statPoint S x)| ≤ L := fun x ↦ by
    simp only
    rw [← hpt]
    exact hL x
  rw [hθ, hf]
  exact klDiv_tilted_comp_eq_statisticLift_add_map' ν D (statPoint S) (measurable_statPoint hS) hDν
    (f := fun y : J → ℝ ↦ -(1 : ℝ) * dotJ θ y) ((continuous_dotJ_right θ).measurable.const_mul _)
    hL' hDkl

end Projection

section Tower

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  (ν : Measure X)

omit [MeasurableSpace Z] in
/-- The lift depends on `D` only through its statistic law. -/
theorem statisticLift_congr {D₁ D₂ : Measure X} {S : X → Y} (h : D₁.map S = D₂.map S) :
    statisticLift ν D₁ S = statisticLift ν D₂ S := by
  unfold statisticLift
  rw [h]

variable (D : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : X → Y) (h : Y → Z)
  (hS : Measurable S) (hh : Measurable h) (hD : D ≪ ν)
include hS hh hD

/-- The lift along a coarser statistic factors through the lift along the finer one. -/
theorem statisticLift_statisticLift :
    statisticLift ν (statisticLift ν D S) (h ∘ S) = statisticLift ν D (h ∘ S) := by
  refine statisticLift_congr ν ?_
  rw [← Measure.map_map hh hS, map_statisticLift ν D S hS hD, Measure.map_map hh hS]

/-- **The information tower**: for nested statistics `T = h ∘ S`,
`KL(D ‖ D↑ᵀ) = KL(D ‖ D↑ˢ) + KL(D↑ˢ ‖ D↑ᵀ)` when `KL(D ‖ ν) < ∞`. -/
theorem klDiv_statisticLift_tower (hfin : klDiv D ν ≠ ⊤) :
    klDiv D (statisticLift ν D (h ∘ S)) =
      klDiv D (statisticLift ν D S) +
        klDiv (statisticLift ν D S) (statisticLift ν D (h ∘ S)) := by
  have hhS : Measurable (h ∘ S) := hh.comp hS
  have hPL := isProbabilityMeasure_statisticLift ν D S hS hD
  have hLν := statisticLift_absolutelyContinuous ν D S
  have h1 := klDiv_eq_klDiv_statisticLift_add_map ν D (h ∘ S) hhS hD hfin
  have h2 := klDiv_eq_klDiv_statisticLift_add_map ν D S hS hD hfin
  have hLfin : klDiv (statisticLift ν D S) ν ≠ ⊤ := by
    rw [klDiv_statisticLift_eq_map ν D S hS hD]
    exact ne_top_of_le_ne_top hfin (klDiv_map_le (μ := D) (ν := ν) hS)
  have h3 := klDiv_eq_klDiv_statisticLift_add_map ν (statisticLift ν D S) (h ∘ S) hhS hLν hLfin
  have hm : (statisticLift ν D S).map (h ∘ S) = D.map (h ∘ S) := by
    rw [← Measure.map_map hh hS, map_statisticLift ν D S hS hD, Measure.map_map hh hS]
  rw [statisticLift_statisticLift ν D S h hS hh hD, hm] at h3
  have h5 := klDiv_statisticLift_eq_map ν D S hS hD
  have hTfin : klDiv (D.map (h ∘ S)) (ν.map (h ∘ S)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (klDiv_map_le (μ := D) (ν := ν) hhS)
  refine (ENNReal.add_left_inj hTfin).1 ?_
  rw [← h1, h2, ← h5, h3]
  ring

end Tower

end Laplace.Multi
