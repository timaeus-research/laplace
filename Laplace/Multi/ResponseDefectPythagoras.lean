/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseBregman

/-!
# The response defect as the distance to the whole family

For a data law `ρ` of finite information with response `M = E_ρ S`, and every interior response
`N`, the Pythagorean identity in mean coordinates reads

  `D(ρ ‖ q_N) = D(ρ ‖ q_M) + D(q_M ‖ q_N)`   (`klDiv_responseProjection_eq_add`).

Hence the response defect `D(ρ ‖ q_M)` is the minimum of `D(ρ ‖ q_N)` over the family
(`klDiv_responseProjection_le`, `responseDefect_eq_iInf`), attained exactly at the response
projection, and the response projection is a one-sided KL contraction:
`D(q_M ‖ q_N) ≤ D(ρ ‖ q_N)` (`klDiv_responseProjection_le_klDiv`).  These are the global forms of
the defect decomposition `D(ρ‖ν) = I(M) + ℰ` of `ResponseDefect`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Pythagoras

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (ρ : Measure X) [IsProbabilityMeasure ρ] (hρ : klDiv ρ ν ≠ ⊤)
include hS hρ

/-- **The Pythagorean identity in mean coordinates**: for every interior response `N`,
`D(ρ ‖ q_N) = D(ρ ‖ q_{E_ρ S}) + D(q_{E_ρ S} ‖ q_N)`. -/
theorem klDiv_responseProjection_eq_add {N : J → ℝ}
    (hN : N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv ρ (responseProjection hS ν N) =
      klDiv ρ (responseProjection hS ν fun i ↦ ∫ x, S i x ∂ρ) +
        klDiv (responseProjection hS ν fun i ↦ ∫ x, S i x ∂ρ) (responseProjection hS ν N) := by
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hN]
  exact klDiv_familyMeasure_eq_add_projection hS ν ρ hρ _

/-- **The response projection is the closest family member**: `D(ρ ‖ q_{E_ρ S}) ≤ D(ρ ‖ q_N)`. -/
theorem klDiv_responseProjection_le {N : J → ℝ}
    (hN : N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv ρ (responseProjection hS ν fun i ↦ ∫ x, S i x ∂ρ) ≤
      klDiv ρ (responseProjection hS ν N) := by
  rw [klDiv_responseProjection_eq_add hS ν ρ hρ hN]
  exact le_self_add

/-- **One-sided KL contraction of the response projection**: `D(q_{E_ρ S} ‖ q_N) ≤ D(ρ ‖ q_N)`. -/
theorem klDiv_responseProjection_le_klDiv {N : J → ℝ}
    (hN : N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv (responseProjection hS ν fun i ↦ ∫ x, S i x ∂ρ) (responseProjection hS ν N) ≤
      klDiv ρ (responseProjection hS ν N) := by
  rw [klDiv_responseProjection_eq_add hS ν ρ hρ hN]
  exact le_add_self

/-- **The defect is the distance from the data law to the family**: when the response of `ρ` is
interior, `D(ρ ‖ q_{E_ρ S}) = ⨅_{N ∈ ri} D(ρ ‖ q_N)`. -/
theorem responseDefect_eq_iInf
    (hM : (fun i ↦ ∫ x, S i x ∂ρ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv ρ (responseProjection hS ν fun i ↦ ∫ x, S i x ∂ρ) =
      ⨅ N : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S),
        klDiv ρ (responseProjection hS ν N) := by
  apply le_antisymm
  · exact le_iInf fun N ↦ klDiv_responseProjection_le hS ν ρ hρ N.2
  · exact iInf_le_of_le ⟨_, hM⟩ le_rfl

end Pythagoras

end Laplace.Multi
