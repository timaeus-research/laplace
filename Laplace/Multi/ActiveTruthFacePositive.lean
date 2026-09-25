/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthTheorem

/-!
# Positive face volume

Astra round 10, item 2: under the nondegeneracy `(c_j, a_j) ≠ (0, 0)`, the limiting polytope
`F' = {w ≥ 0 | c_j·w ≤ a_j}` has positive volume iff it has a strictly interior point
`w > 0`, `c_j·w < a_j` (`volume_poly2_pos_iff`): the open part is a nonempty open set, and the
boundary is contained in the null hyperplanes. In the original coordinates this is the face
`{α ≥ 0 | κ·α = δ, Q·α = γ}` having a point with all `α_j > 0`.
-/

open MeasureTheory Set Filter Topology
open scoped Matrix

namespace Laplace.Multi

variable {k : ℕ}

theorem continuous_dotProduct_left (c : Fin k → ℝ) : Continuous fun x : Fin k → ℝ ↦ c ⬝ᵥ x := by
  unfold dotProduct
  exact continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_apply i)

/-- The strict interior of the polytope is open. -/
theorem isOpen_poly2_interior (c₁ c₂ : Fin k → ℝ) (a₁ a₂ : ℝ) :
    IsOpen {w : Fin k → ℝ | (∀ i, 0 < w i) ∧ c₁ ⬝ᵥ w < a₁ ∧ c₂ ⬝ᵥ w < a₂} := by
  have h1 : IsOpen {w : Fin k → ℝ | ∀ i, 0 < w i} := by
    rw [orthantSet_eq_pi]
    exact isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioi
  have h2 : IsOpen {w : Fin k → ℝ | c₁ ⬝ᵥ w < a₁} :=
    isOpen_lt (continuous_dotProduct_left c₁) continuous_const
  have h3 : IsOpen {w : Fin k → ℝ | c₂ ⬝ᵥ w < a₂} :=
    isOpen_lt (continuous_dotProduct_left c₂) continuous_const
  exact (h1.inter (h2.inter h3))

/-- **Positive face volume iff a strictly interior point**, under nondegeneracy. -/
theorem volume_poly2_pos_iff {c₁ c₂ : Fin k → ℝ} {a₁ a₂ : ℝ} (h₁ : c₁ ≠ 0 ∨ a₁ ≠ 0)
    (h₂ : c₂ ≠ 0 ∨ a₂ ≠ 0) :
    0 < volume (poly2 c₁ c₂ a₁ a₂) ↔
      ∃ w : Fin k → ℝ, (∀ i, 0 < w i) ∧ c₁ ⬝ᵥ w < a₁ ∧ c₂ ⬝ᵥ w < a₂ := by
  constructor
  · intro hpos
    by_contra hno
    push Not at hno
    have hsub : poly2 c₁ c₂ a₁ a₂ ⊆ ({x : Fin k → ℝ | c₁ ⬝ᵥ x = a₁} ∪ {x | c₂ ⬝ᵥ x = a₂} ∪
        ⋃ i, {x : Fin k → ℝ | x i = 0}) := by
      intro w hw
      by_cases hi : ∃ i, w i = 0
      · obtain ⟨i, hi⟩ := hi
        exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
      · push Not at hi
        have hw0 : ∀ i, 0 < w i := fun i ↦ lt_of_le_of_ne (hw.1 i) (Ne.symm (hi i))
        by_cases hc1 : c₁ ⬝ᵥ w = a₁
        · exact Or.inl (Or.inl hc1)
        · have hlt1 : c₁ ⬝ᵥ w < a₁ := lt_of_le_of_ne hw.2.1 hc1
          have := hno w hw0 hlt1
          exact Or.inl (Or.inr (le_antisymm hw.2.2 this))
    have hnull : volume ({x : Fin k → ℝ | c₁ ⬝ᵥ x = a₁} ∪ {x | c₂ ⬝ᵥ x = a₂} ∪
        ⋃ i, {x : Fin k → ℝ | x i = 0}) = 0 :=
      measure_union_null (measure_union_null (volume_hyperplane' h₁) (volume_hyperplane' h₂))
        (measure_iUnion_null fun i ↦ volume_coordHyperplane i)
    exact hpos.ne' (measure_mono_null hsub hnull)
  · rintro ⟨w, hw0, hw1, hw2⟩
    have hopen := isOpen_poly2_interior c₁ c₂ a₁ a₂
    have hne : {w : Fin k → ℝ | (∀ i, 0 < w i) ∧ c₁ ⬝ᵥ w < a₁ ∧ c₂ ⬝ᵥ w < a₂}.Nonempty :=
      ⟨w, hw0, hw1, hw2⟩
    refine lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono fun x hx ↦ ?_)
    exact ⟨fun i ↦ (hx.1 i).le, hx.2.1.le, hx.2.2.le⟩


end Laplace.Multi
