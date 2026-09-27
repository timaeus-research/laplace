/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherMeanControl

/-!
# The intrinsic Fisher distance on the direction space

`fisherDist S ν x y = inf { L(p) | p a flat C¹ path in W from x to y }`. It is a metric on `W`:
nonnegative, zero on the diagonal (constant path), symmetric (reversal), satisfies the triangle
inequality (concatenation of near-minimisers), is bounded by `K ‖y − x‖` (flattened segment), and
separates points because the mean map is `B`-Lipschitz for it and injective on `W`.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Def

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (S : J → X → ℝ) (ν : Measure X)

/-- The set of lengths of flat `C¹` paths from `x` to `y`. -/
def fisherLengths (x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : Set ℝ :=
  {L | ∃ p : FisherPath S ν x y, p.length = L}

/-- **The intrinsic Fisher distance.** -/
noncomputable def fisherDist (x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : ℝ :=
  sInf (fisherLengths S ν x y)

variable {S ν} {x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S}

theorem fisherLengths_nonempty : (fisherLengths S ν x y).Nonempty :=
  ⟨_, FisherPath.segment x y, rfl⟩

theorem fisherLengths_bddBelow : BddBelow (fisherLengths S ν x y) :=
  ⟨0, fun _ ⟨p, hp⟩ ↦ hp ▸ p.length_nonneg⟩

theorem fisherDist_le_length (p : FisherPath S ν x y) : fisherDist S ν x y ≤ p.length :=
  csInf_le fisherLengths_bddBelow ⟨p, rfl⟩

theorem fisherDist_nonneg : 0 ≤ fisherDist S ν x y :=
  Real.sInf_nonneg fun _ ⟨p, hp⟩ ↦ hp ▸ p.length_nonneg

/-- Near-minimising paths exist. -/
theorem exists_fisherPath_length_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ p : FisherPath S ν x y, p.length < fisherDist S ν x y + ε := by
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := Real.lt_sInf_add_pos (fisherLengths_nonempty (x := x) (y := y)) hε
  exact ⟨p, hp⟩

end Def

section Metric

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

variable {x y z : dirSpan ν (fun _ ↦ (1 : ℝ)) S}

theorem fisherDist_self (x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : fisherDist S ν x x = 0 :=
  le_antisymm ((fisherDist_le_length (FisherPath.const x)).trans_eq
    (FisherPath.length_const hS ν x)) fisherDist_nonneg

theorem fisherDist_comm_le : fisherDist S ν x y ≤ fisherDist S ν y x :=
  le_csInf fisherLengths_nonempty fun _ ⟨p, hp⟩ ↦
    hp ▸ (fisherDist_le_length p.rev).trans_eq (FisherPath.length_rev hS ν p)

theorem fisherDist_comm : fisherDist S ν x y = fisherDist S ν y x :=
  le_antisymm (fisherDist_comm_le hS ν) (fisherDist_comm_le hS ν)

/-- **The triangle inequality.** -/
theorem fisherDist_triangle (x y z : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    fisherDist S ν x z ≤ fisherDist S ν x y + fisherDist S ν y z := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨p, hp⟩ := exists_fisherPath_length_lt (x := x) (y := y) (half_pos hε)
  obtain ⟨q, hq⟩ := exists_fisherPath_length_lt (x := y) (y := z) (half_pos hε)
  calc fisherDist S ν x z ≤ (p.cat q).length := fisherDist_le_length _
    _ = p.length + q.length := FisherPath.length_cat hS ν p q
    _ < fisherDist S ν x y + fisherDist S ν y z + ε := by linarith

/-- **The segment bound**: `d_F(x,y) ≤ K ‖y − x‖`. -/
theorem fisherDist_le_mul_norm {K : ℝ} (hK : ∀ θ w : J → ℝ, fisherNorm S ν θ w ≤ K * ‖w‖)
    (x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : fisherDist S ν x y ≤ K * ‖y - x‖ :=
  (fisherDist_le_length _).trans (FisherPath.length_segment_le hS ν hK x y)

/-- **The mean map is `B`-Lipschitz for the Fisher distance.** -/
theorem norm_meanMap_sub_le_fisherDist {B : ℝ} (hB : ∀ i x, |S i x| ≤ B) (hB0 : 0 ≤ B)
    (x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    ‖mean (y : J → ℝ) - mean (x : J → ℝ)‖ ≤ B * fisherDist S ν x y := by
  rcases eq_or_lt_of_le hB0 with hB' | hB'
  · obtain ⟨p, -⟩ := exists_fisherPath_length_lt (x := x) (y := y) one_pos
    have := norm_meanMap_sub_le_length hS ν p hB hB0
    rw [← hB'] at this ⊢
    simpa using this
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨p, hp⟩ := exists_fisherPath_length_lt (x := x) (y := y) (div_pos hε hB')
    calc ‖mean (y : J → ℝ) - mean (x : J → ℝ)‖ ≤ B * p.length :=
          norm_meanMap_sub_le_length hS ν p hB hB0
      _ ≤ B * (fisherDist S ν x y + ε / B) := mul_le_mul_of_nonneg_left hp.le hB0
      _ = B * fisherDist S ν x y + ε := by field_simp

/-- **Positivity**: the Fisher distance separates points of `W`. -/
theorem eq_of_fisherDist_eq_zero [Nonempty J] (h : fisherDist S ν x y = 0) : x = y := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  have h1 := norm_meanMap_sub_le_fisherDist hS ν hB hB0 x y
  rw [h, mul_zero, norm_le_zero_iff, sub_eq_zero] at h1
  have h2 : chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS x = chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS y := by
    apply Subtype.ext
    rw [chartV_apply, chartV_apply, h1]
  rw [← chartVInv_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS x, h2, chartVInv_chartV]

theorem fisherDist_eq_zero_iff [Nonempty J] : fisherDist S ν x y = 0 ↔ x = y :=
  ⟨eq_of_fisherDist_eq_zero hS ν, fun h ↦ h ▸ fisherDist_self hS ν x⟩

end Metric

end Laplace.Multi
