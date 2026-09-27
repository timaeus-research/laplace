/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AccessibleFaceStratification

/-!
# Finite essential range: the support gap of an exposed face

A statistic with **finite essential support** `V` — `statPoint S ∈ V` almost surely, every fibre
over `V` charged — has moment body the polytope `conv V` (`momentBody_eq_convexHull_of_finiteRange`,
`essRange_eq_of_finiteRange`), so it is a charged polytope model. For an exposed face
`{⟨u,S⟩ = β}` with `⟨u,v⟩ ≤ β` on `V`, the **support gap**

`faceGap V u β = min {β − ⟨u,v⟩ : v ∈ V, ⟨u,v⟩ < β}`

is positive (`faceGap_pos`), and almost surely the statistic is either on the face or at least the
gap below it (`ae_face_or_le_sub_gap`). Face models inherit finite essential support on the tight
vertices (`ae_statPoint_mem_tight_faceMeasure`). These are the inputs of the exponential ray
decay that makes every face accessible.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Gap

variable {J : Type*} [Fintype J] (V : Finset (J → ℝ)) (u : J → ℝ) (β : ℝ)

/-- The off-face vertices. -/
noncomputable def offFaceVertices : Finset (J → ℝ) := V.filter fun v ↦ dotJ u v < β

open Classical in
/-- **The support gap** of the exposed face `{⟨u,·⟩ = β}`: the least slack of an off-face vertex
(`1` when there is none). -/
noncomputable def faceGap : ℝ :=
  if h : (offFaceVertices V u β).Nonempty then
    ((offFaceVertices V u β).image fun v ↦ β - dotJ u v).min'
      (Finset.image_nonempty.2 h)
  else 1

theorem faceGap_pos : 0 < faceGap V u β := by
  unfold faceGap
  split_ifs with h
  · refine (Finset.lt_min'_iff _ _).2 fun y hy ↦ ?_
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    have := (Finset.mem_filter.1 hv).2
    linarith
  · exact one_pos

/-- The gap is at most the slack of every off-face vertex. -/
theorem faceGap_le {v : J → ℝ} (hv : v ∈ V) (hlt : dotJ u v < β) :
    faceGap V u β ≤ β - dotJ u v := by
  unfold faceGap
  have hmem : v ∈ offFaceVertices V u β := Finset.mem_filter.2 ⟨hv, hlt⟩
  rw [dif_pos ⟨v, hmem⟩]
  exact Finset.min'_le _ _ (Finset.mem_image.2 ⟨v, hmem, rfl⟩)

end Gap

section Range

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (hae : ∀ᵐ x ∂ν, statPoint S x ∈ V)
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hae hcharged

omit [IsProbabilityMeasure ν] hcharged in
set_option linter.unusedFintypeInType false in
/-- The essential range of a finitely supported statistic lies in the support. -/
theorem essRange_subset_of_finiteRange : essRange ν (fun _ ↦ (1 : ℝ)) S ⊆ V := by
  intro y hy
  rw [mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS] at hy
  by_contra hyV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (V.finite_toSet.isClosed.isOpen_compl) y hyV
  have h0 : ν (statPoint S ⁻¹' Metric.ball y ε) = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_) (ae_iff.1 hae)
    exact hball hx
  exact (hy ε hε).ne' h0

omit [IsProbabilityMeasure ν] hae in
set_option linter.unusedFintypeInType false in
/-- Every charged support point lies in the essential range. -/
theorem subset_essRange_of_charged : (V : Set (J → ℝ)) ⊆ essRange ν (fun _ ↦ (1 : ℝ)) S := by
  intro v hv
  rw [mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS]
  intro r hr
  refine lt_of_lt_of_le (b := ν (statFibre S v)) ?_ (measure_mono fun x hx ↦ ?_)
  · exact (ENNReal.toReal_pos_iff.1 (hcharged v hv)).1
  · change statPoint S x ∈ Metric.ball v r
    have hx' : statPoint S x = v := hx
    rw [hx']
    exact Metric.mem_ball_self hr

omit [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **The essential range of a finitely supported statistic is its charged support.** -/
theorem essRange_eq_of_finiteRange : essRange ν (fun _ ↦ (1 : ℝ)) S = V :=
  le_antisymm (essRange_subset_of_finiteRange hS ν V hae)
    (subset_essRange_of_charged hS ν V hcharged)

omit [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **Finite essential support gives a charged polytope**: `momentBody = conv V`. -/
theorem momentBody_eq_convexHull_of_finiteRange :
    momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)) := by
  rw [momentBody, essRange_eq_of_finiteRange hS ν V hae hcharged]
  exact (V.finite_toSet.isClosed_convexHull (𝕜 := ℝ)).closure_eq

omit hS [IsProbabilityMeasure ν] hcharged in
/-- Almost surely the statistic lies below an exposing hyperplane of the polytope. -/
theorem ae_dirLoss_le_of_finiteRange {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) :
    ∀ᵐ x ∂ν, dirLoss S u x ≤ β := by
  filter_upwards [hae] with x hx
  rw [dirLoss_eq_dotJ_statPoint]
  exact hV _ hx

omit hS [IsProbabilityMeasure ν] hcharged in
/-- **The a.e. gap dichotomy**: almost surely the statistic is on the face or at least the support
gap below it. -/
theorem ae_face_or_le_sub_gap {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) :
    ∀ᵐ x ∂ν, dirLoss S u x = β ∨ dirLoss S u x ≤ β - faceGap V u β := by
  filter_upwards [hae] with x hx
  rw [dirLoss_eq_dotJ_statPoint]
  rcases (hV _ hx).lt_or_eq with hlt | heq
  · right
    linarith [faceGap_le V u β hx hlt]
  · left
    exact heq

omit [IsProbabilityMeasure ν] hcharged in
/-- **Face models have finite essential support on the tight vertices.** -/
theorem ae_statPoint_mem_tight_faceMeasure {u : J → ℝ} {β : ℝ} :
    ∀ᵐ x ∂faceMeasure ν {x | dirLoss S u x = β},
      statPoint S x ∈ (V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) := by
  have hF := measurableSet_faceFibre hS u β
  have hae' : ∀ᵐ x ∂faceMeasure ν {x | dirLoss S u x = β}, statPoint S x ∈ V := by
    rw [faceMeasure, ae_iff, Measure.smul_apply, ae_iff.1 (ae_restrict_of_ae hae), smul_zero]
  filter_upwards [hae', ae_mem_faceMeasure ν hF] with x hx hxF
  refine Finset.mem_filter.2 ⟨hx, ?_⟩
  have hxF' : dirLoss S u x = β := hxF
  rwa [dirLoss_eq_dotJ_statPoint] at hxF'

end Range

end Laplace.Multi
