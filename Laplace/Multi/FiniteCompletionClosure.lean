/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteMinimalFace

/-!
# The completed family is the closure of the exponential family

On a finite alphabet with a full-support reference law:

* `essRange_eq_range_statPoint`: the essential range of the features is the whole feature set,
  so the moment body is the moment polytope `conv S(X)` (`momentBody_eq_convexHull`);
* on the relative interior of the polytope the completed family is the exponential family
  (`vecMeasure_qStarVec_eq_familyMeasure`), and **the completed family is the closure of the
  interior exponential family** (`closure_interiorFamily`): every boundary law is the limit of the
  family members along the straight atlas ray towards it.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] [Fintype J] [Nonempty J]
  [IsProbabilityMeasure ν] in
/-- **The essential range of a full-support finite alphabet is the whole feature set.** -/
theorem essRange_eq_range_statPoint [Finite X] [Finite J] :
    essRange ν (fun _ ↦ (1 : ℝ)) S = range (statPoint S) := by
  cases nonempty_fintype J
  ext y
  rw [mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS]
  constructor
  · intro h
    by_contra hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (finite_range (statPoint S)).isClosed.isOpen_compl
      y hy
    have h0 : statPoint S ⁻¹' Metric.ball y ε = ∅ :=
      eq_empty_iff_forall_notMem.2 fun x hx ↦ hball hx ⟨x, rfl⟩
    have := h ε hε
    rw [h0, measure_empty] at this
    exact lt_irrefl _ this
  · rintro ⟨x, rfl⟩ r hr
    refine lt_of_lt_of_le (hν x) (measure_mono ?_)
    intro z hz
    rw [mem_singleton_iff] at hz
    subst hz
    exact Metric.mem_ball_self hr

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] [Fintype J] [Nonempty J]
  [IsProbabilityMeasure ν] in
/-- **The moment body is the moment polytope.** -/
theorem momentBody_eq_convexHull [Finite X] [Finite J] :
    momentBody ν (fun _ ↦ (1 : ℝ)) S = hull := by
  cases nonempty_fintype J
  unfold momentBody
  rw [essRange_eq_range_statPoint hS ν hν]
  exact ((finite_range (statPoint S)).isCompact_convexHull (𝕜 := ℝ)).isClosed.closure_eq

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] [Fintype J] [Nonempty J]
  [IsProbabilityMeasure ν] in
theorem intrinsicInterior_subset_hull [Finite X] [Finite J] : Ω ⊆ hull := by
  rw [← momentBody_eq_convexHull hS ν hν]
  exact intrinsicInterior_subset

omit [Fintype X] hν in
/-- On the relative interior the completed family is the exponential family. -/
theorem vecMeasure_qStarVec_eq_familyMeasure [Finite X] {M : J → ℝ} (hrel : M ∈ Ω) :
    vecMeasure (qStarVec hS ν M) = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS M) := by
  cases nonempty_fintype X
  rw [vecMeasure_qStarVec hS ν (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel)]
  exact responseProjection_eq_familyMeasure_responseTheta hS ν hrel

omit hν in
/-- The interior exponential family as a set of probability vectors. -/
def interiorFamily : Set (X → ℝ) := qStarVec hS ν '' Ω

omit [Fintype X] in
/-- **The completed family is the closure of the interior exponential family.** -/
theorem closure_interiorFamily [Finite X] :
    closure (interiorFamily hS ν) = completedFamily hS ν := by
  cases nonempty_fintype X
  refine subset_antisymm ?_ fun p hp ↦ ?_
  · refine closure_minimal (Set.image_mono (intrinsicInterior_subset_hull hS ν hν))
      (isCompact_completedFamily hS ν hν).isClosed
  · obtain ⟨M, hM, rfl⟩ := hp
    have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
    -- the atlas ray `s_n = 1 − 1/(n+2)` towards `M`
    obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 2) := ⟨_, rfl⟩
    have hu0 : ∀ n, 0 ≤ u n := fun n ↦ by
      rw [hu]
      have h2 : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      simp only
      linarith
    have hu1 : ∀ n, u n < 1 := fun n ↦ by
      rw [hu]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      simp only
      linarith
    have hulim : Tendsto u atTop (𝓝 1) := by
      rw [hu]
      have h' : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub h'
      rwa [sub_zero] at this
    have hpath : Tendsto (fun n ↦ atlasPath S ν M (u n)) atTop (𝓝 M) := by
      have hc : ContinuousAt (atlasPath S ν M) 1 :=
        (hasDerivAt_atlasPath ν (S := S) (M := M) 1).continuousAt
      have := hc.tendsto.comp hulim
      rwa [atlasPath_one] at this
    have hmem : ∀ n, atlasPath S ν M (u n) ∈ Ω := fun n ↦
      atlas_mem_intrinsicInterior hS ν hfin (hu0 n) (hu1 n)
    refine mem_closure_of_tendsto (tendsto_qStarVec hS ν hν hM
      (fun n ↦ intrinsicInterior_subset_hull hS ν hν (hmem n)) hpath)
      (Eventually.of_forall fun n ↦ mem_image_of_mem _ (hmem n))

end Laplace.Multi
