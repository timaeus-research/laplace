/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.StraightPathAtlas

/-!
# Boundary compactification of the atlas: laws converge while parameters escape

Let `M` be a finite-rate response on the relative boundary of the moment body, `M_s` the straight
path from the featureless response, and `θ_s = θ(M_s) ∈ 𝕍` its natural coordinates (defined for
`s < 1`, where `M_s` lies in the relative interior). Then

  `‖θ_s‖ → ∞` as `s ↑ 1`                                          (`tendsto_norm_atlasTheta_atTop`)

by compactness: a bounded subsequence of parameters would accumulate at some `θ* ∈ 𝕍`, and by
continuity of the mean map `m(θ*) = lim M_s = M`, so `M` would lie in the image of the chart, which
is the relative interior (`range_meanMap_eq_intrinsicInterior_momentBody`).

Together with the endpoint convergence `KL(Π(M) ‖ P_{θ_s}) → 0` this is the boundary picture of the
atlas: the laws `P_{θ_s}` converge (in information, hence in total variation) to the completed
representative `Π_ν(M)`, while their natural coordinates leave every bounded region of `𝕍`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The natural coordinates of the atlas invert the mean map along the path. -/
theorem meanMap_atlasTheta {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s) = atlasPath S ν M s :=
  meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (atlas_mem_intrinsicInterior hS ν hfin hs0 hs1)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hfin in
/-- The straight path is continuous. -/
theorem continuous_atlasPath : Continuous (atlasPath S ν M) := by
  unfold atlasPath
  fun_prop

/-- **Parameter escape at boundary responses**: if the finite-rate response `M` is not in the
relative interior of the moment body, the natural coordinates `θ(M_s)` of the straight path leave
every bounded set of `𝕍` as `s ↑ 1`. -/
theorem tendsto_norm_atlasTheta_atTop
    (hM : M ∉ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    Tendsto (fun s ↦ ‖atlasTheta hS ν M s‖) (𝓝[<] (1 : ℝ)) atTop := by
  by_contra hcon
  simp only [Filter.tendsto_atTop, not_forall, Filter.not_eventually, not_le] at hcon
  obtain ⟨b, hb⟩ := hcon
  have hb' : ∃ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Ioo (0 : ℝ) 1 ∧ ‖atlasTheta hS ν M s‖ < b :=
    (hb.and_eventually (Ioo_mem_nhdsLT zero_lt_one)).mono fun s hs ↦ ⟨hs.2, hs.1⟩
  obtain ⟨u, hu, hpu⟩ := Filter.exists_seq_forall_of_frequently hb'
  obtain ⟨θ, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S)) (r := b))
    (x := fun n ↦ atlasTheta hS ν M (u n))
    (fun n ↦ mem_closedBall_zero_iff.2 (hpu n).2.le)
  have hcont : Continuous (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1) :=
    continuous_meanMap measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS one_pos
  have h1 : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M (u (φ n)))) atTop
      (𝓝 (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)) :=
    (hcont.tendsto _).comp (continuous_subtype_val.tendsto _ |>.comp hlim)
  have h2 : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M (u (φ n)))) atTop (𝓝 M) := by
    have hu1 : Tendsto (fun n ↦ u (φ n)) atTop (𝓝 (1 : ℝ)) :=
      (hu.mono_right nhdsWithin_le_nhds).comp hφ.tendsto_atTop
    have := ((continuous_atlasPath ν (S := S) (M := M)).tendsto 1).comp hu1
    rw [atlasPath_one] at this
    refine this.congr fun n ↦ ?_
    exact (meanMap_atlasTheta hS ν hfin (hpu (φ n)).1.1.le (hpu (φ n)).1.2).symm
  have hθ : meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ = M := tendsto_nhds_unique h1 h2
  apply hM
  rw [← range_meanMap_eq_intrinsicInterior_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS]
  exact ⟨θ, hθ⟩

end Laplace.Multi
