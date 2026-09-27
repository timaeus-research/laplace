/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ExposedFaceRayEndpoint
import Laplace.Multi.AccessibleFaceStrata

/-!
# Finite range: every face is accessible

For a statistic of finite essential range (`hae : ∀ᵐ x ∂ν, statPoint S x ∈ V`, every point of `V`
charged) every exposed face of the polytope `conv V` is accessible, in any codimension, and every
point of the polytope is an extended mean.

The only new ingredient is a **Riesz step**: an exposing functional `⟨u,·⟩` need not have `u` in the
direction space `𝕍`, but the dot product restricted to `𝕍` is an inner product, so there is `u' ∈ 𝕍`
with `⟨u',w⟩ = ⟨u,w⟩` for all `w ∈ 𝕍` (`exists_mem_dotJ_eq_on`). On the polytope, whose direction
space is `𝕍`, the two functionals differ by a constant (`dotJ_eq_add_const_of_finiteRange`), so they
expose the same face with a shifted level `β'`, the face fibres agree `ν`-a.e., and the face laws
and strata coincide (`faceMeasure_congr_ae`, `faceStratum_eq_of_finiteRange`). The normal ray of
`FiniteRangeRayDecay` then reaches the face (`face_accessible_of_finiteRange`); the face strata
theory gives every point of the open face (`exists_meanExt_eq_of_mem_ri_face_finiteRange`), and the
minimal-face decomposition gives every point of the polytope (`meanExt_surjective_of_finiteRange`,
`range_meanExt_eq_convexHull_of_finiteRange`).
-/

open MeasureTheory Filter Topology Set
open scoped Matrix

set_option quotPrecheck false

namespace Laplace.Multi

section Riesz

variable {J : Type*} [Fintype J]

/-- **Riesz on a subspace of `J → ℝ`**: every dot-product functional agrees on `W` with the
functional of a vector of `W`. -/
theorem exists_mem_dotJ_eq_on (W : Submodule ℝ (J → ℝ)) (u : J → ℝ) :
    ∃ u' ∈ W, ∀ w ∈ W, dotJ u' w = dotJ u w := by
  let K : Submodule ℝ (EuclideanSpace ℝ J) :=
    W.comap (WithLp.linearEquiv 2 ℝ (J → ℝ) : EuclideanSpace ℝ J →ₗ[ℝ] (J → ℝ))
  have : CompleteSpace K := completeSpace_coe_iff_isComplete.2 K.complete_of_finiteDimensional
  refine ⟨WithLp.ofLp (K.starProjection (WithLp.toLp 2 u)), ?_, fun w hw ↦ ?_⟩
  · have hp : K.starProjection (WithLp.toLp 2 u) ∈ K := K.starProjection_apply_mem _
    exact hp
  · have hwK : WithLp.toLp 2 w ∈ K := by
      change WithLp.ofLp (WithLp.toLp 2 w) ∈ W
      exact hw
    have h0 := K.starProjection_inner_eq_zero (WithLp.toLp 2 u) (WithLp.toLp 2 w) hwK
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, WithLp.ofLp_sub, WithLp.ofLp_toLp,
      dotProduct_sub, sub_eq_zero] at h0
    have e : ∀ a b : J → ℝ, dotJ a b = b ⬝ᵥ a := fun a b ↦ by
      simp [dotJ, dotProduct, mul_comm]
    rw [e, e, h0]

end Riesz

section FiniteRange

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (hae : ∀ᵐ x ∂ν, statPoint S x ∈ V)
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hae hcharged

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit hae in
set_option linter.unusedFintypeInType false in
/-- Differences of charged vertices lie in the direction space. -/
theorem vertex_sub_mem_dirSpan {v z : J → ℝ} (hv : v ∈ V) (hz : z ∈ V) : v - z ∈ 𝕍 :=
  sub_mem_dirSpan_of_mem_momentBody' hS ν
    (essRange_subset_momentBody S (subset_essRange_of_charged hS ν V hcharged hz))
    (essRange_subset_momentBody S (subset_essRange_of_charged hS ν V hcharged hv))

omit hae in
set_option linter.unusedFintypeInType false in
/-- **An exposing functional is, on the vertices, a functional of the direction space plus a
constant.** -/
theorem dotJ_eq_add_const_of_finiteRange (u : J → ℝ) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V) :
    ∃ u' ∈ 𝕍, ∀ v ∈ V, dotJ u' v = dotJ u v + (dotJ u' z₀ - dotJ u z₀) := by
  obtain ⟨u', hu'W, hagree⟩ := exists_mem_dotJ_eq_on 𝕍 u
  refine ⟨u', hu'W, fun v hv ↦ ?_⟩
  have h := hagree _ (vertex_sub_mem_dirSpan hS ν V hcharged hv hz₀V)
  rw [(isLinearMap_dotJ u').map_sub, (isLinearMap_dotJ u).map_sub] at h
  linarith

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hcharged in
/-- Two exposing data with the same vertex behaviour have `ν`-a.e. equal face fibres. -/
theorem faceFibre_ae_eq_of_finiteRange {u u' : J → ℝ} {β β' : ℝ}
    (h : ∀ v ∈ V, dotJ u' v = β' ↔ dotJ u v = β) :
    ({x | dirLoss S u' x = β'} : Set X) =ᵐ[ν] {x | dirLoss S u x = β} := by
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [hae] with x hx
  simp only [dirLoss_eq_dotJ_statPoint]
  exact h _ hx

omit [Nonempty X] hS [IsProbabilityMeasure ν] hae hcharged in
/-- The face law depends only on the `ν`-a.e. class of the face fibre. -/
theorem faceMeasure_congr_ae {E E' : Set X} (h : E =ᵐ[ν] E') :
    faceMeasure ν E = faceMeasure ν E' := by
  rw [faceMeasure, faceMeasure, measure_congr h, Measure.restrict_congr_set h]

omit hcharged in
/-- Exposing data with the same vertex behaviour have the same face stratum. -/
theorem faceStratum_eq_of_finiteRange {u u' : J → ℝ} {β β' : ℝ}
    (h : ∀ v ∈ V, dotJ u' v = β' ↔ dotJ u v = β) :
    faceStratum hS ν u' β' = faceStratum hS ν u β := by
  unfold faceStratum
  rw [faceMeasure_congr_ae ν (faceFibre_ae_eq_of_finiteRange ν V hae h)]

/-- **Every exposed face of a finitely supported model is accessible**, in any codimension: the
face stratum of every exposed face with a tight vertex is nonempty. -/
theorem face_accessible_of_finiteRange {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {z₀ : J → ℝ} (hz₀V : z₀ ∈ V) (hz₀β : dotJ u z₀ = β) : Accessible hS ν u β := by
  obtain ⟨u', hu'W, hkey⟩ := dotJ_eq_add_const_of_finiteRange hS ν V hcharged u hz₀V
  set c := dotJ u' z₀ - dotJ u z₀ with hc
  have hV' : ∀ v ∈ V, dotJ u' v ≤ β + c := fun v hv ↦ by
    rw [hkey v hv]
    linarith [hV v hv]
  have hz₀β' : dotJ u' z₀ = β + c := by rw [hkey z₀ hz₀V, hz₀β]
  have hiff : ∀ v ∈ V, dotJ u' v = β + c ↔ dotJ u v = β := fun v hv ↦ by
    rw [hkey v hv]
    constructor <;> intro h <;> linarith
  have hstr := faceStratum_eq_of_finiteRange hS ν V hae hiff
  unfold Accessible
  rw [← hstr]
  exact accessible_of_ray hS ν (Submodule.zero_mem 𝕍) hu'W
    (ae_dirLoss_le_of_finiteRange ν V hae hV') (faceFibre_pos_of_charged ν V hcharged hz₀V hz₀β')
    (integrableOn_sqrt_raySpeedSq_of_finiteRange hS ν V hae hcharged 0 hV' hz₀V hz₀β')

/-- **Every point of the relative interior of an exposed face is an extended mean** (finite range,
any codimension). -/
theorem exists_meanExt_eq_of_mem_ri_face_finiteRange {u : J → ℝ} {β : ℝ}
    (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V) (hz₀β : dotJ u z₀ = β) {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)) :
    ∃ x : FisherCompletion hS ν, meanExt hS ν x = M := by
  have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
  have : IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β}) :=
    isProbabilityMeasure_faceMeasure_of_real_pos ν (faceFibre_pos_of_charged ν V hcharged hz₀V hz₀β)
  obtain ⟨x₀, hx₀⟩ := face_accessible_of_finiteRange hS ν V hae hcharged hV hz₀V hz₀β
  exact exists_meanExt_eq_of_mem_ri_face hS ν V
    (momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged) hcharged hV hz₀V hz₀β rfl hx₀ rfl
    hM

/-- **Every point of the polytope is an extended mean** (finite range). -/
theorem meanExt_surjective_of_finiteRange {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ∃ x : FisherCompletion hS ν, meanExt hS ν x = M := by
  have : Nonempty V := by
    obtain ⟨z, hz⟩ := convexHull_nonempty_iff.1 ⟨M, hM⟩
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨u, β, hV, hMβ, -, hF⟩ := exists_exposing_minimalFacePoly hM
  obtain ⟨z₀, hz₀V, hz₀β, -⟩ := exists_charged_vertex_on_face V hV hM hMβ
  have hri : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) := by
    have hpoly := momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged
    rw [momentBody_faceMeasure_eq hS ν V hpoly hcharged hV hz₀V hz₀β, ← hF]
    exact mem_intrinsicInterior_minimalFacePoly hM
  exact exists_meanExt_eq_of_mem_ri_face_finiteRange hS ν V hae hcharged hV hz₀V hz₀β hri

/-- **The range of the extended mean map is the whole polytope** (finite range). -/
theorem range_meanExt_eq_convexHull_of_finiteRange :
    Set.range (meanExt hS ν) = convexHull ℝ (V : Set (J → ℝ)) := by
  refine Set.Subset.antisymm ?_ fun M hM ↦ meanExt_surjective_of_finiteRange hS ν V hae hcharged hM
  rintro _ ⟨x, rfl⟩
  have : Nonempty V := by
    obtain ⟨z₀, hz₀V⟩ : ∃ z₀, z₀ ∈ V := by
      by_contra hV
      push Not at hV
      have h0 : ∀ᵐ x ∂ν, False := by
        filter_upwards [hae] with x hx
        exact hV _ hx
      rw [ae_iff] at h0
      simp at h0
    exact ⟨⟨z₀, hz₀V⟩⟩
  exact meanExt_mem_polytope hS ν V (momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged) x

end FiniteRange

end Laplace.Multi
