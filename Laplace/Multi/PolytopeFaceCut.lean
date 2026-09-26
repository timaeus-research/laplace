/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BoundaryRayFormula

/-!
# Supporting cuts of a polytope and the moment body of a face

**Geometry**: a supporting hyperplane cuts a finite convex hull along the hull of its tight
generators, `conv V ∩ {⟨u,·⟩ = β} = conv {v ∈ V | ⟨u,v⟩ = β}` when `⟨u,v⟩ ≤ β` on `V`
(`convexHull_inter_hyperplane`): the weighted slacks `w_v(β − ⟨u,v⟩)` are nonnegative and sum to
zero, so every positive weight sits on a tight generator.

**Measure theory**: on a charged polytope the conditioned law `ν(· | ⟨u,S⟩ = β)` has moment body
exactly the exposed face (`momentBody_faceMeasure_eq_of_exposed`): the upper inclusion is the
seabed's conditioning lemma, the lower one uses that the tight generators stay charged after
conditioning. Hence the boundary-ray theorem applies to every response in the relative interior of
an exposed face of the polytope (`exists_ray_tendsto_responseProjection_polytope`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Geometry

variable {J : Type*} [Fintype J]

theorem dotJ_finset_sum_smul (u : J → ℝ) (T : Finset (J → ℝ)) (w : (J → ℝ) → ℝ) :
    dotJ u (∑ v ∈ T, w v • v) = ∑ v ∈ T, w v * dotJ u v := by
  change (IsLinearMap.mk' (dotJ u) (isLinearMap_dotJ u)) (∑ v ∈ T, w v • v) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun v _ ↦ by rw [map_smul, smul_eq_mul]; rfl

theorem convex_hyperplane_dotJ (u : J → ℝ) (β : ℝ) : Convex ℝ {y : J → ℝ | dotJ u y = β} := by
  intro y hy z hz a b ha hb hab
  simp only [mem_ofPred_eq] at hy hz ⊢
  rw [(isLinearMap_dotJ u).map_add, (isLinearMap_dotJ u).map_smul, (isLinearMap_dotJ u).map_smul,
    hy, hz, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]

theorem convex_halfspace_dotJ (u : J → ℝ) (β : ℝ) : Convex ℝ {y : J → ℝ | dotJ u y ≤ β} := by
  intro y hy z hz a b ha hb hab
  simp only [mem_ofPred_eq] at hy hz ⊢
  rw [(isLinearMap_dotJ u).map_add, (isLinearMap_dotJ u).map_smul, (isLinearMap_dotJ u).map_smul,
    smul_eq_mul, smul_eq_mul]
  calc a * dotJ u y + b * dotJ u z ≤ a * β + b * β :=
        add_le_add (mul_le_mul_of_nonneg_left hy ha) (mul_le_mul_of_nonneg_left hz hb)
    _ = β := by rw [← add_mul, hab, one_mul]

/-- **A supporting hyperplane cuts a finite hull along the hull of its tight generators.** -/
theorem convexHull_inter_hyperplane (V : Finset (J → ℝ)) (u : J → ℝ) (β : ℝ)
    (hV : ∀ v ∈ V, dotJ u v ≤ β) :
    convexHull ℝ (V : Set (J → ℝ)) ∩ {y | dotJ u y = β} =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) := by
  ext y
  constructor
  · rintro ⟨hy, hyβ⟩
    simp only [mem_ofPred_eq] at hyβ
    obtain ⟨w, hw0, hw1, hwy⟩ := Finset.mem_convexHull'.1 hy
    have hslack : ∑ v ∈ V, w v * (β - dotJ u v) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      rw [← dotJ_finset_sum_smul, hwy, hyβ, sub_self]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun v hv ↦
      mul_nonneg (hw0 v hv) (sub_nonneg.2 (hV v hv))).1 hslack
    have htight : ∀ v ∈ V, v ∉ V.filter (fun v ↦ dotJ u v = β) → w v = 0 := fun v hv hvf ↦ by
      rcases mul_eq_zero.1 (hzero v hv) with h | h
      · exact h
      · exact absurd (Finset.mem_filter.2 ⟨hv, (sub_eq_zero.1 h).symm⟩) hvf
    refine Finset.mem_convexHull'.2 ⟨w, fun v hv ↦ hw0 v (Finset.mem_filter.1 hv).1, ?_, ?_⟩
    · rw [← hw1]
      exact Finset.sum_subset (Finset.filter_subset _ _) fun v hv hvf ↦ htight v hv hvf
    · rw [← hwy]
      exact Finset.sum_subset (Finset.filter_subset _ _) fun v hv hvf ↦ by
        rw [htight v hv hvf, zero_smul]
  · intro hy
    refine ⟨convexHull_mono (Finset.coe_subset.2 (Finset.filter_subset _ _)) hy, ?_⟩
    refine convexHull_min (fun v hv ↦ ?_) (convex_hyperplane_dotJ u β) hy
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2

end Geometry

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (u : J → ℝ) (β : ℝ)
include hS

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- A half-space bound on the polytope is an a.e. bound on the statistic. -/
theorem ae_dirLoss_le_of_polytope
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hV : ∀ v ∈ V, dotJ u v ≤ β) : ∀ᵐ x ∂ν, dirLoss S u x ≤ β := by
  filter_upwards [ae_statPoint_mem_essRange (μ := ν) measurable_const (fun _ ↦ one_pos) hS]
    with x hx
  have hmem : statPoint S x ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := essRange_subset_momentBody S hx
  rw [hpoly] at hmem
  have := convexHull_min (fun v hv ↦ hV v (Finset.mem_coe.1 hv)) (convex_halfspace_dotJ u β) hmem
  exact this

omit [Nonempty X] [Nonempty J] in
/-- Tight generators stay charged after conditioning on the face fibre. -/
theorem faceMeasure_statFibre_pos {v : J → ℝ} (hv : 0 < ν.real (statFibre S v))
    (hvβ : dotJ u v = β) (hp : 0 < ν.real {x | dirLoss S u x = β}) :
    0 < faceMeasure ν {x | dirLoss S u x = β} (statFibre S v) := by
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  rw [faceMeasure, Measure.smul_apply, Measure.restrict_apply (measurableSet_statFibre hS v),
    smul_eq_mul]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) ?_
  have hsub : statFibre S v ⊆ statFibre S v ∩ {x | dirLoss S u x = β} := fun x hx ↦ by
    refine ⟨hx, ?_⟩
    have hx' : statPoint S x = v := hx
    change dirLoss S u x = β
    rw [← hvβ, ← hx']
    rfl
  exact (lt_of_lt_of_le (ENNReal.toReal_pos_iff.1 hv).1 (measure_mono hsub)).ne'

omit [Nonempty X] [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **The moment body of the conditioned law is the exposed face of the polytope.** -/
theorem momentBody_faceMeasure_eq_of_exposed
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) (hV : ∀ v ∈ V, dotJ u v ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) :
    momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) := by
  have hF := measurableSet_faceFibre hS u β
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  rw [← convexHull_inter_hyperplane V u β hV, ← hpoly]
  refine subset_antisymm (fun y hy ↦ ⟨momentBody_faceMeasure_subset ν hF hS hp hy,
    momentBody_faceMeasure_subset_hyperplane ν hF hS hp rfl hy⟩) ?_
  rw [hpoly, convexHull_inter_hyperplane V u β hV]
  refine convexHull_min (fun v hv ↦ ?_) (convex_momentBody S)
  obtain ⟨hvV, hvβ⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hv)
  refine essRange_subset_momentBody S ?_
  rw [mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS]
  intro r hr
  refine (faceMeasure_statFibre_pos hS ν u β (hcharged v hvV) hvβ hp).trans_le
    (measure_mono fun x hx ↦ ?_)
  have hx' : statPoint S x = v := hx
  change statPoint S x ∈ Metric.ball v r
  rw [hx']
  exact Metric.mem_ball_self hr

/-- **Boundary rays on a charged polytope**: every response in the relative interior of an exposed
face is the total-variation limit of an explicit natural ray with exact rate `2B_t/(A + B_t)`. -/
theorem exists_ray_tendsto_responseProjection_polytope
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) (hV : ∀ v ∈ V, dotJ u v ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {M : J → ℝ} (hM : dotJ u M = β)
    (hrel : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))) :
    ∃ θ : J → ℝ,
      responseProjection hS ν M = ν.withDensity (fun x ↦ ENNReal.ofReal (faceDens S ν θ u β x)) ∧
      (∀ t, ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν =
        2 * offFaceMass S ν θ u β t / (faceMass S ν θ u β + offFaceMass S ν θ u β t)) ∧
      Tendsto (fun t : ℝ ↦ ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν) atTop
        (𝓝 0) :=
  exists_ray_tendsto_responseProjection hS ν u β (ae_dirLoss_le_of_polytope hS ν V u β hpoly hV)
    hp hM (by rwa [momentBody_faceMeasure_eq_of_exposed hS ν V u β hpoly hcharged hV hp])

end Face

end Laplace.Multi
