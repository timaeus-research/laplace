/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolytopeProjectionSupport

/-!
# The face order: absolute continuity between response projections

On a charged polytope the response projection `q_M` is mutually absolutely continuous with the
reference law conditioned on the fibre of the minimal face of `M`
(`responseProjection_absolutelyContinuous_restrict`,
`restrict_minimalFaceFibre_absolutelyContinuous`).  Hence

  `q_M ≪ q_N  ↔  F_M ⊆ F_N`

(`responseProjection_absolutelyContinuous_iff`): the absolute-continuity preorder of the completed
family is the face lattice of the polytope, and the mutual-absolute-continuity classes are exactly
the (relative interiors of the) faces (`responseProjection_equivalent_iff`).  In terms of the
vertex section, `F_M ⊆ F_N` says every vertex charged by `M` is charged by `N`
(`minimalFacePoly_subset_iff`).  This is the stratification of the response atlas.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Fibre

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ}
  (V : Finset (J → ℝ)) [Nonempty V]

omit [MeasurableSpace X] in
/-- The fibre of the minimal face of `M`. -/
def minimalFaceFibre (S : J → X → ℝ) (M : J → ℝ) : Set X :=
  {x | statPoint S x ∈ minimalFacePoly V M}

variable {V}

theorem measurableSet_minimalFaceFibre (hS : ∀ j, Bdd (S j)) (M : J → ℝ) :
    MeasurableSet (minimalFaceFibre V S M) :=
  measurable_statPoint hS ((V.finite_toSet.subset
    (chargedVertices_subset V M)).isCompact_convexHull ℝ).isClosed.measurableSet

omit [MeasurableSpace X] in
theorem statFibre_subset_minimalFaceFibre {M : J → ℝ} {v : J → ℝ} (hv : v ∈ minimalFacePoly V M) :
    statFibre S v ⊆ minimalFaceFibre V S M := by
  intro x hx
  have hx' : statPoint S x = v := hx
  change statPoint S x ∈ minimalFacePoly V M
  rw [hx']
  exact hv

omit [MeasurableSpace X] in
theorem statFibre_subset_compl_minimalFaceFibre {M : J → ℝ} {v : J → ℝ}
    (hv : v ∉ minimalFacePoly V M) : statFibre S v ⊆ (minimalFaceFibre V S M)ᶜ := by
  intro x hx hxF
  have hx' : statPoint S x = v := hx
  have hxF' : statPoint S x ∈ minimalFacePoly V M := hxF
  rw [hx'] at hxF'
  exact hv hxF'

omit [MeasurableSpace X] in
theorem minimalFaceFibre_mono {M N : J → ℝ} (h : minimalFacePoly V M ⊆ minimalFacePoly V N) :
    minimalFaceFibre V S M ⊆ minimalFaceFibre V S N := fun _ hx ↦ h hx

omit [MeasurableSpace X] in
/-- `F_M ⊆ F_N` iff every vertex charged by `M` is charged by `N`. -/
theorem minimalFacePoly_subset_iff {M N : J → ℝ} (hN : N ∈ convexHull ℝ (V : Set (J → ℝ))) :
    minimalFacePoly V M ⊆ minimalFacePoly V N ↔
      ∀ v : V, 0 < vertexSection V M v → 0 < vertexSection V N v := by
  constructor
  · intro h v hv
    rw [vertexSection_pos_iff_mem_minimalFacePoly hN]
    exact h (mem_minimalFacePoly_of_pos V hv)
  · intro h
    refine convexHull_mono ?_
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, h v hv, rfl⟩

end Fibre

section Order

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

omit [Nonempty V] in
/-- The response projection is absolutely continuous with respect to `ν`. -/
theorem responseProjection_absolutelyContinuous_of_mem_polytope {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) : responseProjection hS ν M ≪ ν := by
  rw [responseProjection_eq_withDensity_projDens hS ν
    (genRate_ne_top_of_mem_momentBody_polytope hS ν V hcharged hpoly (hpoly ▸ hM))]
  exact withDensity_absolutelyContinuous _ _

/-- **Essential support in face form**: `q_M` is carried by the fibre of the minimal face. -/
theorem responseProjection_compl_minimalFaceFibre_eq_zero {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    responseProjection hS ν M (minimalFaceFibre V S M)ᶜ = 0 := by
  obtain ⟨u, β, hV, hMβ, -, -, -, hF⟩ := exists_exposing_polytope ν V hcharged hM
  have hac := responseProjection_absolutelyContinuous_of_mem_polytope hS ν V hpoly hcharged hM
  have hnull := responseProjection_compl_faceFibre_eq_zero hS ν V hpoly hcharged hV hM hMβ
  have h1 : ∀ᵐ x ∂responseProjection hS ν M, dirLoss S u x = β := ae_iff.2 hnull
  have h2 : ∀ᵐ x ∂responseProjection hS ν M, statPoint S x ∈ essRange ν (fun _ ↦ (1 : ℝ)) S :=
    hac.ae_le (ae_statPoint_mem_essRange (μ := ν) measurable_const (fun _ ↦ one_pos) hS)
  have h3 : ∀ᵐ x ∂responseProjection hS ν M, x ∈ minimalFaceFibre V S M := by
    filter_upwards [h1, h2] with x hxβ hxP
    have hmem : statPoint S x ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S :=
      essRange_subset_momentBody S hxP
    rw [hpoly] at hmem
    change statPoint S x ∈ minimalFacePoly V M
    rw [hF, ← convexHull_inter_hyperplane V u β hV]
    exact ⟨hmem, by rwa [mem_ofPred_eq, ← dirLoss_eq_dotJ_statPoint]⟩
  exact ae_iff.1 h3

/-- `q_M` is absolutely continuous with respect to `ν` restricted to the face fibre. -/
theorem responseProjection_absolutelyContinuous_restrict {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    responseProjection hS ν M ≪ ν.restrict (minimalFaceFibre V S M) := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h ↦ ?_
  rw [Measure.restrict_apply hs] at h
  have hac := responseProjection_absolutelyContinuous_of_mem_polytope hS ν V hpoly hcharged hM
  refine measure_mono_null (fun x hx ↦ ?_)
    (measure_union_null (hac h)
      (responseProjection_compl_minimalFaceFibre_eq_zero hS ν V hpoly hcharged hM))
  by_cases hxF : x ∈ minimalFaceFibre V S M
  · exact Or.inl ⟨hx, hxF⟩
  · exact Or.inr hxF

omit [MeasurableSpace X] [Nonempty X] hS [IsProbabilityMeasure ν] hpoly hcharged in
/-- The minimal face fibre lies in the face fibre of any exposing functional. -/
theorem minimalFaceFibre_subset_faceFibre {M : J → ℝ} {u : J → ℝ} {β : ℝ}
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))) :
    minimalFaceFibre V S M ⊆ {x | dirLoss S u x = β} := by
  intro x hx
  have hx' : statPoint S x ∈ minimalFacePoly V M := hx
  rw [hF] at hx'
  have hsub : convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) ⊆
      {y | dotJ u y = β} := by
    refine convexHull_min (fun v hv ↦ ?_) (convex_hyperplane_dotJ u β)
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2
  have := hsub hx'
  rwa [mem_ofPred_eq, ← dirLoss_eq_dotJ_statPoint] at this

/-- **The restricted reference law is absolutely continuous with respect to `q_M`**: on the face
the projection is a bounded exponential tilt of the conditioned law. -/
theorem restrict_minimalFaceFibre_absolutelyContinuous {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ν.restrict (minimalFaceFibre V S M) ≪ responseProjection hS ν M := by
  obtain ⟨u, β, hV, hMβ, -, hp, hrel, hF⟩ := exists_exposing_polytope ν V hcharged hM
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  have hrel' : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) := by
    rwa [momentBody_faceMeasure_eq_of_exposed hS ν V u β hpoly hcharged hV hp]
  obtain ⟨θ, hθ⟩ := responseProjection_eq_tilted hS (faceMeasure ν {x | dirLoss S u x = β}) hrel'
  rw [responseProjection_eq_faceMeasure_of_exposed hS ν V hpoly hcharged hV hp hMβ hrel, hθ]
  have h1 : ν.restrict (minimalFaceFibre V S M) ≪ ν.restrict {x | dirLoss S u x = β} :=
    Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (minimalFaceFibre_subset_faceFibre (V := V) hF) le_rfl)
  have h2 : ν.restrict {x | dirLoss S u x = β} ≪ faceMeasure ν {x | dirLoss S u x = β} := by
    refine Measure.AbsolutelyContinuous.mk fun s _ h ↦ ?_
    rw [faceMeasure, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
    · exact h
  have h3 : faceMeasure ν {x | dirLoss S u x = β} ≪
      (faceMeasure ν {x | dirLoss S u x = β}).tilted fun x ↦ -1 * dirLoss S θ x :=
    absolutelyContinuous_tilted
      (integrable_exp_of_bdd (faceMeasure ν {x | dirLoss S u x = β})
        (Bdd.const_mul (-1) (bdd_dirLoss hS θ)))
  exact h1.trans (h2.trans h3)

/-- **The face order**: `q_M ≪ q_N` iff the minimal face of `M` lies in the minimal face of `N`. -/
theorem responseProjection_absolutelyContinuous_iff {M N : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hN : N ∈ convexHull ℝ (V : Set (J → ℝ))) :
    responseProjection hS ν M ≪ responseProjection hS ν N ↔
      minimalFacePoly V M ⊆ minimalFacePoly V N := by
  constructor
  · intro hac
    unfold minimalFacePoly
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro _ ⟨v, hv, rfl⟩
    by_contra hvN
    have h1 : responseProjection hS ν N (statFibre S (v : J → ℝ)) = 0 :=
      measure_mono_null (statFibre_subset_compl_minimalFaceFibre hvN)
        (responseProjection_compl_minimalFaceFibre_eq_zero hS ν V hpoly hcharged hN)
    have h2 := restrict_minimalFaceFibre_absolutelyContinuous hS ν V hpoly hcharged hM (hac h1)
    rw [Measure.restrict_apply (measurableSet_statFibre hS _),
      Set.inter_eq_left.2 (statFibre_subset_minimalFaceFibre (mem_minimalFacePoly_of_pos V hv))]
      at h2
    have := hcharged v v.2
    rw [measureReal_def, h2, ENNReal.toReal_zero] at this
    exact lt_irrefl _ this
  · intro hsub
    exact (responseProjection_absolutelyContinuous_restrict hS ν V hpoly hcharged hM).trans
      ((Measure.absolutelyContinuous_of_le
        (Measure.restrict_mono (minimalFaceFibre_mono hsub) le_rfl)).trans
        (restrict_minimalFaceFibre_absolutelyContinuous hS ν V hpoly hcharged hN))

/-- **The strata of the completed family are the faces**: two projections are mutually absolutely
continuous iff their minimal faces coincide. -/
theorem responseProjection_equivalent_iff {M N : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hN : N ∈ convexHull ℝ (V : Set (J → ℝ))) :
    (responseProjection hS ν M ≪ responseProjection hS ν N ∧
      responseProjection hS ν N ≪ responseProjection hS ν M) ↔
      minimalFacePoly V M = minimalFacePoly V N := by
  rw [responseProjection_absolutelyContinuous_iff hS ν V hpoly hcharged hM hN,
    responseProjection_absolutelyContinuous_iff hS ν V hpoly hcharged hN hM, subset_antisymm_iff]

/-- The face order in terms of charged vertices. -/
theorem responseProjection_absolutelyContinuous_iff_charged {M N : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hN : N ∈ convexHull ℝ (V : Set (J → ℝ))) :
    responseProjection hS ν M ≪ responseProjection hS ν N ↔
      ∀ v : V, 0 < vertexSection V M v → 0 < vertexSection V N v := by
  rw [responseProjection_absolutelyContinuous_iff hS ν V hpoly hcharged hM hN,
    minimalFacePoly_subset_iff hN]

end Order

end Laplace.Multi
