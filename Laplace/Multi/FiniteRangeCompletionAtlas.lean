/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteRangeFaceIncidence

/-!
# Finite range: the completed response atlas

For a statistic of finite essential range with every value charged, the earlier accessible-face
results become unconditional and assemble into a complete description of the Fisher completion
`Ŵ` of the response atlas:

* `iUnion_faceStratum_of_finiteRange`: `Ŵ = ⋃_F X_F` over ALL exposed faces `F` with a tight vertex
  (no accessibility hypothesis remains);
* `faceStratum_eq_iff_of_finiteRange` / `faceStratum_eq_or_disjoint_of_finiteRange`: two strata
  are equal when their faces are and disjoint otherwise (every stratum is nonempty);
* `exists_faceStratum_eq_range_of_finiteRange`: every stratum is the image of a canonical finite
  chart `j_F : W_F → Ŵ`;
* `range_completionLaw_eq_of_finiteRange`: the completion laws are exactly the face-family laws
  of all faces, and `completionLaw` is injective, so `Ŵ` is in bijection with the union of the
  open face families;
* `bijOn_meanExt_of_finiteRange`: the extended mean map is a bijection of `Ŵ` onto the moment
  polytope `conv V`.

Together with `FiniteRangeFaceIncidence` (`closure X_F = ⋃_{E ⊆ F} X_E`) this is the finite-range
completed atlas: a stratification of `Ŵ` by the face lattice of the moment polytope, each stratum
a canonical copy of its face family. No claim is made that `meanExt` is a homeomorphism.
-/

open MeasureTheory Filter Topology Set

set_option quotPrecheck false

namespace Laplace.Multi

section Atlas

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (hae : ∀ᵐ x ∂ν, statPoint S x ∈ V)
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hae hcharged

/-- **The completion is the union of the strata of all exposed faces with a tight vertex.** -/
theorem iUnion_faceStratum_of_finiteRange :
    ⋃ (u : J → ℝ) (β : ℝ) (_ : ∀ v ∈ V, dotJ u v ≤ β) (_ : ∃ z₀ ∈ V, dotJ u z₀ = β),
      faceStratum hS ν u β = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  have : Nonempty V := by
    have hx := meanExt_mem_polytope' hS ν V hae hcharged x
    obtain ⟨z, hz⟩ := convexHull_nonempty_iff.1 ⟨_, hx⟩
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨u, β, z₀, hz₀V, hz₀β, hx₀, hV, -, -⟩ := exists_faceChart_range_eq hS ν V
    (momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged) hcharged x
  simp only [mem_iUnion]
  exact ⟨u, β, hV, ⟨z₀, hz₀V, hz₀β⟩, hx₀⟩

/-- Two face strata are equal exactly when the faces are. -/
theorem faceStratum_eq_iff_of_finiteRange {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {z₀ : J → ℝ} (hz₀V : z₀ ∈ V) (hz₀β : dotJ u z₀ = β) {u' : J → ℝ} {β' : ℝ}
    (hV' : ∀ v ∈ V, dotJ u' v ≤ β') {z' : J → ℝ} (hz'V : z' ∈ V) (hz'β : dotJ u' z' = β') :
    faceStratum hS ν u β = faceStratum hS ν u' β' ↔
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) =
        convexHull ℝ ((V.filter fun v ↦ dotJ u' v = β' : Finset (J → ℝ)) : Set (J → ℝ)) := by
  have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
  rw [faceStratum_eq_preimage_ri hS ν V hae hcharged hV hz₀V hz₀β,
    faceStratum_eq_preimage_ri hS ν V hae hcharged hV' hz'V hz'β]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := face_accessible_of_finiteRange hS ν V hae hcharged hV hz₀V hz₀β
    have hx' : x ∈ meanExt hS ν ⁻¹' intrinsicInterior ℝ
        (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))) := by
      rwa [faceStratum_eq_preimage_ri hS ν V hae hcharged hV hz₀V hz₀β] at hx
    have hx'' := hx'
    rw [h] at hx''
    rw [← minimalFacePoly_eq_of_mem_ri_face V hV hx',
      ← minimalFacePoly_eq_of_mem_ri_face V hV' hx'']
  · intro h
    rw [h]

/-- **Distinct faces have disjoint strata**; the strata of all faces partition the completion. -/
theorem faceStratum_eq_or_disjoint_of_finiteRange {u : J → ℝ} {β : ℝ}
    (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V) (hz₀β : dotJ u z₀ = β)
    {u' : J → ℝ} {β' : ℝ} (hV' : ∀ v ∈ V, dotJ u' v ≤ β') {z' : J → ℝ} (hz'V : z' ∈ V)
    (hz'β : dotJ u' z' = β') :
    faceStratum hS ν u β = faceStratum hS ν u' β' ∨
      Disjoint (faceStratum hS ν u β) (faceStratum hS ν u' β') := by
  by_cases h : faceStratum hS ν u β = faceStratum hS ν u' β'
  · exact Or.inl h
  right
  rw [Set.disjoint_left]
  intro x hx hx'
  apply h
  have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
  rw [faceStratum_eq_iff_of_finiteRange hS ν V hae hcharged hV hz₀V hz₀β hV' hz'V hz'β]
  rw [faceStratum_eq_preimage_ri hS ν V hae hcharged hV hz₀V hz₀β] at hx
  rw [faceStratum_eq_preimage_ri hS ν V hae hcharged hV' hz'V hz'β] at hx'
  rw [← minimalFacePoly_eq_of_mem_ri_face V hV hx, ← minimalFacePoly_eq_of_mem_ri_face V hV' hx']

/-- **Every stratum is the image of a canonical finite chart** `j_F : W_F → Ŵ`. -/
theorem exists_faceStratum_eq_range_of_finiteRange {u : J → ℝ} {β : ℝ}
    (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V) (hz₀β : dotJ u z₀ = β) :
    ∃ (x₀ : FisherCompletion hS ν) (hx₀ : x₀ ∈ faceStratum hS ν u β),
      faceStratum hS ν u β = Set.range (faceChart hS ν V hcharged hz₀V hz₀β hx₀) := by
  have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
  obtain ⟨x₀, hx₀⟩ := face_accessible_of_finiteRange hS ν V hae hcharged hV hz₀V hz₀β
  exact ⟨x₀, hx₀, faceStratum_eq_range hS ν V
    (momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged) hcharged hV hz₀V hz₀β hx₀⟩

/-- **The completion laws are exactly the face-family laws of all exposed faces.** -/
theorem range_completionLaw_eq_of_finiteRange :
    Set.range (completionLaw hS ν) =
      ⋃ (u : J → ℝ) (β : ℝ) (_ : ∀ v ∈ V, dotJ u v ≤ β) (_ : ∃ z₀ ∈ V, dotJ u z₀ = β),
        Set.range (fun w : dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S ↦
          familyMeasure (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
            (fun _ ↦ (0 : ℝ)) S 1 (w : J → ℝ)) := by
  have hpoly := momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged
  ext Q
  simp only [mem_range, mem_iUnion]
  constructor
  · rintro ⟨x, rfl⟩
    have hxU : x ∈ (univ : Set (FisherCompletion hS ν)) := mem_univ x
    rw [← iUnion_faceStratum_of_finiteRange hS ν V hae hcharged] at hxU
    simp only [mem_iUnion] at hxU
    obtain ⟨u, β, hV, ⟨z₀, hz₀V, hz₀β⟩, hx⟩ := hxU
    have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
    have : IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β}) :=
      isProbabilityMeasure_faceMeasure_of_real_pos ν
        (faceFibre_pos_of_charged ν V hcharged hz₀V hz₀β)
    have hx' : meanExt hS ν x ∈ intrinsicInterior ℝ
        (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) := hx
    exact ⟨u, β, hV, ⟨z₀, hz₀V, hz₀β⟩, faceThetaOf hS ν _ hx',
      (completionLaw_eq_faceFamily_faceThetaOf hS ν V hpoly hcharged hV hz₀V hz₀β hx' rfl).symm⟩
  · rintro ⟨u, β, hV, ⟨z₀, hz₀V, hz₀β⟩, w, rfl⟩
    have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
    obtain ⟨x₀, hx₀, -⟩ :=
      exists_faceStratum_eq_range_of_finiteRange hS ν V hae hcharged hV hz₀V hz₀β
    exact ⟨faceChart hS ν V hcharged hz₀V hz₀β hx₀ w,
      completionLaw_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀ w⟩

/-- **The completion law is injective** (finite range): `Ŵ` is in bijection with the union of the
open face families. -/
theorem completionLaw_injective_of_finiteRange : Function.Injective (completionLaw hS ν) := by
  by_cases hV : Nonempty V
  · exact completionLaw_injective hS ν V
      (momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged) hcharged
  · exact absurd (nonempty_of_finiteRange ν V hae) hV

/-- **The extended mean map is a bijection of the completion onto the moment polytope**
(finite range). -/
theorem bijOn_meanExt_of_finiteRange :
    Set.BijOn (meanExt hS ν) univ (convexHull ℝ (V : Set (J → ℝ))) := by
  refine ⟨fun x _ ↦ meanExt_mem_polytope' hS ν V hae hcharged x, fun x _ y _ hxy ↦ ?_, ?_⟩
  · have : Nonempty V := nonempty_of_finiteRange ν V hae
    exact meanExt_injective hS ν V (momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged)
      hcharged hxy
  · intro M hM
    obtain ⟨x, hx⟩ := meanExt_surjective_of_finiteRange hS ν V hae hcharged hM
    exact ⟨x, mem_univ x, hx⟩

end Atlas

end Laplace.Multi
