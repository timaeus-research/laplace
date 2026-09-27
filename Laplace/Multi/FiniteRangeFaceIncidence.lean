/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteRangeAllFacesAccessible

/-!
# Finite range: face incidence in the completion

For a finite-range charged polytope model, the face strata `X_F = {x | meanExt x ∈ ri F}` are
glued exactly as the faces are: for every exposed face `F` with a tight vertex,

  `closure X_F = meanExt⁻¹(F) = ⋃_{E ⊆ F} X_E`.

The upper inclusion is continuity of `meanExt` and closedness of `F`
(`closure_faceStratum_subset_preimage`). The middle equality is the minimal-face decomposition of
the polytope (`preimage_face_eq_iUnion_faceStratum`), using that an exposed face is an extreme set
(`isExtreme_face`). The lower inclusion is the substantive step
(`faceStratum_subset_closure_of_subset`): inside the *face model* `ν_F` (finitely supported on the
tight vertices, charged) the subface `E` is again an exposed face, so by
`FiniteRangeAllFacesAccessible` it carries a face-model completion point over any point of `ri E`;
the extended face embedding `ĵ_F` maps it to an ambient point with the same extended mean, which
by injectivity of `meanExt` is the given point of `X_E`, and `ĵ_F` maps the dense interior of the
face completion into `X_F`. Consequently `X_E ⊆ closure X_F ⇔ E ⊆ F`
(`faceStratum_subset_closure_iff`).
-/

open MeasureTheory Filter Topology Set

set_option quotPrecheck false

namespace Laplace.Multi

section Extreme

variable {J : Type*} [Fintype J]

/-- **An exposed face of a polytope is an extreme set.** -/
theorem isExtreme_face (V : Finset (J → ℝ)) {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) :
    IsExtreme ℝ (convexHull ℝ (V : Set (J → ℝ)))
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))) := by
  rw [← convexHull_inter_hyperplane V u β hV]
  have hle : ∀ y ∈ convexHull ℝ (V : Set (J → ℝ)), dotJ u y ≤ β := fun y hy ↦
    (convex_halfspace_dotJ u β).convexHull_subset_iff.2 (fun v hv ↦ hV v hv) hy
  refine ⟨inter_subset_left, fun x hx y hy z hz hseg ↦ ?_⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  refine ⟨hx, ?_⟩
  have hz' : dotJ u (a • x + b • y) = β := hz.2
  rw [(isLinearMap_dotJ u).map_add, (isLinearMap_dotJ u).map_smul,
    (isLinearMap_dotJ u).map_smul, smul_eq_mul, smul_eq_mul] at hz'
  have h1 := hle x hx
  have h2 := hle y hy
  change dotJ u x = β
  have hβ : a * β + b * β = β := by rw [← add_mul, hab, one_mul]
  refine le_antisymm h1 (le_of_not_gt fun hlt ↦ ?_)
  nlinarith [mul_lt_mul_of_pos_left hlt ha, mul_le_mul_of_nonneg_left h2 hb.le]

/-- **A point of the relative interior of an exposed face determines the face**: the minimal face
of the point is the exposed face. -/
theorem minimalFacePoly_eq_of_mem_ri_face [Nonempty J] (V : Finset (J → ℝ)) [Nonempty V]
    {u : J → ℝ} {β : ℝ}
    (hV : ∀ v ∈ V, dotJ u v ≤ β) {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))) :
    minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) := by
  have hMF := intrinsicInterior_subset hM
  have hMP : M ∈ convexHull ℝ (V : Set (J → ℝ)) :=
    (isExtreme_face V hV).subset hMF
  refine le_antisymm (minimalFacePoly_subset_of_isExtreme hMP (isExtreme_face V hV) hMF) ?_
  obtain ⟨e, γ, heV, hMγ, hG⟩ := exists_minimalFacePoly_eq_inter_hyperplane hMP
  rw [mem_intrinsicInterior_iff_forall_supporting (convex_convexHull ℝ _)] at hM
  have hsupp : ∀ y ∈ convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) :
      Set (J → ℝ)), dotJ e y ≤ dotJ e M := fun y hy ↦ by
    rw [hMγ]
    exact (convex_halfspace_dotJ e γ).convexHull_subset_iff.2 (fun v hv ↦ heV v hv)
      ((isExtreme_face V hV).subset hy)
  intro y hy
  rw [hG]
  refine ⟨(isExtreme_face V hV).subset hy, ?_⟩
  change dotJ e y = γ
  rw [hM.2 e hsupp y hy, hMγ]

end Extreme

section Incidence

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (hae : ∀ᵐ x ∂ν, statPoint S x ∈ V)
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
  {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V)
  (hz₀β : dotJ u z₀ = β)
include hS hae hcharged hV hz₀V hz₀β

/-- The tight vertices of the face. -/
local notation "Vt" => (V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ))

/-- The face of the polytope. -/
local notation "Fbody" => convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) :
  Set (J → ℝ))

/-- The face law. -/
local notation "νE" => faceMeasure ν {x | dirLoss S u x = β}

/-- **The face stratum is the preimage of the open face** under the extended mean map. -/
theorem faceStratum_eq_preimage_ri :
    faceStratum hS ν u β = meanExt hS ν ⁻¹' intrinsicInterior ℝ Fbody := by
  have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
  unfold faceStratum
  rw [momentBody_faceMeasure_eq hS ν V (momentBody_eq_convexHull_of_finiteRange hS ν V hae
    hcharged) hcharged hV hz₀V hz₀β]
  rfl

/-- **Upper inclusion**: the closure of a face stratum lies over the closed face. -/
theorem closure_faceStratum_subset_preimage :
    closure (faceStratum hS ν u β) ⊆ meanExt hS ν ⁻¹' Fbody := by
  rw [faceStratum_eq_preimage_ri hS ν V hae hcharged hV hz₀V hz₀β]
  refine closure_minimal (preimage_mono intrinsicInterior_subset) ?_
  exact ((V.filter fun v ↦ dotJ u v = β).finite_toSet.isClosed_convexHull (𝕜 := ℝ)).preimage
    (continuous_meanExt hS ν)

omit hz₀β in
/-- **The preimage of a closed face is the union of the strata of its subfaces.** -/
theorem preimage_face_eq_iUnion_faceStratum :
    meanExt hS ν ⁻¹' Fbody =
      ⋃ (u' : J → ℝ) (β' : ℝ) (_ : ∀ v ∈ V, dotJ u' v ≤ β') (_ : ∃ z ∈ V, dotJ u' z = β')
        (_ : convexHull ℝ ((V.filter fun v ↦ dotJ u' v = β' : Finset (J → ℝ)) : Set (J → ℝ)) ⊆
          Fbody), faceStratum hS ν u' β' := by
  have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
  have hpoly := momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged
  ext x
  simp only [mem_preimage, mem_iUnion]
  constructor
  · intro hx
    obtain ⟨u', β', z', hz'V, hz'β, hx₀, hV', hF, -⟩ :=
      exists_faceChart_range_eq hS ν V hpoly hcharged x
    have hxP : meanExt hS ν x ∈ convexHull ℝ (V : Set (J → ℝ)) :=
      meanExt_mem_polytope hS ν V hpoly x
    refine ⟨u', β', hV', ⟨z', hz'V, hz'β⟩, ?_, hx₀⟩
    rw [← hF]
    exact minimalFacePoly_subset_of_isExtreme hxP (isExtreme_face V hV) hx
  · rintro ⟨u', β', hV', ⟨z', hz'V, hz'β⟩, hsub, hx⟩
    have hx' : x ∈ faceStratum hS ν u' β' := hx
    rw [faceStratum_eq_preimage_ri hS ν V hae hcharged hV' hz'V hz'β] at hx'
    exact hsub (intrinsicInterior_subset hx')

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hae hcharged hz₀V hz₀β in
/-- The tight vertices of a subface are tight for the face. -/
theorem tight_subface {u' : J → ℝ} {β' : ℝ}
    (hsub : convexHull ℝ ((V.filter fun v ↦ dotJ u' v = β' : Finset (J → ℝ)) : Set (J → ℝ)) ⊆
      Fbody) {z : J → ℝ} (hzV : z ∈ V) (hzβ' : dotJ u' z = β') : dotJ u z = β := by
  have hz : z ∈ Fbody := hsub (subset_convexHull ℝ _ (Finset.mem_filter.2 ⟨hzV, hzβ'⟩))
  rw [← convexHull_inter_hyperplane V u β hV] at hz
  exact hz.2

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hae hcharged hz₀V hz₀β in
/-- The tight vertices of a subface, seen in the face model, are the tight vertices of the
subface. -/
theorem filter_tight_subface {u' : J → ℝ} {β' : ℝ}
    (hsub : convexHull ℝ ((V.filter fun v ↦ dotJ u' v = β' : Finset (J → ℝ)) : Set (J → ℝ)) ⊆
      Fbody) :
    ((V.filter fun v ↦ dotJ u v = β).filter fun v ↦ dotJ u' v = β') =
      V.filter fun v ↦ dotJ u' v = β' := by
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hvV, -⟩, hv⟩
    exact ⟨hvV, hv⟩
  · rintro ⟨hvV, hv⟩
    exact ⟨⟨hvV, tight_subface V hV hsub hvV hv⟩, hv⟩

/-- **Lower inclusion**: the stratum of a subface lies in the closure of the face stratum. -/
theorem faceStratum_subset_closure_of_subset {u' : J → ℝ} {β' : ℝ} (hV' : ∀ v ∈ V, dotJ u' v ≤ β')
    {z' : J → ℝ} (hz'V : z' ∈ V) (hz'β : dotJ u' z' = β')
    (hsub : convexHull ℝ ((V.filter fun v ↦ dotJ u' v = β' : Finset (J → ℝ)) : Set (J → ℝ)) ⊆
      Fbody) :
    faceStratum hS ν u' β' ⊆ closure (faceStratum hS ν u β) := by
  have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
  have hpoly := momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged
  have hpE : 0 < ν.real {x | dirLoss S u x = β} := faceFibre_pos_of_charged ν V hcharged hz₀V hz₀β
  have : IsProbabilityMeasure νE := isProbabilityMeasure_faceMeasure_of_real_pos ν hpE
  -- the face model is a finite-range charged polytope model on the tight vertices
  have haeE : ∀ᵐ x ∂νE, statPoint S x ∈ Vt := ae_statPoint_mem_tight_faceMeasure hS ν V hae
  have hchargedE : ∀ v ∈ Vt, 0 < (νE).real (statFibre S v) :=
    faceMeasure_charged hS ν V hcharged hz₀V hz₀β
  have hVE : ∀ v ∈ Vt, dotJ u' v ≤ β' := fun v hv ↦ hV' v (Finset.mem_filter.1 hv).1
  have hz'E : z' ∈ Vt := Finset.mem_filter.2 ⟨hz'V,
    tight_subface V hV hsub hz'V hz'β⟩
  -- a seed of the face stratum and the face embedding
  obtain ⟨x₀, hx₀⟩ := face_accessible_of_finiteRange hS ν V hae hcharged hV hz₀V hz₀β
  have hx₀' : meanExt hS ν x₀ ∈ intrinsicInterior ℝ (momentBody νE (fun _ ↦ (1 : ℝ)) S) := hx₀
  have hle := faceDirSpan_le hS ν V hcharged hz₀V hz₀β
  have hlaw := completionLaw_eq_faceFamily_faceThetaOf hS ν V hpoly hcharged hV hz₀V hz₀β hx₀' rfl
  intro x hx
  -- the point of the face completion over the same mean
  have hxE : meanExt hS ν x ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure νE {y | dirLoss S u' y = β'}) (fun _ ↦ (1 : ℝ)) S) := by
    have hpolyE : momentBody νE (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (Vt : Set (J → ℝ)) :=
      momentBody_faceMeasure_eq hS ν V hpoly hcharged hV hz₀V hz₀β
    have : Nonempty Vt := ⟨⟨z', hz'E⟩⟩
    rw [momentBody_faceMeasure_eq hS νE Vt hpolyE hchargedE hVE hz'E hz'β,
      filter_tight_subface V hV hsub]
    have hx' : x ∈ faceStratum hS ν u' β' := hx
    rwa [faceStratum_eq_preimage_ri hS ν V hae hcharged hV' hz'V hz'β] at hx'
  obtain ⟨y, hy⟩ := exists_meanExt_eq_of_mem_ri_face_finiteRange hS νE Vt haeE hchargedE hVE hz'E
    hz'β hxE
  -- its image is `x`, and it lies in the closure of the embedded interior
  have hjy : faceEmbedExt hS ν νE hle x₀ (faceThetaOf hS ν _ hx₀') y = x := by
    apply meanExt_injective hS ν V hpoly hcharged
    rw [meanExt_faceEmbedExt hS ν νE hle hlaw y, hy]
  rw [← hjy]
  have hdense : y ∈ closure (Set.range ((↑) : FisherPoint hS νE → FisherCompletion hS νE)) :=
    UniformSpace.Completion.denseRange_coe y
  have hcont := continuous_faceEmbedExt hS ν νE hle hlaw
  have hmem : faceEmbedExt hS ν νE hle x₀ (faceThetaOf hS ν _ hx₀') y ∈
      closure (faceEmbedExt hS ν νE hle x₀ (faceThetaOf hS ν _ hx₀') ''
        Set.range ((↑) : FisherPoint hS νE → FisherCompletion hS νE)) :=
    image_closure_subset_closure_image hcont ⟨y, hdense, rfl⟩
  refine closure_mono (Set.image_subset_iff.2 (Set.range_subset_iff.2 fun p ↦ ?_)) hmem
  rw [Set.mem_preimage, faceEmbedExt_coe hS ν νE hle hlaw p]
  change meanExt hS ν (faceEmbed hS ν νE hle x₀ (faceThetaOf hS ν _ hx₀') p.param) ∈
    intrinsicInterior ℝ (momentBody νE (fun _ ↦ (1 : ℝ)) S)
  rw [meanExt_faceEmbed hS ν νE hle hlaw p.param]
  exact meanMap_faceMeasure_mem_intrinsicInterior hS ν (u := u) (β := β) (p.param : J → ℝ)

/-- **The closure of a face stratum is the preimage of the closed face.** -/
theorem closure_faceStratum_eq_preimage :
    closure (faceStratum hS ν u β) = meanExt hS ν ⁻¹' Fbody := by
  refine Subset.antisymm (closure_faceStratum_subset_preimage hS ν V hae hcharged hV hz₀V hz₀β) ?_
  rw [preimage_face_eq_iUnion_faceStratum hS ν V hae hcharged hV hz₀V]
  refine iUnion_subset fun u' ↦ iUnion_subset fun β' ↦ iUnion_subset fun hV' ↦
    iUnion_subset fun ⟨z', hz'V, hz'β⟩ ↦ iUnion_subset fun hsub ↦ ?_
  exact faceStratum_subset_closure_of_subset hS ν V hae hcharged hV hz₀V hz₀β hV' hz'V hz'β hsub

/-- **Face incidence**: the closure of a face stratum is the union of the strata of its
subfaces. -/
theorem closure_faceStratum_eq_iUnion :
    closure (faceStratum hS ν u β) =
      ⋃ (u' : J → ℝ) (β' : ℝ) (_ : ∀ v ∈ V, dotJ u' v ≤ β') (_ : ∃ z ∈ V, dotJ u' z = β')
        (_ : convexHull ℝ ((V.filter fun v ↦ dotJ u' v = β' : Finset (J → ℝ)) : Set (J → ℝ)) ⊆
          Fbody), faceStratum hS ν u' β' := by
  rw [closure_faceStratum_eq_preimage hS ν V hae hcharged hV hz₀V hz₀β,
    preimage_face_eq_iUnion_faceStratum hS ν V hae hcharged hV hz₀V]

/-- **The incidence order**: a stratum lies in the closure of another iff its face lies in the
other's face. -/
theorem faceStratum_subset_closure_iff {u' : J → ℝ} {β' : ℝ} (hV' : ∀ v ∈ V, dotJ u' v ≤ β')
    {z' : J → ℝ} (hz'V : z' ∈ V) (hz'β : dotJ u' z' = β') :
    faceStratum hS ν u' β' ⊆ closure (faceStratum hS ν u β) ↔
      convexHull ℝ ((V.filter fun v ↦ dotJ u' v = β' : Finset (J → ℝ)) : Set (J → ℝ)) ⊆ Fbody := by
  refine ⟨fun h ↦ ?_, faceStratum_subset_closure_of_subset hS ν V hae hcharged hV hz₀V hz₀β hV'
    hz'V hz'β⟩
  have : Nonempty V := ⟨⟨z₀, hz₀V⟩⟩
  have hpoly := momentBody_eq_convexHull_of_finiteRange hS ν V hae hcharged
  obtain ⟨x, hx⟩ := face_accessible_of_finiteRange hS ν V hae hcharged hV' hz'V hz'β
  have hxF : meanExt hS ν x ∈ Fbody :=
    closure_faceStratum_subset_preimage hS ν V hae hcharged hV hz₀V hz₀β (h hx)
  have hx' : x ∈ faceStratum hS ν u' β' := hx
  rw [faceStratum_eq_preimage_ri hS ν V hae hcharged hV' hz'V hz'β] at hx'
  have hxP : meanExt hS ν x ∈ convexHull ℝ (V : Set (J → ℝ)) :=
    meanExt_mem_polytope hS ν V hpoly x
  rw [← minimalFacePoly_eq_of_mem_ri_face V hV' hx']
  exact minimalFacePoly_subset_of_isExtreme hxP (isExtreme_face V hV) hxF

end Incidence

end Laplace.Multi
