/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFaceRestriction
import Laplace.Multi.RelativeInterior

/-!
# The support of the response is constant on the relative interior of a face

The entropy response `R_M` charges exactly the atoms whose feature vectors lie on the minimal face
of the polytope containing `M` (Csiszár's support theorem, `FiniteMinimalFace`). Along the polytope
the support can only shrink towards the boundary: the support of every point of the face of `M`
is contained in the support of `M` (`supportSet_subset_of_mem_carriedResponses`), while the
supports of the endpoints of a segment through `M` are contained in the support of `M`
(`supportSet_subset_of_mem_openSegment`). Since every point of the relative interior of a face is
the midpoint-like interior point of a segment through any other point of the face
(`exists_mem_openSegment_of_mem_intrinsicInterior`), the support is **constant on the relative
interior of each face** (`supportSet_eq_of_mem_intrinsicInterior`). Combined with the exact face
restriction of `ResponseFaceRestriction`, the entropy response is, on the whole relative interior of
the face of `M`, the entropy response of the fixed conditioned law `ν_A`, `A = supp q*(M)`
(`responseProjection_eq_faceMeasure_of_mem_intrinsicInterior`): each open face stratum is one
interior problem for one base law, which is what lets the interior response calculus run facewise.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Segment

variable {J : Type*} [Fintype J]

set_option linter.unusedFintypeInType false in
/-- A relative-interior point of a set lies on an open segment from any point of the set to
another point of the set. -/
theorem exists_mem_openSegment_of_mem_intrinsicInterior {K : Set (J → ℝ)} {x y : J → ℝ}
    (hx : x ∈ intrinsicInterior ℝ K) (hy : y ∈ K) : ∃ z ∈ K, x ∈ openSegment ℝ y z := by
  obtain ⟨hxK, δ, hδ, hball⟩ := mem_intrinsicInterior_iff_exists_ball.1 hx
  set t : ℝ := δ / (2 * (‖x - y‖ + 1)) with ht
  have ht0 : 0 < t := by positivity
  have hv : t • (x - y) ∈ (affineSpan ℝ K).direction := by
    refine Submodule.smul_mem _ _ ?_
    have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hxK) (mem_affineSpan ℝ hy)
    simpa using this
  have hnorm : ‖t • (x - y)‖ < δ := by
    rw [norm_smul, Real.norm_of_nonneg ht0.le, ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (x - y)]
  refine ⟨x + t • (x - y), hball _ hv hnorm, t / (1 + t), 1 / (1 + t), by positivity,
    by positivity, ?_, ?_⟩
  · field_simp
    ring
  · rw [smul_add, smul_smul, smul_sub]
    match_scalars <;> (field_simp; try ring)

end Segment

section Constancy

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Fintype J] [Nonempty J] hS hν
  [IsProbabilityMeasure ν] in
variable (S) in
/-- The face polytope of a set of atoms is convex. -/
theorem convex_carriedResponses (A : Set X) : Convex ℝ (carriedResponses S A) := by
  rintro _ ⟨b, hb, hbs, rfl⟩ _ ⟨b', hb', hbs', rfl⟩ a c ha hc hac
  refine ⟨a • b + c • b', convex_stdSimplex ℝ X hb hb' ha hc hac, fun x hx ↦ ?_, ?_⟩
  · simp [hbs x hx, hbs' x hx]
  · rw [vecMoment_add, vecMoment_smul, vecMoment_smul]

/-- **Supports grow inward**: the support of an endpoint of a segment through `M` is contained in
the support of `M`. -/
theorem supportSet_subset_of_mem_openSegment {M M' z : J → ℝ} (hM' : M' ∈ hull) (hz : z ∈ hull)
    (hseg : M ∈ openSegment ℝ M' z) : supportSet hS ν M' ⊆ supportSet hS ν M := by
  obtain ⟨a, c, ha, hc, hac, hM⟩ := hseg
  have hMh : M ∈ hull := hM ▸ (convex_convexHull ℝ _) hM' hz ha.le hc.le hac
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hMh
  have hq := qStarVec_mem_stdSimplex hS ν hfin
  have hq' := qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM'
  have hqz := qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hz
  intro x hx
  have hw : a • qStarVec hS ν M' + c • qStarVec hS ν z ∈ stdSimplex ℝ X :=
    convex_stdSimplex ℝ X hq' hqz ha.le hc.le hac
  have hwb : vecMoment S (a • qStarVec hS ν M' + c • qStarVec hS ν z) =
      vecMoment S (qStarVec hS ν M) := by
    rw [vecMoment_add, vecMoment_smul, vecMoment_smul,
      vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM'),
      vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hz),
      vecMoment_qStarVec hS ν hfin, hM]
  have hwx : 0 < (a • qStarVec hS ν M' + c • qStarVec hS ν z) x := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : 0 < qStarVec hS ν M' x := hx
    have h2 := hqz.1 x
    nlinarith
  exact support_absorb hS ν hν hMh hq (fun y hy ↦ qStarVec_eq_zero_of_notMem hS ν hν hMh hy)
    hw hwb hwx

/-- **Supports shrink outward**: every point of the face of `M` has support inside the support of
`M`. -/
theorem supportSet_subset_of_mem_carriedResponses {M M' : J → ℝ} (hM : M ∈ hull)
    (hM' : M' ∈ carriedResponses S (supportSet hS ν M)) :
    supportSet hS ν M' ⊆ supportSet hS ν M := by
  have hM'h : M' ∈ hull := carriedResponses_subset_hull (S := S) _ hM'
  have hsub := carriedResponses_supportSet_subset_of_isExtreme hS ν hν hM'h
    (isExtreme_carriedResponses_supportSet hS ν hν hM) hM'
  intro x hx
  have h1 : statPoint S x ∈ carriedResponses S (supportSet hS ν M') := by
    rw [← minimalFace_eq hS ν hν hM'h]
    exact (qStarVec_pos_iff_mem_minimalFace hS ν hν hM'h x).1 hx
  have h2 := hsub h1
  rw [← minimalFace_eq hS ν hν hM] at h2
  exact (qStarVec_pos_iff_mem_minimalFace hS ν hν hM x).2 h2

/-- **THE SUPPORT IS CONSTANT ON THE RELATIVE INTERIOR OF A FACE**: every point of the relative
interior of the face of `M` has the same support as `M`. -/
theorem supportSet_eq_of_mem_intrinsicInterior {M M' : J → ℝ} (hM : M ∈ hull)
    (hM' : M' ∈ intrinsicInterior ℝ (carriedResponses S (supportSet hS ν M))) :
    supportSet hS ν M' = supportSet hS ν M := by
  refine subset_antisymm
    (supportSet_subset_of_mem_carriedResponses hS ν hν hM (intrinsicInterior_subset hM')) ?_
  obtain ⟨z, hz, hseg⟩ := exists_mem_openSegment_of_mem_intrinsicInterior hM'
    (mem_carriedResponses_supportSet hS ν hν hM)
  exact supportSet_subset_of_mem_openSegment hS ν hν hM (carriedResponses_subset_hull (S := S) _ hz)
    hseg

/-- **One base law per open face stratum**: on the relative interior of the face of `M` the entropy
response is the entropy response relative to the fixed conditioned law `ν_A`, `A = supp q*(M)`. -/
theorem responseProjection_eq_faceMeasure_of_mem_intrinsicInterior {M M' : J → ℝ} (hM : M ∈ hull)
    (hM' : M' ∈ intrinsicInterior ℝ (carriedResponses S (supportSet hS ν M))) :
    responseProjection hS (faceMeasure ν (supportSet hS ν M)) M' = responseProjection hS ν M' := by
  rw [← supportSet_eq_of_mem_intrinsicInterior hS ν hν hM hM']
  exact responseProjection_faceMeasure_supportSet hS ν hν
    (carriedResponses_subset_hull (S := S) _ (intrinsicInterior_subset hM'))

end Constancy

end Laplace.Multi
