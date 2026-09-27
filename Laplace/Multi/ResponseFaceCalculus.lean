/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFaceSupportConstancy
import Laplace.Multi.FiniteCompletionClosure
import Laplace.Multi.ResponseObservableSamplingGeometry

/-!
# The facewise interior calculus of the response map

The conditioned law `ν_A` of a set of atoms `A` sees exactly the feature vectors of `A`
(`essRange_faceMeasure_eq_image`), so its moment body is the face polytope `conv S(A)`, which is the
set of responses carried by `A` (`carriedResponses_eq_convexHull_image`,
`momentBody_faceMeasure_eq_carriedResponses`); in particular the direction space of `ν_A` is the
direction space `W_A = span (S(A) − S(A))` of the face (`dirSpan_faceMeasure_eq_vectorSpan_image`).
Hence the relative interior of the face of `M` is the interior response domain `Ω^{ν_A}` of the base
law `ν_A`, `A = supp q*(M)`, on which the whole interior response calculus is available; combined
with the constancy of the support on the relative interior of the face
(`ResponseFaceSupportConstancy`), this gives the **facewise derivative of the response map**
(`hasDerivAt_responseObs_face`): for `M'` in the relative interior of the face of `M` and a face
direction `e ∈ W_A`,
`d/dt E_{R_{M' + t e}} F |_{t=0} = ⟨u_F^{A}(M'), e⟩`,
where `u_F^{A}(M')` is the regression direction of `F` relative to the conditioned law `ν_A` at the
chart point of `M'`. Every open face stratum of the polytope therefore carries its own smooth
response calculus, with the face law as base law and the face directions as tangent directions.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section FaceBody

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

omit [Nonempty X] [Fintype J] [Nonempty J] hS hν [IsProbabilityMeasure ν] in
open Classical in
/-- The atoms of the conditioned law. -/
theorem faceMeasure_singleton (A : Set X) (x : X) :
    faceMeasure ν A {x} = if x ∈ A then (ν A)⁻¹ * ν {x} else 0 := by
  rw [faceMeasure_apply ν (A.toFinite.measurableSet)]
  split_ifs with hx
  · rw [inter_eq_left.2 (singleton_subset_iff.2 hx)]
  · rw [singleton_inter_eq_empty.2 hx, measure_empty, mul_zero]

omit [Nonempty X] [Nonempty J] hS hν [IsProbabilityMeasure ν] in
/-- The conditioned law charges nothing outside its set. -/
theorem faceMeasure_compl_self (A : Set X) : faceMeasure ν A Aᶜ = 0 := by
  rw [faceMeasure_apply ν (A.toFinite.measurableSet), compl_inter_self, measure_empty, mul_zero]

omit [Nonempty X] [Nonempty J] in
/-- **The essential range of a conditioned law is the feature set of its atoms.** -/
theorem essRange_faceMeasure_eq_image (A : Set X) :
    essRange (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S = statPoint S '' A := by
  ext y
  rw [mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS]
  constructor
  · intro h
    by_contra hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
      ((A.toFinite.image (statPoint S)).isClosed.isOpen_compl) y hy
    have h0 : faceMeasure ν A (statPoint S ⁻¹' Metric.ball y ε) = 0 := by
      refine measure_mono_null (fun x hx hxA ↦ hball hx ⟨x, hxA, rfl⟩) (faceMeasure_compl_self ν A)
    have := h ε hε
    rw [h0] at this
    exact lt_irrefl _ this
  · rintro ⟨x, hxA, rfl⟩ r hr
    refine lt_of_lt_of_le ?_ (measure_mono (singleton_subset_iff.2 (Metric.mem_ball_self hr)))
    rw [faceMeasure_singleton ν A x, if_pos hxA]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (measure_ne_top ν A)) (hν x).ne'

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Fintype J] [Nonempty J] hS hν
  [IsProbabilityMeasure ν] in
variable (S) in
/-- **The responses carried by a set of atoms form the face polytope** `conv S(A)`. -/
theorem carriedResponses_eq_convexHull_image (A : Set X) :
    carriedResponses S A = convexHull ℝ (statPoint S '' A) := by
  classical
  refine subset_antisymm ?_ (convexHull_min ?_ (convex_carriedResponses S A))
  · rintro _ ⟨b, hb, hbs, rfl⟩
    rw [vecMoment_eq_sum_smul]
    have hfilt : ∀ f : X → J → ℝ, ∑ x ∈ Finset.univ.filter (· ∈ A), b x • f x =
        ∑ x, b x • f x := fun f ↦
      Finset.sum_filter_of_ne fun x _ hx ↦ by_contra fun hxA ↦ hx (by rw [hbs x hxA, zero_smul])
    rw [← hfilt]
    refine (convex_convexHull ℝ _).sum_mem (fun x _ ↦ hb.1 x) ?_
      (fun x hx ↦ subset_convexHull ℝ _ ⟨x, (Finset.mem_filter.1 hx).2, rfl⟩)
    rw [Finset.sum_filter_of_ne fun x _ hx ↦ by_contra fun hxA ↦ hx (hbs x hxA)]
    exact hb.2
  · rintro _ ⟨x, hxA, rfl⟩
    refine ⟨Pi.single x 1, ⟨fun y ↦ ?_, by simp⟩, fun y hy ↦ ?_, ?_⟩
    · by_cases hyx : y = x
      · subst hyx; simp
      · simp [hyx]
    · exact Pi.single_eq_of_ne (fun h : y = x ↦ hy (h ▸ hxA)) 1
    · rw [vecMoment_eq_sum_smul, Finset.sum_eq_single x (fun y _ hy ↦ by simp [hy]) (by simp)]
      simp

omit [Nonempty X] [Nonempty J] in
/-- **The moment body of a conditioned law is the face polytope of its atoms.** -/
theorem momentBody_faceMeasure_eq_carriedResponses (A : Set X) :
    momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S = carriedResponses S A := by
  unfold momentBody
  rw [essRange_faceMeasure_eq_image hS ν hν A, carriedResponses_eq_convexHull_image]
  exact ((A.toFinite.image (statPoint S)).isCompact_convexHull (𝕜 := ℝ)).isClosed.closure_eq

omit [Nonempty X] [Nonempty J] in
/-- **The direction space of a conditioned law is the direction space of its face**,
`W_A = span (S(A) − S(A))`. -/
theorem dirSpan_faceMeasure_eq_vectorSpan_image (A : Set X) :
    dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S = vectorSpan ℝ (statPoint S '' A) := by
  unfold dirSpan
  rw [momentBody_faceMeasure_eq_carriedResponses hS ν hν A, carriedResponses_eq_convexHull_image,
    affineSpan_convexHull, direction_affineSpan]

omit [Nonempty X] [Nonempty J] in
/-- **The relative interior of a face is the interior response domain of its conditioned law.** -/
theorem intrinsicInterior_momentBody_faceMeasure (A : Set X) :
    intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) =
      intrinsicInterior ℝ (carriedResponses S A) := by
  rw [momentBody_faceMeasure_eq_carriedResponses hS ν hν A]

/-- The support of a polytope point carries positive mass. -/
theorem measure_supportSet_ne_zero {M : J → ℝ} (hM : M ∈ hull) : ν (supportSet hS ν M) ≠ 0 :=
  (ENNReal.toReal_pos_iff.1 (measureReal_supportSet_pos hS ν hν hM)).1.ne'

end FaceBody

section FaceDerivative

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- **THE FACEWISE DERIVATIVE OF THE RESPONSE MAP**: for `M'` in the relative interior of the
face of `M`, `A = supp q*(M)`, and a face direction `e ∈ W_A`, the posterior expectation of `F` is
differentiable along `M' + t e` at `t = 0` with derivative `⟨u_F^{A}(M'), e⟩`, the pairing of the
displacement with the regression direction of `F` relative to the conditioned law `ν_A` at the
chart point of `M'`. -/
theorem hasDerivAt_responseObs_face {A : Set X} [IsProbabilityMeasure (faceMeasure ν A)]
    {M M' : J → ℝ} (hM : M ∈ hull) (hA : A = supportSet hS ν M)
    (hM' : M' ∈ intrinsicInterior ℝ (carriedResponses S A)) {F : X → ℝ} (hF : Bdd F)
    (e : dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, F x ∂responseProjection hS ν (M' + t • (e : J → ℝ)))
      (dotJ (regressionDir hS (faceMeasure ν A) F
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos (faceMeasure ν A)) hS M') : J → ℝ) (e : J → ℝ)) 0 := by
  have hrel : M' ∈ intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) := by
    rwa [intrinsicInterior_momentBody_faceMeasure hS ν hν A]
  set θ₀ := responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos (faceMeasure ν A)) hS M' with hθ₀
  have hmean : meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (θ₀ : J → ℝ) = M' :=
    meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos (faceMeasure ν A)) hS hrel
  refine (hasDerivAt_lineObservable_zero hS (faceMeasure ν A) hF θ₀ e).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_responseLineDomain hS (faceMeasure ν A) θ₀ e).mem_nhds
    (zero_mem_responseLineDomain hS (faceMeasure ν A) θ₀ e)] with t ht
  have ht' : M' + t • (e : J → ℝ) ∈
      intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) := by
    change meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ₀ : J → ℝ) +
      t • (e : J → ℝ) ∈
      intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) at ht
    rwa [hmean] at ht
  have ht'' : M' + t • (e : J → ℝ) ∈ intrinsicInterior ℝ (carriedResponses S A) := by
    rwa [intrinsicInterior_momentBody_faceMeasure hS ν hν A] at ht'
  unfold lineObservable responseLine
  rw [hmean, ← responseProjection_eq_familyMeasure_responseTheta hS (faceMeasure ν A) ht']
  subst hA
  rw [responseProjection_eq_faceMeasure_of_mem_intrinsicInterior hS ν hν hM ht'']

end FaceDerivative

end Laplace.Multi
