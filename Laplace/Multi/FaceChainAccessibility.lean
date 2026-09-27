/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FaceEmbedExtension
import Laplace.Multi.ConditioningCertificate
import Laplace.Multi.FaceResponsePythagoras

/-!
# Face chains: the coherent nonexpanding boundary atlas

For a sub-model `μ'` (direction space `W' ⊆ W`) with accessible seed `x₀` the extended embedding
`ĵ : Ŵ' → Ŵ` of `FaceEmbedExtension` is compatible with the laws, the tilt actions and nested
sub-models:

* **law compatibility at completion points**: `Q_{ĵ y} = Q'_y` (`completionLaw_faceEmbedExt`), the
  ambient law of an embedded point is its intrinsic law;
* **equivariance**: `ĵ (tiltExt' h y) = tiltExt h (ĵ y)` (`faceEmbedExt_tiltExt`);
* **chain compatibility**: for a sub-model `μ_E` of `μ_A` (itself a sub-model of `ν`), the composite
  `ĵ_A ∘ ĵ^A_E` is the direct embedding `ĵ_E` built from the transported seed `ĵ_A y₀`
  (`faceEmbedExt_faceEmbedExt`);
* **nested faces are nested sub-models**: `(ν_A)_E = ν_E` for `E ⊆ A` (`faceMeasure_faceMeasure`)
  and `W_E ⊆ W_A` (`dirSpan_faceMeasure_le_of_subset`).

Together with the mean compatibility and nonexpansion this is the coherent nonexpanding boundary
atlas of the response completion: law, mean, nonexpansion and chain compatibilities, with seed
independence following from uniqueness of the fibres on interior face points.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Law

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (μ' : Measure X) [IsProbabilityMeasure μ']
  (hle : dirSpan μ' (fun _ ↦ (1 : ℝ)) S ≤ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
  {x₀ : FisherCompletion hS ν} {v₀ : dirSpan μ' (fun _ ↦ (1 : ℝ)) S}
  (hx₀ : completionLaw hS ν x₀ =
    familyMeasure μ' (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀ : J → ℝ))
include hS hle hx₀

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] [IsProbabilityMeasure μ'] hle
  hx₀ in
theorem bdd_indicator_one {B : Set X} (hB : MeasurableSet B) : Bdd (B.indicator (1 : X → ℝ)) :=
  ⟨measurable_one.indicator hB, 1, fun x ↦ by
    by_cases h : x ∈ B <;> simp [h]⟩

/-- **Law compatibility at completion points**: the ambient law of an embedded point of the
sub-model completion is its intrinsic law, `Q_{ĵ y} = Q'_y`. -/
theorem completionLaw_faceEmbedExt (y : FisherCompletion hS μ') :
    completionLaw hS ν (faceEmbedExt hS ν μ' hle x₀ v₀ y) = completionLaw hS μ' y := by
  have key : ∀ B : Set X, MeasurableSet B → ∀ y : FisherCompletion hS μ',
      (completionLaw hS ν (faceEmbedExt hS ν μ' hle x₀ v₀ y) B).toReal =
        (completionLaw hS μ' y B).toReal := by
    intro B hB
    have e1 : (fun y : FisherCompletion hS μ' ↦
        (completionLaw hS ν (faceEmbedExt hS ν μ' hle x₀ v₀ y) B).toReal) =
        fun y ↦ ∫ x, B.indicator (1 : X → ℝ) x
          ∂completionLaw hS ν (faceEmbedExt hS ν μ' hle x₀ v₀ y) := by
      funext y
      rw [integral_indicator_one hB, measureReal_def]
    have e2 : (fun y : FisherCompletion hS μ' ↦ (completionLaw hS μ' y B).toReal) =
        fun y ↦ ∫ x, B.indicator (1 : X → ℝ) x ∂completionLaw hS μ' y := by
      funext y
      rw [integral_indicator_one hB, measureReal_def]
    intro y
    refine UniformSpace.Completion.induction_on y ?_ fun p ↦ ?_
    · refine isClosed_eq ?_ ?_
      · rw [e1]
        exact (continuous_integral_completionLaw hS ν (bdd_indicator_one hB)).comp
          (continuous_faceEmbedExt hS ν μ' hle hx₀)
      · rw [e2]
        exact continuous_integral_completionLaw hS μ' (bdd_indicator_one hB)
    · rw [faceEmbedExt_coe hS ν μ' hle hx₀, completionLaw_faceEmbed hS ν μ' hle hx₀,
        completionLaw_coe hS μ' p]
  ext B hB
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (key B hB y)

/-- **Equivariance of the extended embedding under the tilt actions.** -/
theorem faceEmbedExt_tiltExt (h : dirSpan μ' (fun _ ↦ (1 : ℝ)) S) (y : FisherCompletion hS μ') :
    faceEmbedExt hS ν μ' hle x₀ v₀ (tiltExt hS μ' h y) =
      tiltExt hS ν ⟨(h : J → ℝ), hle h.2⟩ (faceEmbedExt hS ν μ' hle x₀ v₀ y) := by
  refine UniformSpace.Completion.induction_on y ?_ fun p ↦ ?_
  · exact isClosed_eq ((continuous_faceEmbedExt hS ν μ' hle hx₀).comp (continuous_tiltExt hS μ' h))
      ((continuous_tiltExt hS ν _).comp (continuous_faceEmbedExt hS ν μ' hle hx₀))
  · rw [tiltExt_coe, faceEmbedExt_coe hS ν μ' hle hx₀, faceEmbedExt_coe hS ν μ' hle hx₀, faceEmbed,
      faceEmbed, tiltExt_tiltExt]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_add, faceDir_coe, faceDir_coe, tiltPoint_param]
    ring

end Law

section Chain

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (μA : Measure X) [IsProbabilityMeasure μA]
  (hleA : dirSpan μA (fun _ ↦ (1 : ℝ)) S ≤ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
  {x₀ : FisherCompletion hS ν} {v₀ : dirSpan μA (fun _ ↦ (1 : ℝ)) S}
  (hx₀ : completionLaw hS ν x₀ =
    familyMeasure μA (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀ : J → ℝ))
  (μE : Measure X) [IsProbabilityMeasure μE]
  (hleEA : dirSpan μE (fun _ ↦ (1 : ℝ)) S ≤ dirSpan μA (fun _ ↦ (1 : ℝ)) S)
  {y₀ : FisherCompletion hS μA} {u₀ : dirSpan μE (fun _ ↦ (1 : ℝ)) S}
  (hy₀ : completionLaw hS μA y₀ =
    familyMeasure μE (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (u₀ : J → ℝ))
include hS hleA hx₀ hleEA hy₀

omit [IsProbabilityMeasure μE] hleEA in
/-- The transported seed `ĵ_A y₀` is a seed for the direct embedding of `μ_E`. -/
theorem completionLaw_faceEmbedExt_seed :
    completionLaw hS ν (faceEmbedExt hS ν μA hleA x₀ v₀ y₀) =
      familyMeasure μE (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (u₀ : J → ℝ) := by
  rw [completionLaw_faceEmbedExt hS ν μA hleA hx₀, hy₀]

/-- **Chain compatibility**: `ĵ_A ∘ ĵ^A_E = ĵ_E`, the direct embedding of `μ_E` built from the
transported seed `ĵ_A y₀`. -/
theorem faceEmbedExt_faceEmbedExt (z : FisherCompletion hS μE) :
    faceEmbedExt hS ν μA hleA x₀ v₀ (faceEmbedExt hS μA μE hleEA y₀ u₀ z) =
      faceEmbedExt hS ν μE (hleEA.trans hleA) (faceEmbedExt hS ν μA hleA x₀ v₀ y₀) u₀ z := by
  have hx₁ := completionLaw_faceEmbedExt_seed hS ν μA hleA hx₀ μE hy₀
  refine UniformSpace.Completion.induction_on z ?_ fun p ↦ ?_
  · exact isClosed_eq ((continuous_faceEmbedExt hS ν μA hleA hx₀).comp
      (continuous_faceEmbedExt hS μA μE hleEA hy₀))
      (continuous_faceEmbedExt hS ν μE (hleEA.trans hleA) hx₁)
  · rw [faceEmbedExt_coe hS μA μE hleEA hy₀, faceEmbedExt_coe hS ν μE (hleEA.trans hleA) hx₁,
      faceEmbed, faceEmbed, faceEmbedExt_tiltExt hS ν μA hleA hx₀]
    congr 1

end Chain

section Nested

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- **Nested faces**: the face law of `E ⊆ A` inside the face law of `A` is the face law of `E`. -/
theorem faceMeasure_faceMeasure_of_subset {A E : Set X} (hA : MeasurableSet A)
    (hE : MeasurableSet E) (hEA : E ⊆ A) (hA0 : ν A ≠ 0) :
    faceMeasure (faceMeasure ν A) E = faceMeasure ν E := by
  rw [faceMeasure_faceMeasure ν hA hE hA0, Set.inter_eq_right.2 hEA]

omit [Nonempty X] [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **Nested faces are nested sub-models**: `W_E ⊆ W_A` for `E ⊆ A`. -/
theorem dirSpan_faceMeasure_le_of_subset {A E : Set X} (hA : MeasurableSet A) (hE : MeasurableSet E)
    (hEA : E ⊆ A) (hpA : 0 < ν.real A) (hpE : 0 < ν.real E) :
    dirSpan (faceMeasure ν E) (fun _ ↦ (1 : ℝ)) S ≤
      dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S := by
  have hPA := isProbabilityMeasure_faceMeasure_of_real_pos ν hpA
  have hA0 : ν A ≠ 0 := fun h ↦ by simp [measureReal_def, h] at hpA
  have hpE' : 0 < (faceMeasure ν A).real E := by
    rw [measureReal_def, faceMeasure_apply ν hA E, Set.inter_eq_left.2 hEA,
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hE0 : 0 < (ν E).toReal := hpE
    exact mul_pos (inv_pos.2 (ENNReal.toReal_pos hA0 (measure_ne_top _ _))) hE0
  rw [← faceMeasure_faceMeasure_of_subset ν hA hE hEA hA0]
  exact dirSpan_faceMeasure_le hS (faceMeasure ν A) E hE hpE'

end Nested

end Laplace.Multi
