/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FaceChainAccessibility
import Laplace.Multi.FaceFibreUnique
import Laplace.Multi.FixedNormalLimit
import Laplace.Multi.DataResponseMap

/-!
# Seed independence: the canonical boundary atlas

The sub-model embedding `ĵ : Ŵ' → Ŵ` of `FaceEmbedExtension` is built from a **seed** `(x₀, v₀)`:
a completion point `x₀` whose law is the sub-model law `Q'_{v₀}`. This file classifies the seeds
giving the same embedding and shows that on charged faces the embedding is canonical.

* **Tilt-orbit classification** (`faceEmbedExt_eq_iff`): two admissible seeds give the same
  extended embedding iff they lie on the same orbit of the ambient tilt action,
  `x₀' = tiltExt (v₀' − v₀) x₀`. Equivalently the finite embeddings agree at *one* parameter
  (`faceEmbedExt_eq_of_faceEmbed_eq`), and the seed can always be transported along the finite
  embedding without changing the extension (`faceEmbedExt_transport`).
* **One singleton fibre suffices** (`faceEmbedExt_eq_of_completionLaw_unique`,
  `faceEmbedExt_eq_of_meanExt_unique`): if the ambient completion fibre over one finite sub-model
  law (or one finite sub-model mean) is a single point, every admissible seed pair produces the
  same extension.
* **Injectivity** (`faceEmbedExt_injective`): the extension is injective whenever the source
  completion has unique law fibres — nonexpansion and law compatibility alone do not give it.
* **The canonical charged-face atlas** (`faceEmbedExt_eq_of_charged_face`): for a charged
  polytope model and an exposed face, every seed pair gives the same extension `ĵ_F : Ŵ_F → Ŵ`,
  because every finite face mean lies in the relative interior of the face, where the ambient
  fibre is a single point (`meanExt_eq_face_unique`). The face atlas of
  `FaceChainAccessibility` is therefore seed-free: law and mean compatible, `1`-Lipschitz, tilt
  equivariant and chain compatible, with no choices made.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Orbit

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (μ' : Measure X) [IsProbabilityMeasure μ']
  (hle : dirSpan μ' (fun _ ↦ (1 : ℝ)) S ≤ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
include hS hle

/-- The sub-model direction space. -/
local notation "𝕍A" => dirSpan μ' (fun _ ↦ (1 : ℝ)) S

/-- The sub-model family. -/
local notation "Qface" => familyMeasure μ' (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] [IsProbabilityMeasure μ'] in
theorem faceDir_add (v₀ w w' : 𝕍A) :
    faceDir ν μ' hle v₀ w + faceDir ν μ' hle w w' = faceDir ν μ' hle v₀ w' := by
  apply Subtype.ext
  rw [Submodule.coe_add, faceDir_coe, faceDir_coe, faceDir_coe]
  ring

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] [IsProbabilityMeasure μ'] in
theorem faceDir_self (v₀ : 𝕍A) : faceDir ν μ' hle v₀ v₀ = 0 :=
  Subtype.ext (by rw [faceDir_coe, sub_self]; rfl)

omit [IsProbabilityMeasure μ'] in
/-- The finite embedding returns the seed at the seed parameter: `j(v₀) = x₀`. -/
theorem faceEmbed_self (x₀ : FisherCompletion hS ν) (v₀ : 𝕍A) :
    faceEmbed hS ν μ' hle x₀ v₀ v₀ = x₀ := by
  rw [faceEmbed, faceDir_self, tiltExt_zero]

omit [IsProbabilityMeasure μ'] in
/-- **Finite equivariance**: the ambient tilt by `w' − w` carries `j(w)` to `j(w')`. -/
theorem tiltExt_faceEmbed (x₀ : FisherCompletion hS ν) (v₀ w w' : 𝕍A) :
    tiltExt hS ν (faceDir ν μ' hle w w') (faceEmbed hS ν μ' hle x₀ v₀ w) =
      faceEmbed hS ν μ' hle x₀ v₀ w' := by
  rw [faceEmbed, faceEmbed, tiltExt_tiltExt, faceDir_add]

omit [IsProbabilityMeasure μ'] in
/-- **Seed transport on finite parameters**: the embedding seeded at `(j(v₀'), v₀')` is the
embedding seeded at `(x₀, v₀)`. -/
theorem faceEmbed_transport (x₀ : FisherCompletion hS ν) (v₀ v₀' w : 𝕍A) :
    faceEmbed hS ν μ' hle (faceEmbed hS ν μ' hle x₀ v₀ v₀') v₀' w =
      faceEmbed hS ν μ' hle x₀ v₀ w :=
  tiltExt_faceEmbed hS ν μ' hle x₀ v₀ v₀' w

variable {x₀ : FisherCompletion hS ν} {v₀ : dirSpan μ' (fun _ ↦ (1 : ℝ)) S}
  (hx₀ : completionLaw hS ν x₀ =
    familyMeasure μ' (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀ : J → ℝ))
include hx₀

/-- **Tilt-orbit classification of seeds**: two admissible seeds give the same extended embedding
iff the second seed is the ambient tilt of the first by the parameter difference. -/
theorem faceEmbedExt_eq_iff {x₀' : FisherCompletion hS ν} {v₀' : 𝕍A}
    (hx₀' : completionLaw hS ν x₀' = Qface (v₀' : J → ℝ)) :
    faceEmbedExt hS ν μ' hle x₀ v₀ = faceEmbedExt hS ν μ' hle x₀' v₀' ↔
      x₀' = tiltExt hS ν (faceDir ν μ' hle v₀ v₀') x₀ := by
  constructor
  · intro h
    have := congrFun h ((⟨v₀'⟩ : FisherPoint hS μ') : FisherCompletion hS μ')
    rw [faceEmbedExt_coe hS ν μ' hle hx₀, faceEmbedExt_coe hS ν μ' hle hx₀'] at this
    change faceEmbed hS ν μ' hle x₀ v₀ v₀' = faceEmbed hS ν μ' hle x₀' v₀' v₀' at this
    rw [faceEmbed_self] at this
    exact this.symm
  · intro h
    refine UniformSpace.Completion.ext (continuous_faceEmbedExt hS ν μ' hle hx₀)
      (continuous_faceEmbedExt hS ν μ' hle hx₀') fun p ↦ ?_
    rw [faceEmbedExt_coe hS ν μ' hle hx₀, faceEmbedExt_coe hS ν μ' hle hx₀', h]
    exact (faceEmbed_transport hS ν μ' hle x₀ v₀ v₀' p.param).symm

/-- **Agreement at one finite parameter forces agreement of the extensions.** -/
theorem faceEmbedExt_eq_of_faceEmbed_eq {x₀' : FisherCompletion hS ν} {v₀' : 𝕍A}
    (hx₀' : completionLaw hS ν x₀' = Qface (v₀' : J → ℝ)) {w : 𝕍A}
    (h : faceEmbed hS ν μ' hle x₀ v₀ w = faceEmbed hS ν μ' hle x₀' v₀' w) :
    faceEmbedExt hS ν μ' hle x₀ v₀ = faceEmbedExt hS ν μ' hle x₀' v₀' := by
  rw [faceEmbedExt_eq_iff hS ν μ' hle hx₀ hx₀']
  have := congrArg (tiltExt hS ν (faceDir ν μ' hle w v₀')) h
  rw [tiltExt_faceEmbed, tiltExt_faceEmbed, faceEmbed_self] at this
  exact this.symm

/-- **Seed transport**: the seed may be moved along the finite embedding without changing the
extension. -/
theorem faceEmbedExt_transport (v₀' : 𝕍A) :
    faceEmbedExt hS ν μ' hle (faceEmbed hS ν μ' hle x₀ v₀ v₀') v₀' =
      faceEmbedExt hS ν μ' hle x₀ v₀ :=
  ((faceEmbedExt_eq_iff hS ν μ' hle hx₀ (completionLaw_faceEmbed hS ν μ' hle hx₀ v₀')).2 rfl).symm

/-- **One singleton law fibre suffices**: if the ambient completion fibre over one finite sub-model
law `Q'_w` is a single point, every admissible seed pair gives the same extension. -/
theorem faceEmbedExt_eq_of_completionLaw_unique {x₀' : FisherCompletion hS ν} {v₀' : 𝕍A}
    (hx₀' : completionLaw hS ν x₀' = Qface (v₀' : J → ℝ)) {w : 𝕍A}
    (hfib : ∀ x y : FisherCompletion hS ν, completionLaw hS ν x = Qface (w : J → ℝ) →
      completionLaw hS ν y = Qface (w : J → ℝ) → x = y) :
    faceEmbedExt hS ν μ' hle x₀ v₀ = faceEmbedExt hS ν μ' hle x₀' v₀' :=
  faceEmbedExt_eq_of_faceEmbed_eq hS ν μ' hle hx₀ hx₀' (hfib _ _
    (completionLaw_faceEmbed hS ν μ' hle hx₀ w) (completionLaw_faceEmbed hS ν μ' hle hx₀' w))

/-- **One singleton mean fibre suffices**: if the ambient completion fibre over one finite
sub-model mean `m'(w)` is a single point, every admissible seed pair gives the same extension. -/
theorem faceEmbedExt_eq_of_meanExt_unique {x₀' : FisherCompletion hS ν} {v₀' : 𝕍A}
    (hx₀' : completionLaw hS ν x₀' = Qface (v₀' : J → ℝ)) {w : 𝕍A}
    (hfib : ∀ x y : FisherCompletion hS ν,
      meanExt hS ν x = meanMap μ' (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (w : J → ℝ) →
      meanExt hS ν y = meanMap μ' (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (w : J → ℝ) →
      x = y) :
    faceEmbedExt hS ν μ' hle x₀ v₀ = faceEmbedExt hS ν μ' hle x₀' v₀' :=
  faceEmbedExt_eq_of_faceEmbed_eq hS ν μ' hle hx₀ hx₀' (hfib _ _
    (meanExt_faceEmbed hS ν μ' hle hx₀ w) (meanExt_faceEmbed hS ν μ' hle hx₀' w))

/-- **Injectivity from unique source fibres**: the extended embedding is injective whenever two
points of the sub-model completion with the same law coincide. -/
theorem faceEmbedExt_injective
    (huniq : ∀ y z : FisherCompletion hS μ', completionLaw hS μ' y = completionLaw hS μ' z →
      y = z) :
    Function.Injective (faceEmbedExt hS ν μ' hle x₀ v₀) := fun y z h ↦
  huniq y z (by
    rw [← completionLaw_faceEmbedExt hS ν μ' hle hx₀, ← completionLaw_faceEmbedExt hS ν μ' hle hx₀,
      h])

end Orbit

section Charged

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
  {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
include hS hpoly hcharged hV

omit [MeasurableSpace X] [Nonempty X] hS [IsProbabilityMeasure ν] hpoly hcharged in
/-- A point of the exposed face charges a vertex of the exposed face. -/
theorem exists_charged_vertex_on_face {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u M = β) : ∃ z₀ ∈ V, dotJ u z₀ = β ∧ z₀ ∈ minimalFacePoly V M := by
  obtain ⟨z₀, hz₀⟩ := convexHull_nonempty_iff.1 ⟨M, mem_minimalFacePoly hM⟩
  have hz₀F : z₀ ∈ minimalFacePoly V M := subset_convexHull ℝ _ hz₀
  refine ⟨z₀, chargedVertices_subset V M hz₀, ?_, hz₀F⟩
  have hint := (mem_intrinsicInterior_iff_forall_supporting (K := minimalFacePoly V M)
    (convex_convexHull ℝ _)).1 (mem_intrinsicInterior_minimalFacePoly hM)
  have hhull : convexHull ℝ (V : Set (J → ℝ)) ⊆ {y | dotJ u y ≤ β} :=
    convexHull_min (fun v hv ↦ hV v (Finset.mem_coe.1 hv)) (convex_halfspace_dotJ u β)
  have := hint.2 u (fun y hy ↦ by
    rw [hMβ]
    exact hhull (minimalFacePoly_subset V M hy)) z₀ hz₀F
  rw [this, hMβ]

variable (hle : dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S ≤
    dirSpan ν (fun _ ↦ (1 : ℝ)) S)
  (hp : 0 < ν.real {x | dirLoss S u x = β})
  [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
include hle hp

omit [Nonempty J] [IsProbabilityMeasure ν] [Nonempty V] hpoly hcharged hV hle hp in
/-- The finite face means lie in the relative interior of the face moment body. -/
theorem meanMap_faceMeasure_mem_intrinsicInterior (w : J → ℝ) :
    meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 w ∈
      intrinsicInterior ℝ
        (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) := by
  rw [← mean_familyMeasure_one_zero hS _ w, familyMeasure_one_zero_eq_tilted hS _ w]
  exact mean_tilted_mem_intrinsicInterior hS _ ((bdd_dirLoss hS w).const_mul (-1))

/-- **The canonical charged-face atlas**: on an exposed face of a charged polytope model every
admissible seed pair gives the same extended embedding `ĵ_F : Ŵ_F → Ŵ`. -/
theorem faceEmbedExt_eq_of_charged_face {x₀ x₀' : FisherCompletion hS ν}
    {v₀ v₀' : dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S}
    (hx₀ : completionLaw hS ν x₀ = familyMeasure (faceMeasure ν {x | dirLoss S u x = β})
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀ : J → ℝ))
    (hx₀' : completionLaw hS ν x₀' = familyMeasure (faceMeasure ν {x | dirLoss S u x = β})
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v₀' : J → ℝ)) :
    faceEmbedExt hS ν _ hle x₀ v₀ = faceEmbedExt hS ν _ hle x₀' v₀' := by
  refine faceEmbedExt_eq_of_meanExt_unique hS ν _ hle hx₀ hx₀' (w := v₀) fun x y hx hy ↦ ?_
  have hAm := measurableSet_faceFibre hS u β
  have hMint := meanMap_faceMeasure_mem_intrinsicInterior hS ν (u := u) (β := β) (v₀ : J → ℝ)
  have hMbody := intrinsicInterior_subset hMint
  have hM : meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ))
      S 1 (v₀ : J → ℝ) ∈ convexHull ℝ (V : Set (J → ℝ)) := by
    rw [← hpoly]
    exact momentBody_faceMeasure_subset ν hAm hS hp hMbody
  have hMβ : dotJ u (meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (v₀ : J → ℝ)) = β :=
    momentBody_faceMeasure_subset_hyperplane ν hAm hS hp rfl hMbody
  obtain ⟨z₀, hz₀V, hz₀β, hz₀F⟩ := exists_charged_vertex_on_face V hV hM hMβ
  exact meanExt_eq_face_unique hS ν V hpoly hcharged hV hz₀V hz₀β hM hMβ hz₀F hMint hx hy

end Charged

end Laplace.Multi
