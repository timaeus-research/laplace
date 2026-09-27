/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BoundedTiltCompletionAction
import Laplace.Multi.FacetCompletionAccess
import Laplace.Multi.FacetCompletionLaw

/-!
# One accessible facet point makes the whole facet accessible

Over a facet `F = {⟨u,·⟩ = β}` of a charged polytope, the completion point over a mean
`M ∈ ri F` exists iff the normal ray has finite Fisher length, and its law is the face
exponential-family law `P^A_{v_M}` (`FacetCompletionAccess`, `FacetCompletionLaw`). The
bounded-tilt action moves this one point through the whole face family: `tiltExt h x` has law
`P^A_{v_M + h}` and extended mean `m_A(v_M + h)`, and since the face mean map is onto the relative
interior of the face body, **every point of `ri(momentBody ν_A)` is an extended mean as soon as one
is** (`forall_exists_meanExt_eq_of_facet`). Accessibility is a property of the open facet, not of
individual points on it.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Facet

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- **From one accessible facet point to the whole open facet**: if the normal ray of the facet
has finite Fisher length, every point of the relative interior of the facet body is an extended
mean of the Fisher completion. -/
theorem forall_exists_meanExt_eq_of_facet {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β)
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
    (hM' : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)
    (hray : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) u r))) < ⊤)
    {M' : J → ℝ} (hM'' : M' ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)) :
    ∃ x' : FisherCompletion hS ν, meanExt hS ν x' = M' := by
  obtain ⟨x, hx⟩ := (exists_meanExt_eq_iff_ray hS ν V hpoly hcharged hV hM hMβ hF hMint hv₀V hv₀β
    hzV hz huW hu hT).2 hray
  have hlaw := completionLaw_eq_faceFamily hS ν V hpoly hcharged hV hM hMβ hF hMint hM' hv₀V hv₀β
    hzV hz huW hu hT hx
  have hp : 0 < ν.real {x | dirLoss S u x = β} := faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hWA := dirSpan_faceMeasure_le hS ν {x | dirLoss S u x = β}
    (measurableSet_faceFibre hS u β) hp
  obtain ⟨h, hhdef⟩ : ∃ h : dirSpan ν (fun _ ↦ (1 : ℝ)) S, h =
      ⟨(faceThetaOf hS ν {x | dirLoss S u x = β} hM'' : J → ℝ) -
        (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ),
        hWA (Submodule.sub_mem _ (faceThetaOf _ _ _ hM'').2 (faceThetaOf _ _ _ hM').2)⟩ := ⟨_, rfl⟩
  refine ⟨tiltExt hS ν h x, ?_⟩
  rw [meanExt_tiltExt_faceFamily hS ν _ h x hlaw, hhdef]
  simp only [add_sub_cancel]
  exact meanMap_faceThetaOf hS ν _ hM''

end Facet

end Laplace.Multi
