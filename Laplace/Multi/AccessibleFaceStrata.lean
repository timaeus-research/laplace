/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CompletionLawEqProjection
import Laplace.Multi.FaceResponsePythagoras
import Laplace.Multi.PolytopeFaceCut

/-!
# Accessible face strata

The accessible extended means of the Fisher completion form a union of relative interiors of
faces. For an exposed face event `A = {⟨u,S⟩ = β}` of a charged polytope: the variational
response at a face-family mean is the face-family law itself, `Π(m_A(v)) = P^A_v`
(`responseProjection_eq_faceFamily`, by the two Pythagorean identities and uniqueness of the
information projection); so if some completion point `x` has extended mean `M₀ ∈ ri(momentBody ν_A)`
its law is `P^A_{v₀}` (`completionLaw_eq_responseProjection`), and the bounded-tilt action moves it
to `P^A_v` for every face parameter `v`. Since the face mean map is onto `ri(momentBody ν_A)`,
**one extended mean in the relative interior of a face makes the whole relative interior
accessible** (`exists_meanExt_eq_of_mem_ri_face`), in every codimension and from an arbitrary
accessible point (no normal ray).
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Strata

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

variable {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V)
  (hz₀β : dotJ u z₀ = β) {A : Set X} (hA : A = {x | dirLoss S u x = β})
include hV hz₀V hz₀β hA

/-- The face family. -/
local notation "Qface" => familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The face mean map. -/
local notation "meanA" => meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty V] in
/-- **The variational response at a face-family mean is the face-family law**:
`Pi(m_A(v)) = P^A_v`. -/
theorem responseProjection_eq_faceFamily (v : J → ℝ) :
    responseProjection hS ν (meanA v) = Qface v := by
  have hp : 0 < ν.real A := hA ▸ faceFibre_pos_of_charged ν V hcharged hz₀V hz₀β
  have hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β :=
    ae_dirLoss_le_of_polytope hS ν V (u := u) (β := β) hpoly hV
  have hνA := isProbabilityMeasure_faceMeasure_of_real_pos ν hp
  have hQf := isProbabilityMeasure_family hS (faceMeasure ν A) v
  have hAm : MeasurableSet A := measurableSet_of_eq_faceFibre hS hA
  have hQν : Qface v ≪ ν := by
    refine (faceFamily_absolutelyContinuous hS ν hp v).trans ?_
    rw [faceMeasure_eq_withDensity ν hAm]
    exact withDensity_absolutelyContinuous _ _
  have hmean := mean_familyMeasure_one_zero hS (faceMeasure ν A) v
  have hM : meanA v ∈ convexHull ℝ (V : Set (J → ℝ)) := by
    rw [← hpoly, ← hmean]
    exact mean_mem_momentBody_of_ac hS ν _ hQν
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  obtain ⟨hP, hPmean, hPkl, hpyth⟩ := responseProjection_spec hS ν hfin
  have hPac := responseProjection_absolutelyContinuous hS ν hfin
  have h1 := hpyth (Qface v) hQf hmean
  have h2 := klDiv_faceFamily_le hS ν hβ hA hp v _ hPac hPmean
  have heq : klDiv (responseProjection hS ν (meanA v)) ν = klDiv (Qface v) ν := by
    refine le_antisymm ?_ h2
    rw [hPkl, h1]
    exact le_add_self
  exact eq_faceFamily_of_klDiv_eq hS ν hβ hA hp v _ hPac hPmean heq

/-- **One extended mean in the relative interior of a face makes the whole relative interior
accessible.** -/
theorem exists_meanExt_eq_of_mem_ri_face [IsProbabilityMeasure (faceMeasure ν A)] {M₀ : J → ℝ}
    (hM₀ : M₀ ∈ intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S))
    {x : FisherCompletion hS ν} (hx : meanExt hS ν x = M₀) {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S)) :
    ∃ x' : FisherCompletion hS ν, meanExt hS ν x' = M := by
  have hp : 0 < ν.real A := hA ▸ faceFibre_pos_of_charged ν V hcharged hz₀V hz₀β
  have hWA := dirSpan_faceMeasure_le hS ν A (measurableSet_of_eq_faceFibre hS hA) hp
  have e := meanMap_faceThetaOf hS ν A hM₀
  have hQx : completionLaw hS ν x = Qface (faceThetaOf hS ν A hM₀ : J → ℝ) := by
    rw [completionLaw_eq_responseProjection hS ν V hpoly hcharged x, hx]
    calc responseProjection hS ν M₀ =
          responseProjection hS ν (meanA (faceThetaOf hS ν A hM₀ : J → ℝ)) := by rw [e]
      _ = Qface (faceThetaOf hS ν A hM₀ : J → ℝ) :=
          responseProjection_eq_faceFamily hS ν V hpoly hcharged hV hz₀V hz₀β hA _
  obtain ⟨h, hhdef⟩ : ∃ h : dirSpan ν (fun _ ↦ (1 : ℝ)) S, h =
      ⟨(faceThetaOf hS ν A hM : J → ℝ) - (faceThetaOf hS ν A hM₀ : J → ℝ),
        hWA (Submodule.sub_mem _ (faceThetaOf _ _ _ hM).2 (faceThetaOf _ _ _ hM₀).2)⟩ := ⟨_, rfl⟩
  refine ⟨tiltExt hS ν h x, ?_⟩
  rw [meanExt_tiltExt_faceFamily hS ν _ h x hQx, hhdef]
  simp only [add_sub_cancel]
  exact meanMap_faceThetaOf hS ν _ hM

end Strata

end Laplace.Multi
