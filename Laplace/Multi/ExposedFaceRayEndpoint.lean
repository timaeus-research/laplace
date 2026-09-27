/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteRangeRayDecay
import Laplace.Multi.ResponseAtlasClosure
import Laplace.Multi.TiltedFisherCompactConvergence

/-!
# A finite-length normal ray reaches the face law, in any codimension

For an exposed face `{⟨u,S⟩ = β}` of positive mass, with `u` and the base point `θ` in the direction
space, the natural ray `θ − t u` is a `W`-path whose Fisher speed is `√raySpeedSq`
(`fisherNorm_rayPath`). If that speed is integrable, the ray converges in the completion to an
endpoint `rayEndpoint` (`tendsto_rayEndpoint`, `dist_rayEndpoint_le_tail`), the ray means converge
to the face-family mean `m_F(θ)` (`tendsto_meanMap_ray`, from the total-variation convergence of
the ray law to the face law), so the endpoint has extended mean `m_F(θ)` in the relative interior
of the face body (`meanExt_rayEndpoint`, `meanExt_rayEndpoint_mem`) and, on a charged polytope,
law `P^F_θ` (`completionLaw_rayEndpoint`). Hence **the face is accessible** (`accessible_of_ray`).
No transversality hypothesis is needed: the argument is the same in every codimension.
-/

open MeasureTheory Filter Topology Set

set_option quotPrecheck false

namespace Laplace.Multi

section Ray

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {θ u : J → ℝ} (hθW : θ ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
include hS hθW huW

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The natural ray lies in the direction space. -/
theorem rayPath_mem (s : ℝ) : θ - s • u ∈ 𝕍 := Submodule.sub_mem _ hθW (Submodule.smul_mem _ _ huW)

set_option linter.unusedFintypeInType false in
omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hθW huW in
theorem hasDerivAt_rayPath (s : ℝ) : HasDerivAt (fun s : ℝ ↦ θ - s • u) (-u) s := by
  simpa using ((hasDerivAt_id s).smul_const u).const_sub θ

omit [Nonempty J] hθW huW in
/-- **The Fisher speed of the ray is the ray speed.** -/
theorem fisherNorm_rayPath (s : ℝ) :
    fisherNorm S ν (θ - s • u) (-u) = √(raySpeedSq S ν θ u s) := by
  rw [fisherNorm, raySpeedSq, fisherVar]
  have hP := isProbabilityMeasure_family hS ν (θ - s • u)
  congr 1
  have e : dirLoss S (-u) = fun x ↦ -dirLoss S u x := funext fun x ↦ dirLoss_neg u x
  rw [e, lawCov_neg_left, lawCov_comm, lawCov_neg_left, lawCov_comm, neg_neg]

variable (hint : IntegrableOn (fun t ↦ √(raySpeedSq S ν θ u t)) (Ioi (0 : ℝ)))
include hint

omit [Nonempty J] hθW huW in
theorem integrableOn_fisherNorm_rayPath :
    IntegrableOn (fun s ↦ fisherNorm S ν (θ - s • u) (-u)) (Ioi (0 : ℝ)) :=
  hint.congr_fun (fun s _ ↦ (fisherNorm_rayPath hS ν s).symm) measurableSet_Ioi

/-- **The endpoint of the normal ray** in the completion. -/
noncomputable def rayEndpoint : FisherCompletion hS ν :=
  pathEndpoint hS ν (rayPath_mem ν hθW huW) (hasDerivAt_rayPath (θ := θ) (u := u))
    continuous_const (integrableOn_fisherNorm_rayPath hS ν hint)

theorem tendsto_rayEndpoint :
    Tendsto (fun t ↦ ((⟨⟨θ - t • u, rayPath_mem ν hθW huW t⟩⟩ : FisherPoint hS ν) :
      FisherCompletion hS ν)) atTop (𝓝 (rayEndpoint hS ν hθW huW hint)) :=
  tendsto_pathEndpoint hS ν _ _ _ _

/-- **The tail estimate**: `d̂(ι(θ − Tu), ξ) ≤ ∫_T^∞ √raySpeedSq`. -/
theorem dist_rayEndpoint_le_tail {T : ℝ} (hT : 0 ≤ T) :
    dist (((⟨⟨θ - T • u, rayPath_mem ν hθW huW T⟩⟩ : FisherPoint hS ν) : FisherCompletion hS ν))
        (rayEndpoint hS ν hθW huW hint) ≤
      ∫ s in Ioi T, √(raySpeedSq S ν θ u s) := by
  have h := dist_pathEndpoint_le_tail hS ν (rayPath_mem ν hθW huW)
    (hasDerivAt_rayPath (θ := θ) (u := u)) continuous_const
    (integrableOn_fisherNorm_rayPath hS ν hint) hT
  refine h.trans (le_of_eq ?_)
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ fisherNorm_rayPath hS ν s

end Ray

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {θ u : J → ℝ} (hθW : θ ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
  {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) (hp : 0 < ν.real {x | dirLoss S u x = β})
include hS hθW huW hβ hp

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The face law. -/
local notation "νE" => faceMeasure ν {x | dirLoss S u x = β}

/-- The face mean map. -/
local notation "meanE" => meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
  (fun _ ↦ (0 : ℝ)) S 1

variable (hint : IntegrableOn (fun t ↦ √(raySpeedSq S ν θ u t)) (Ioi (0 : ℝ)))
include hint

/-- **The endpoint has the face-family mean** `m_F(θ)`. -/
theorem meanExt_rayEndpoint : meanExt hS ν (rayEndpoint hS ν hθW huW hint) = meanE θ :=
  tendsto_nhds_unique (tendsto_meanMap_pathEndpoint hS ν _ _ _ _)
    (tendsto_meanMap_ray hS ν θ u β hβ hp)

/-- **The endpoint's mean lies in the relative interior of the face body.** -/
theorem meanExt_rayEndpoint_mem :
    meanExt hS ν (rayEndpoint hS ν hθW huW hint) ∈
      intrinsicInterior ℝ (momentBody νE (fun _ ↦ (1 : ℝ)) S) := by
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν hp
  rw [meanExt_rayEndpoint hS ν hθW huW hβ hp hint]
  exact meanMap_faceMeasure_mem_intrinsicInterior hS ν (u := u) (β := β) θ

/-- **A finite-length normal ray makes its face accessible.** -/
theorem accessible_of_ray : Accessible hS ν u β :=
  ⟨rayEndpoint hS ν hθW huW hint, meanExt_rayEndpoint_mem hS ν hθW huW hβ hp hint⟩

variable (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) (hV : ∀ v ∈ V, dotJ u v ≤ β)
  {z₀ : J → ℝ} (hz₀V : z₀ ∈ V) (hz₀β : dotJ u z₀ = β)
include hpoly hcharged hV hz₀V hz₀β

/-- **The law of the endpoint is the face-family law** `P^F_θ` (charged polytope). -/
theorem completionLaw_rayEndpoint :
    completionLaw hS ν (rayEndpoint hS ν hθW huW hint) =
      familyMeasure νE (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := by
  rw [rayEndpoint, completionLaw_pathEndpoint_eq hS ν _ _ _ _ V hpoly hcharged
    (tendsto_meanMap_ray hS ν θ u β hβ hp)]
  exact responseProjection_eq_faceFamily hS ν V hpoly hcharged hV hz₀V hz₀β rfl θ

end Face

end Laplace.Multi
