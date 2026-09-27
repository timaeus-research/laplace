/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GlobalChart
import Laplace.Multi.FiniteCompletionClosure
import Laplace.Multi.MixtureResponseJourney
import Laplace.Multi.ResponseTwoScaleCertificate
import Laplace.Multi.ResponseEndpointInformationAction

/-!
# The mean-polytope journey of a finite full-support family

For a finite full-support family — saturated or not — the response domain is the **relative
interior of the moment polytope** `conv S(X)` (`intrinsicInterior_momentBody_eq_polytope`), and
the mean map is a homeomorphism of the direction space onto it (`meanPolytopeHomeomorph`, from
the seabed's global response chart), smooth in both directions (the seabed's `contDiff_meanMap`
and `contDiffOn_responseTheta_polytope`).

Consequently every **affine mean journey** `m_t = m_ν + t (p − m_ν)` towards an interior target
mean `p` lifts uniquely to a `C¹` response journey `θ_t = m⁻¹(m_t)` (`polytopeJourney`,
`meanMap_polytopeJourney`, `hasDerivAt_polytopeJourney`) whose law is the maximum-entropy law with
the prescribed means (`familyMeasure_polytopeJourney_eq_responseProjection`). Outside saturation the
response law `P_{θ_t}` is *not* the mixture `(1−t)ν + tD` of a data law `D` with mean `p` — only
their feature means agree (`meanMap_polytopeJourney_eq_mixLaw`): the response atlas charts the
quotient of the data laws by their feature means. In the saturated case the two coincide
(`polytopeJourney_meanMap_eq_modelJourney` with `atomMass_modelJourney_zero`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Polytope

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The featureless mean. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

omit [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The response domain is the relative interior of the moment polytope.** -/
theorem intrinsicInterior_momentBody_eq_polytope :
    Ω = intrinsicInterior ℝ hull := by
  rw [momentBody_eq_convexHull hS ν hν]

omit [MeasurableSingletonClass X] in
/-- **The mean map is a homeomorphism `W ≃ₜ relint conv S(X)`.** -/
noncomputable def meanPolytopeHomeomorph : 𝕍 ≃ₜ intrinsicInterior ℝ hull :=
  (relintChart hS ν).trans
    (Homeomorph.setCongr (intrinsicInterior_momentBody_eq_polytope hS ν hν))

omit [MeasurableSingletonClass X] in
theorem meanPolytopeHomeomorph_apply (θ : 𝕍) :
    (meanPolytopeHomeomorph hS ν hν θ : J → ℝ) = mean (θ : J → ℝ) := rfl

omit [MeasurableSingletonClass X] in
/-- The inverse of the polytope homeomorphism is the natural coordinate. -/
theorem meanPolytopeHomeomorph_symm_apply (M : intrinsicInterior ℝ hull) :
    (meanPolytopeHomeomorph hS ν hν).symm M = θr (M : J → ℝ) := by
  change (relintChart hS ν).symm
    ((Homeomorph.setCongr (intrinsicInterior_momentBody_eq_polytope hS ν hν)).symm M) = _
  rw [relintChart_symm_apply]
  rfl

omit [MeasurableSingletonClass X] in
/-- **The inverse mean map is `C^∞` on the relative interior of the polytope.** -/
theorem contDiffOn_responseTheta_polytope :
    ContDiffOn ℝ ∞ (fun z : 𝕍 ↦ θr (m₀ + (z : J → ℝ)))
      {z : 𝕍 | m₀ + (z : J → ℝ) ∈ intrinsicInterior ℝ hull} := by
  rw [← intrinsicInterior_momentBody_eq_polytope hS ν hν]
  exact contDiffOn_responseTheta_add hS ν

omit [MeasurableSingletonClass X] in
/-- The featureless mean is interior to the polytope. -/
theorem featureless_mem_polytope : m₀ ∈ intrinsicInterior ℝ hull := by
  rw [← intrinsicInterior_momentBody_eq_polytope hS ν hν]
  exact featureless_mem_intrinsicInterior hS ν

omit [MeasurableSingletonClass X] in
/-- An interior target mean differs from the featureless mean by a direction. -/
theorem sub_featureless_mem_dirSpan {p : J → ℝ}
    (hp : p ∈ intrinsicInterior ℝ hull) : p - m₀ ∈ 𝕍 := by
  rw [← intrinsicInterior_momentBody_eq_polytope hS ν hν] at hp
  exact sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS (intrinsicInterior_subset hp)

omit [MeasurableSingletonClass X] in
/-- The affine mean journey towards an interior target stays interior. -/
theorem polytope_segment_mem {p : J → ℝ}
    (hp : p ∈ intrinsicInterior ℝ hull) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    m₀ + t • (p - m₀) ∈ intrinsicInterior ℝ hull :=
  mem_intrinsicInterior_segment (convex_convexHull ℝ _) (featureless_mem_polytope hS ν hν) hp
    ht0 ht1

variable (p : J → ℝ)

omit [MeasurableSingletonClass X] hν in
/-- **The polytope journey**: the unique lift `θ_t = m⁻¹(m_ν + t(p − m_ν))` of the affine mean
journey towards the target mean `p`. -/
noncomputable def polytopeJourney (t : ℝ) : 𝕍 := θr (m₀ + t • (p - m₀))

omit [Fintype X] [MeasurableSingletonClass X] hν in
/-- The polytope journey starts at the featureless response. -/
theorem polytopeJourney_zero : polytopeJourney hS ν p 0 = 0 := by
  unfold polytopeJourney
  rw [zero_smul, add_zero]
  have := responseTheta_meanMap hS ν (0 : 𝕍)
  rwa [Submodule.coe_zero] at this

omit [Fintype X] [MeasurableSingletonClass X] hν in
/-- The polytope journey ends at the response of the target mean. -/
theorem polytopeJourney_one : polytopeJourney hS ν p 1 = θr p := by
  unfold polytopeJourney
  rw [one_smul, add_sub_cancel]

omit [MeasurableSingletonClass X] in
/-- **The lifted journey has the prescribed means.** -/
theorem meanMap_polytopeJourney (hp : p ∈ intrinsicInterior ℝ hull) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mean (polytopeJourney hS ν p t : J → ℝ) = m₀ + t • (p - m₀) := by
  have h := polytope_segment_mem hS ν hν hp ht0 ht1
  rw [← intrinsicInterior_momentBody_eq_polytope hS ν hν] at h
  exact meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS h

omit [MeasurableSingletonClass X] in
/-- **The velocity of the polytope journey**: `θ'_t = (Dm(θ_t)|_W)⁻¹ (p − m_ν)`. -/
theorem hasDerivAt_polytopeJourney (hp : p ∈ intrinsicInterior ℝ hull)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasDerivAt (polytopeJourney hS ν p)
      ((CDE (polytopeJourney hS ν p t)).symm
        ⟨p - m₀, sub_featureless_mem_dirSpan hS ν hν hp⟩) t := by
  have hV : ∀ s : ℝ, (m₀ + s • (p - m₀)) - m₀ ∈ 𝕍 := fun s ↦ by
    rw [add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (sub_featureless_mem_dirSpan hS ν hν hp)
  have hM' : HasDerivAt (fun s : ℝ ↦ m₀ + s • (p - m₀)) (p - m₀) t := by
    simpa using ((hasDerivAt_id t).smul_const (p - m₀)).const_add m₀
  have hrel := polytope_segment_mem hS ν hν hp ht0 ht1
  rw [← intrinsicInterior_momentBody_eq_polytope hS ν hν] at hrel
  exact hasDerivAt_responseTheta_path measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hV hrel hM'

omit [MeasurableSingletonClass X] in
/-- **The law along the polytope journey is the maximum-entropy law with the prescribed means**:
the information projection of the mean `m_t`. -/
theorem familyMeasure_polytopeJourney_eq_responseProjection
    (hp : p ∈ intrinsicInterior ℝ hull) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Pfam (polytopeJourney hS ν p t : J → ℝ) = responseProjection hS ν (m₀ + t • (p - m₀)) := by
  have h := polytope_segment_mem hS ν hν hp ht0 ht1
  rw [← intrinsicInterior_momentBody_eq_polytope hS ν hν] at h
  exact (responseProjection_eq_familyMeasure_responseTheta hS ν h).symm

omit [Fintype X] [MeasurableSingletonClass X] hν in
/-- **Feature means agree with the mixture law**: if a data law `D` has mean `p`, the polytope
journey's response law and the mixture `(1−t)ν + tD` have the same feature means — the journey
charts the quotient of the data laws by their means, not the mixtures themselves. -/
theorem meanMap_polytopeJourney_eq_mixLaw (D : Measure X) [IsProbabilityMeasure D]
    (hD : (fun i ↦ ∫ x, S i x ∂D) = p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hmean : mean (polytopeJourney hS ν p t : J → ℝ) = m₀ + t • (p - m₀)) :
    mean (polytopeJourney hS ν p t : J → ℝ) = fun i ↦ ∫ x, S i x ∂mixLaw ν D t := by
  rw [hmean, mean_mixLaw hS ν D ht0 ht1, meanMap_zero_eq_mean ν, hD]

omit [Fintype X] [MeasurableSingletonClass X] hν in
/-- Towards a model mean, the polytope journey is the model journey from the featureless response
(so in the saturated finite case it is the mixture segment, `atomMass_modelJourney_zero`). -/
theorem polytopeJourney_meanMap_eq_modelJourney (θ₁ : 𝕍) (t : ℝ) :
    polytopeJourney hS ν (mean (θ₁ : J → ℝ)) t = modelJourney hS ν 0 θ₁ t := rfl

end Polytope

end Laplace.Multi
