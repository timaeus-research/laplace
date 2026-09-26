/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseTransport
import Laplace.Multi.InvisibleQuadratic
import Laplace.Multi.ResponseAtlas

/-!
# Response transport from the featureless law to every completed response

For a bounded observable `F`, the posterior expectation `M ↦ E_{q_M} F` is continuous on the whole
charged polytope (`continuousOn_integral_responseProjection`): it is the composition of the
continuous linear functional `obsL1` on `L¹` with the continuous density map of the atlas.

Along the straight mean path `M_r = (1 − r) m₀ + r M` from the featureless response
`m₀ = E_ν S` (where `q_{m₀} = ν`) to any `M` of finite rate, the fundamental theorem of calculus
gives, for every `r < 1`,

  `E_{q_{M_r}} F − E_ν F = ∫₀^r lin_{F, M_s}(M − m₀) ds`

(`integral_responseProjection_atlasPath_sub_eq`), where `lin_{F,M}(h) = Cov_{q_M}(F, ⟨C_M⁻¹ h, S⟩)`
is the susceptibility.  On a charged polytope the endpoint is reached by continuity:

  `E_{q_M} F − E_ν F = lim_{r ↑ 1} ∫₀^r lin_{F, M_s}(M − m₀) ds`

(`tendsto_integral_linForm_atlasPath`), an improper accumulated-response identity valid for EVERY
completed response, including those on the boundary faces where the susceptibility may fail to be
integrable up to the endpoint.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Transport

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family `P_θ = exp(−⟨θ,S⟩) ν / Z(θ)`. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The response chart `θ(M)`. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response `m₀ = E_ν S`. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The posterior expectation of a bounded observable is the `L¹` functional of the density. -/
theorem integral_responseProjection_eq_obsL1 {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) {F : X → ℝ}
    (hF : Bdd F) : ∫ x, F x ∂responseProjection hS ν M = obsL1 ν hF (projL1 hS ν M) := by
  rw [obsL1_apply, responseProjection_eq_withDensity_projDens hS ν hfin,
    integral_withDensity_ofReal ν (measurable_projDens hS ν M) (projDens_nonneg hS ν M) F]
  refine integral_congr_ae ((Integrable.coeFn_toL1 (integrable_projDens hS ν M)).mono
    fun x hx ↦ ?_)
  beta_reduce
  have hx' : (projL1 hS ν M) x = projDens hS ν M x := hx
  rw [hx', mul_comm]

/-- **Global continuity of posterior expectations on a charged polytope.** -/
theorem continuousOn_integral_responseProjection (V : Finset (J → ℝ)) [Nonempty V]
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {F : X → ℝ} (hF : Bdd F) :
    ContinuousOn (fun M ↦ ∫ x, F x ∂responseProjection hS ν M)
      (convexHull ℝ (V : Set (J → ℝ))) := by
  have h := (obsL1 ν hF).continuous.comp_continuousOn (continuousOn_projL1_polytope hS ν V hcharged)
  refine h.congr fun M hM ↦ ?_
  exact integral_responseProjection_eq_obsL1 hS ν
    (genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM) hF

/-- **Transport along the straight path before the endpoint**: for every response of finite rate
and every `r < 1`, `E_{q_{M_r}} F − E_ν F = ∫₀^r lin_{F, M_s}(M − m₀) ds`. -/
theorem integral_responseProjection_atlasPath_sub_eq {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {F : X → ℝ} (hF : Bdd F) :
    (∫ x, F x ∂responseProjection hS ν (atlasPath S ν M r)) - ∫ x, F x ∂ν =
      ∫ s in (0 : ℝ)..r, linForm hS ν (atlasPath S ν M s) hF (M - m₀) := by
  have hint : ∀ s ∈ Icc (0 : ℝ) r,
      atlasPath S ν M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := fun s hs ↦
    atlas_mem_intrinsicInterior hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) r, HasDerivAt (fun s ↦ ∫ x, F x ∂(Pfam (θr (atlasPath S ν M s))))
      (linForm hS ν (atlasPath S ν M s) hF (M - m₀)) s := fun s hs ↦ by
    rw [uIcc_of_le hr0] at hs
    exact hasDerivAt_integral_response_path hS ν (atlasPath_sub_mem_dirSpan hS ν hfin) (hint s hs)
      (hasDerivAt_atlasPath ν s) hF
  have hMc : ContinuousOn (atlasPath S ν M) (Icc 0 r) := fun s _ ↦
    (hasDerivAt_atlasPath ν s).continuousAt.continuousWithinAt
  have hcont := continuousOn_linForm_path hS ν (M' := fun _ ↦ M - m₀)
    (atlasPath_sub_mem_dirSpan hS ν hfin) hint hMc continuousOn_const
    (fun _ _ ↦ sub_mem_dirSpan_of_genRate_ne_top hS ν hfin) hF
  have hcont' : ContinuousOn (fun s ↦ linForm hS ν (atlasPath S ν M s) hF (M - m₀)) (uIcc 0 r) := by
    rwa [uIcc_of_le hr0]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont'.intervalIntegrable,
    ← responseProjection_eq_familyMeasure_responseTheta hS ν
      (hint r ⟨hr0, le_rfl⟩), atlasPath_zero,
    familyMeasure_responseTheta_featureless hS ν]

/-- The straight path stays in the polytope. -/
theorem atlasPath_mem_convexHull (V : Finset (J → ℝ))
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ))) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    atlasPath S ν M r ∈ convexHull ℝ (V : Set (J → ℝ)) := by
  have hm₀ : m₀ ∈ convexHull ℝ (V : Set (J → ℝ)) := by
    rw [← hpoly]
    exact meanMap_mem_momentBody measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS 0
  have := (convex_convexHull ℝ (V : Set (J → ℝ))).add_smul_sub_mem hm₀ hM hr
  convert this using 1
  rw [atlasPath]
  module

/-- **The accumulated response from the featureless law to every completed response**: on a
charged polytope, for every `M ∈ P` and every bounded `F`,
`E_{q_M} F − E_ν F = lim_{r ↑ 1} ∫₀^r lin_{F, M_s}(M − m₀) ds`. -/
theorem tendsto_integral_linForm_atlasPath (V : Finset (J → ℝ)) [Nonempty V]
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) {F : X → ℝ} (hF : Bdd F) :
    Tendsto (fun r : ℝ ↦ ∫ s in (0 : ℝ)..r, linForm hS ν (atlasPath S ν M s) hF (M - m₀))
      (𝓝[<] 1) (𝓝 ((∫ x, F x ∂responseProjection hS ν M) - ∫ x, F x ∂ν)) := by
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have hpath : ContinuousOn (fun r ↦ ∫ x, F x ∂responseProjection hS ν (atlasPath S ν M r))
      (Icc 0 1) :=
    (continuousOn_integral_responseProjection hS ν V hcharged hF).comp
      (fun r _ ↦ (hasDerivAt_atlasPath ν r).continuousAt.continuousWithinAt)
      (fun r hr ↦ atlasPath_mem_convexHull hS ν V hpoly hM hr)
  have hlim : Tendsto (fun r ↦ (∫ x, F x ∂responseProjection hS ν (atlasPath S ν M r)) -
      ∫ x, F x ∂ν) (𝓝[<] 1) (𝓝 ((∫ x, F x ∂responseProjection hS ν M) - ∫ x, F x ∂ν)) := by
    have h1 := (hpath 1 (right_mem_Icc.2 zero_le_one)).tendsto
    rw [atlasPath_one] at h1
    refine (h1.mono_left ?_).sub_const _
    rw [← nhdsWithin_Ioo_eq_nhdsLT zero_lt_one]
    exact nhdsWithin_mono _ Ioo_subset_Icc_self
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  exact integral_responseProjection_atlasPath_sub_eq hS ν hfin hr.1.le hr.2 hF

end Transport

end Laplace.Multi
