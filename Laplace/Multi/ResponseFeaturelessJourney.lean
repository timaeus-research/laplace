/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseInformationPythagoras
import Laplace.Multi.ResponseFisherCurvature
import Laplace.Multi.SmoothChart

/-!
# The featureless-to-data journey and its response

The **featureless journey** from the reference law `ν` to a data law `ρ_g` is the mixture
`ρ_t = (1 − t) ν + t ρ_g`. Its response is the straight segment in mean coordinates,
`θ_t = θ(m₀ + t Δ)` with `Δ = E_{ρ_g}S − m₀` (`featurelessJourney`,
`featurelessJourney_eq_responseOf_mixTilt`, `meanMap_featurelessJourney`), starting at the
featureless response `0` and ending at `Φ(g)` (`featurelessJourney_zero`, `featurelessJourney_one`).
It is `C^∞` on an open neighbourhood of `[0,1]` in the natural chart (`journeyDomain`,
`contDiffOn_featurelessJourney`), its velocity is the inverse-covariance transport of the constant
mean velocity, `θ'_t = A_{θ_t}⁻¹ Δ` (`hasDerivAt_featurelessJourney`), and it is a global
**m-geodesic**: `θ''_t + C_{θ_t}(θ'_t, θ'_t) = 0` (`hasDerivAt_journeyVel`,
`featurelessJourney_mGeodesic`), with Christoffel coefficient one, as for every mean-affine path.
This is the canonical response journey "from the featureless law to the data": straight in the
mean chart, curved in the natural chart by the third cumulants of the family.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Journey

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The intrinsic chart. -/
local notation "chV" => chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

omit [Nonempty J] in
/-- The tilted mean of the zero tilt is the featureless response. -/
theorem tiltedMean_zero_tilt : tiltedMean S ν (fun _ : X ↦ (0 : ℝ)) = m₀ := by
  funext j
  have h := congrFun (mean_familyMeasure_one_zero hS ν 0) j
  rw [familyMeasure_zero_eq hS ν] at h
  rw [← h]
  unfold tiltedMean
  simp

/-- The mean displacement `Δ = E_{ρ_g} S − m₀` lies in the direction space. -/
theorem tiltedMean_sub_featureless_mem {g : X → ℝ} (hg : Bdd g) : tiltedMean S ν g - m₀ ∈ 𝕍 :=
  sub_mem_dirSpan_of_mem_momentBody' hS ν (meanMap_mem_momentBody measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS 0)
    (intrinsicInterior_subset (mean_tilted_mem_intrinsicInterior hS ν hg))

/-- The mean displacement as a direction. -/
noncomputable def journeyDir {g : X → ℝ} (hg : Bdd g) : 𝕍 :=
  ⟨tiltedMean S ν g - m₀, tiltedMean_sub_featureless_mem hS ν hg⟩

/-- **The featureless journey's response**: `θ_t = θ(m₀ + t (E_{ρ_g}S − m₀))`. -/
noncomputable def featurelessJourney (g : X → ℝ) (t : ℝ) : 𝕍 :=
  θr (m₀ + t • (tiltedMean S ν g - m₀))

/-- On `[0,1]` the journey is the response of the mixture tilt `log((1 − t) + t p_g)`. -/
theorem featurelessJourney_eq_responseOf_mixTilt {g : X → ℝ} (hg : Bdd g) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    featurelessJourney hS ν g t = responseOf hS ν (mixTilt ν (fun _ ↦ (0 : ℝ)) g t) := by
  unfold featurelessJourney responseOf
  congr 1
  have e : (fun i ↦ ∫ x, S i x ∂ν.tilted (mixTilt ν (fun _ ↦ (0 : ℝ)) g t)) =
      tiltedMean S ν (mixTilt ν (fun _ ↦ (0 : ℝ)) g t) := rfl
  rw [e, tiltedMean_mixTilt hS ν (Bdd.const 0) hg ht0 ht1, tiltedMean_zero_tilt hS ν]
  module

/-- On `[0,1]` the journey is the response of the mixture data law `(1 − t) ν + t ρ_g`. -/
theorem featurelessJourney_eq_lawResponse {g : X → ℝ} (hg : Bdd g) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    featurelessJourney hS ν g t =
      lawResponse hS ν (toDataLaw ν (mixTilt ν (fun _ ↦ (0 : ℝ)) g t)
        (bdd_mixTilt ν (Bdd.const 0) hg ht0 ht1)) := by
  rw [lawResponse_toDataLaw hS ν, featurelessJourney_eq_responseOf_mixTilt hS ν hg ht0 ht1]

/-- The journey starts at the featureless response. -/
theorem featurelessJourney_zero (g : X → ℝ) : featurelessJourney hS ν g 0 = 0 := by
  unfold featurelessJourney
  rw [zero_smul, add_zero]
  have h := responseTheta_meanMap hS ν (0 : 𝕍)
  rwa [Submodule.coe_zero] at h

/-- The journey ends at the response of the data law. -/
theorem featurelessJourney_one (g : X → ℝ) : featurelessJourney hS ν g 1 = responseOf hS ν g := by
  unfold featurelessJourney
  rw [one_smul, add_sub_cancel]
  rfl

omit [Nonempty J] in
/-- On `[0,1]` the mean segment lies in the interior response domain. -/
theorem featureless_segment_mem {g : X → ℝ} (hg : Bdd g) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    m₀ + t • (tiltedMean S ν g - m₀) ∈ Ω := by
  have h := mean_tilted_mem_intrinsicInterior hS ν (bdd_mixTilt ν (Bdd.const 0) hg ht0 ht1)
  have e : (fun i ↦ ∫ x, S i x ∂ν.tilted (mixTilt ν (fun _ ↦ (0 : ℝ)) g t)) =
      tiltedMean S ν (mixTilt ν (fun _ ↦ (0 : ℝ)) g t) := rfl
  rw [e, tiltedMean_mixTilt hS ν (Bdd.const 0) hg ht0 ht1, tiltedMean_zero_tilt hS ν] at h
  convert h using 1
  module

variable (S) in
omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **The journey domain**: the parameters at which the mean segment is an interior response. -/
def journeyDomain (g : X → ℝ) : Set ℝ := {t | m₀ + t • (tiltedMean S ν g - m₀) ∈ Ω}

omit [Nonempty J] in
theorem Icc_subset_journeyDomain {g : X → ℝ} (hg : Bdd g) : Icc (0 : ℝ) 1 ⊆ journeyDomain S ν g :=
  fun _ ht ↦ featureless_segment_mem hS ν hg ht.1 ht.2

/-- The journey domain is open. -/
theorem isOpen_journeyDomain {g : X → ℝ} (hg : Bdd g) : IsOpen (journeyDomain S ν g) := by
  have e : journeyDomain S ν g = (fun t : ℝ ↦ t • journeyDir hS ν hg) ⁻¹' Set.range chV := by
    ext t
    simp only [journeyDomain, mem_preimage, mem_range_chartV_iff hS ν, Submodule.coe_smul]
    rfl
  rw [e]
  exact (isOpen_range_chartV hS ν).preimage (continuous_id.smul continuous_const)

/-- **The journey is mean-affine**: `m(θ_t) = m₀ + t Δ` on the journey domain. -/
theorem meanMap_featurelessJourney {g : X → ℝ} {t : ℝ} (ht : t ∈ journeyDomain S ν g) :
    mean (featurelessJourney hS ν g t) = m₀ + t • (tiltedMean S ν g - m₀) :=
  meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS ht

/-- **The journey is `C^∞`** on its (open) domain in the natural chart. -/
theorem contDiffOn_featurelessJourney {g : X → ℝ} (hg : Bdd g) :
    ContDiffOn ℝ ∞ (featurelessJourney hS ν g) (journeyDomain S ν g) := by
  have e : featurelessJourney hS ν g =
      (fun z : 𝕍 ↦ θr (m₀ + (z : J → ℝ))) ∘ fun t : ℝ ↦ t • journeyDir hS ν hg := by
    funext t
    simp only [Function.comp_def, featurelessJourney, journeyDir, Submodule.coe_smul]
  rw [e]
  refine (contDiffOn_responseTheta_add hS ν).comp (contDiff_id.smul contDiff_const).contDiffOn
    fun t ht ↦ ?_
  change m₀ + ((t • journeyDir hS ν hg : 𝕍) : J → ℝ) ∈ Ω
  rw [Submodule.coe_smul]
  exact ht

/-- The journey velocity `θ'_t = A_{θ_t}⁻¹ Δ`. -/
noncomputable def journeyVel {g : X → ℝ} (hg : Bdd g) (t : ℝ) : 𝕍 :=
  (CDE (featurelessJourney hS ν g t)).symm (journeyDir hS ν hg)

/-- The chart derivative of the velocity is the mean displacement: `A_{θ_t} θ'_t = Δ`. -/
theorem chartDeriv_journeyVel {g : X → ℝ} (hg : Bdd g) (t : ℝ) :
    CD (featurelessJourney hS ν g t) (journeyVel hS ν hg t) = journeyDir hS ν hg :=
  chartDeriv_chartDerivEquiv_symm hS ν _ _

/-- **The velocity of the featureless journey** is the inverse-covariance transport of the mean
velocity: `HasDerivAt θ (A_{θ_t}⁻¹ Δ) t` on the journey domain. -/
theorem hasDerivAt_featurelessJourney {g : X → ℝ} (hg : Bdd g) {t : ℝ}
    (ht : t ∈ journeyDomain S ν g) :
    HasDerivAt (featurelessJourney hS ν g) (journeyVel hS ν hg t) t := by
  have hU := (isOpen_journeyDomain hS ν hg).mem_nhds ht
  have hd : HasDerivAt (featurelessJourney hS ν g) (deriv (featurelessJourney hS ν g) t) t :=
    (((contDiffOn_featurelessJourney hS ν hg).differentiableOn (by simp)).differentiableAt
      hU).hasDerivAt
  -- differentiate the mean-affine identity
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hm := (hasStrictFDerivAt_meanMap measurable_const (integrable_const 1)
    (fun _ ↦ zero_le_one) (one_integral_pos ν) measurable_const h0 hS one_pos
    (featurelessJourney hS ν g t : J → ℝ)).hasFDerivAt
  have hpath := hm.comp_hasDerivAt t
    ((𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t hd)
  have haff : HasDerivAt (fun s : ℝ ↦ m₀ + s • (tiltedMean S ν g - m₀))
      (tiltedMean S ν g - m₀) t := by
    simpa using ((hasDerivAt_id t).smul_const (tiltedMean S ν g - m₀)).const_add m₀
  have hev : (fun s ↦ mean (featurelessJourney hS ν g s : J → ℝ)) =ᶠ[𝓝 t]
      fun s ↦ m₀ + s • (tiltedMean S ν g - m₀) := by
    filter_upwards [hU] with s hs
    exact meanMap_featurelessJourney hS ν hs
  have hpath' : HasDerivAt (fun s ↦ mean (featurelessJourney hS ν g s : J → ℝ))
      (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (featurelessJourney hS ν g t)
        ((deriv (featurelessJourney hS ν g) t : 𝕍) : J → ℝ)) t := hpath
  have heq := (hpath'.congr_of_eventuallyEq hev.symm).unique haff
  -- `A θ' = Δ` in the direction space, hence `θ' = A⁻¹ Δ`
  have hV : CD (featurelessJourney hS ν g t) (deriv (featurelessJourney hS ν g) t) =
      journeyDir hS ν hg := by
    refine Subtype.ext ?_
    rw [chartDeriv_apply]
    exact heq
  have := congrArg (CDE (featurelessJourney hS ν g t)).symm hV
  rw [chartDerivEquiv_symm_chartDeriv hS ν] at this
  rw [this] at hd
  exact hd

/-- **The featureless journey is an m-geodesic**: `θ''_t = −C_{θ_t}(θ'_t, θ'_t)` on the journey
domain. -/
theorem hasDerivAt_journeyVel {g : X → ℝ} (hg : Bdd g) {t : ℝ} (ht : t ∈ journeyDomain S ν g) :
    HasDerivAt (journeyVel hS ν hg)
      (-mChristoffel hS ν (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
        (journeyVel hS ν hg t)) t := by
  have h0 := (hasFDerivAt_inverse_natural hS ν (featurelessJourney hS ν g t)).comp_hasDerivAt t
    (hasDerivAt_featurelessJourney hS ν hg ht)
  have h1 : HasDerivAt (fun s ↦ (ContinuousLinearEquiv.symm (CDE (featurelessJourney hS ν g s)) :
      𝕍 →L[ℝ] 𝕍))
      ((-ContinuousLinearMap.mulLeftRight ℝ _
        (ContinuousLinearEquiv.symm (CDE (featurelessJourney hS ν g t)) : 𝕍 →L[ℝ] 𝕍)
        (ContinuousLinearEquiv.symm (CDE (featurelessJourney hS ν g t)) : 𝕍 →L[ℝ] 𝕍))
          (thirdOp hS ν (featurelessJourney hS ν g t) (journeyVel hS ν hg t))) t := h0
  have h2 := h1.clm_apply (hasDerivAt_const t (journeyDir hS ν hg))
  refine h2.congr_deriv ?_
  simp only [map_zero, add_zero]
  rfl

/-- The m-geodesic equation of the featureless journey, `θ'' + C(θ',θ') = 0`. -/
theorem featurelessJourney_mGeodesic {g : X → ℝ} (hg : Bdd g) {t : ℝ}
    (ht : t ∈ journeyDomain S ν g) :
    deriv (journeyVel hS ν hg) t + mChristoffel hS ν (featurelessJourney hS ν g t)
      (journeyVel hS ν hg t) (journeyVel hS ν hg t) = 0 := by
  rw [(hasDerivAt_journeyVel hS ν hg ht).deriv, neg_add_cancel]

end Journey

end Laplace.Multi
