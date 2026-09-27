/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseInformationAction

/-!
# The information action between two model laws

The featureless journey of `ResponseFeaturelessJourney` and its information action
(`ResponseInformationAction`) had the featureless law `ν = P_0` as base point. Here the base point
is an arbitrary model law `P_{θ₀}`: the **model journey** from `θ₀` to `θ₁` is the mean-affine path
`θ_t = m⁻¹((1 − t) m(θ₀) + t m(θ₁))`, again `C^∞` on an open domain containing `[0,1]`, with
velocity `A_{θ_t}⁻¹ Δ`, `Δ = m(θ₁) − m(θ₀)`, and

* `toReal_klDiv_modelJourney_eq_action`: `KL(P_{θ₁} ‖ P_{θ₀}) = ∫₀¹ (1 − t) G_{θ_t}(θ'_t,θ'_t) dt`,
* `toReal_klDiv_modelJourney_eq_action'`: `KL(P_{θ₀} ‖ P_{θ₁}) = ∫₀¹ t G_{θ_t}(θ'_t,θ'_t) dt`,
* `jeffreys_model_eq_action`: the Jeffreys divergence is `∫₀¹ G = −⟨θ₁ − θ₀, m(θ₁) − m(θ₀)⟩`,
* `toReal_klDiv_eq_defect_add_model_action`: for a data law `ρ_g` and any model base point,
  `KL(ρ_g ‖ P_{θ₀}) = KL(ρ_g ‖ P_{Φ(g)}) + ∫₀¹ (1 − t) G_{θ_t}(θ'_t,θ'_t) dt` along the model
  journey from `θ₀` to `Φ(g)`.

This removes the accidental privilege of `θ = 0` from the mathematics while keeping its
interpretive privilege: the information decomposition holds from every model base point.
-/

open MeasureTheory Filter Topology Set InformationTheory intervalIntegral
open scoped ContDiff

namespace Laplace.Multi

section Endpoint

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

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The mean displacement `Δ = m(θ₁) − m(θ₀)` between two model laws lies in the direction
space. -/
theorem meanMap_sub_meanMap_mem (θ₀ θ₁ : 𝕍) :
    mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ) ∈ 𝕍 :=
  sub_mem_dirSpan_of_mem_momentBody' hS ν (meanMap_mem_momentBody measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS _)
    (meanMap_mem_momentBody measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS _)

/-- The mean displacement as a direction. -/
noncomputable def modelDir (θ₀ θ₁ : 𝕍) : 𝕍 :=
  ⟨mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ), meanMap_sub_meanMap_mem hS ν θ₀ θ₁⟩

/-- **The model journey**: `θ_t = θ(m(θ₀) + t (m(θ₁) − m(θ₀)))`. -/
noncomputable def modelJourney (θ₀ θ₁ : 𝕍) (t : ℝ) : 𝕍 :=
  θr (mean (θ₀ : J → ℝ) + t • (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)))

/-- On `[0,1]` the model journey is the featureless journey of the mixture tilt of the two model
tilts. -/
theorem modelJourney_eq_responseOf_mixTilt (θ₀ θ₁ : 𝕍) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    modelJourney hS ν θ₀ θ₁ t =
      responseOf hS ν (mixTilt ν (modelTilt S (θ₀ : J → ℝ)) (modelTilt S (θ₁ : J → ℝ)) t) := by
  unfold modelJourney responseOf
  congr 1
  have e : (fun i ↦ ∫ x, S i x ∂ν.tilted (mixTilt ν (modelTilt S (θ₀ : J → ℝ))
      (modelTilt S (θ₁ : J → ℝ)) t)) =
      tiltedMean S ν (mixTilt ν (modelTilt S (θ₀ : J → ℝ)) (modelTilt S (θ₁ : J → ℝ)) t) := rfl
  rw [e, tiltedMean_mixTilt hS ν (bdd_modelTilt hS _) (bdd_modelTilt hS _) ht0 ht1,
    tiltedMean_modelTilt hS ν, tiltedMean_modelTilt hS ν]
  module

/-- The model journey starts at `θ₀`. -/
theorem modelJourney_zero (θ₀ θ₁ : 𝕍) : modelJourney hS ν θ₀ θ₁ 0 = θ₀ := by
  unfold modelJourney
  rw [zero_smul, add_zero, responseTheta_meanMap hS ν]

/-- The model journey ends at `θ₁`. -/
theorem modelJourney_one (θ₀ θ₁ : 𝕍) : modelJourney hS ν θ₀ θ₁ 1 = θ₁ := by
  unfold modelJourney
  rw [one_smul, add_sub_cancel, responseTheta_meanMap hS ν]

omit [Nonempty J] in
/-- On `[0,1]` the mean segment lies in the interior response domain. -/
theorem model_segment_mem (θ₀ θ₁ : 𝕍) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mean (θ₀ : J → ℝ) + t • (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) ∈ Ω := by
  have h := mean_tilted_mem_intrinsicInterior hS ν
    (bdd_mixTilt ν (bdd_modelTilt hS (θ₀ : J → ℝ)) (bdd_modelTilt hS (θ₁ : J → ℝ)) ht0 ht1)
  have e : (fun i ↦ ∫ x, S i x ∂ν.tilted (mixTilt ν (modelTilt S (θ₀ : J → ℝ))
      (modelTilt S (θ₁ : J → ℝ)) t)) =
      tiltedMean S ν (mixTilt ν (modelTilt S (θ₀ : J → ℝ)) (modelTilt S (θ₁ : J → ℝ)) t) := rfl
  rw [e, tiltedMean_mixTilt hS ν (bdd_modelTilt hS _) (bdd_modelTilt hS _) ht0 ht1,
    tiltedMean_modelTilt hS ν, tiltedMean_modelTilt hS ν] at h
  convert h using 1
  module

variable (S) in
omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **The model journey domain**: the parameters at which the mean segment is an interior
response. -/
def modelJourneyDomain (θ₀ θ₁ : 𝕍) : Set ℝ :=
  {t | mean (θ₀ : J → ℝ) + t • (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) ∈ Ω}

omit [Nonempty J] in
theorem Icc_subset_modelJourneyDomain (θ₀ θ₁ : 𝕍) : Icc (0 : ℝ) 1 ⊆ modelJourneyDomain S ν θ₀ θ₁ :=
  fun _ ht ↦ model_segment_mem hS ν θ₀ θ₁ ht.1 ht.2

/-- The model journey domain is open. -/
theorem isOpen_modelJourneyDomain (θ₀ θ₁ : 𝕍) : IsOpen (modelJourneyDomain S ν θ₀ θ₁) := by
  have e : modelJourneyDomain S ν θ₀ θ₁ =
      (fun t : ℝ ↦ chV θ₀ + t • modelDir hS ν θ₀ θ₁) ⁻¹' Set.range chV := by
    ext t
    simp only [modelJourneyDomain, mem_preimage, mem_range_chartV_iff hS ν, Submodule.coe_add,
      Submodule.coe_smul, chartV_apply, modelDir, Set.mem_ofPred_eq]
    have e2 : mean (0 : J → ℝ) + (mean (θ₀ : J → ℝ) - mean (0 : J → ℝ) +
        t • (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ))) =
        mean (θ₀ : J → ℝ) + t • (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) := by module
    rw [e2]
  rw [e]
  exact (isOpen_range_chartV hS ν).preimage (continuous_const.add (continuous_id.smul
    continuous_const))

/-- **The model journey is mean-affine**: `m(θ_t) = m(θ₀) + t Δ` on its domain. -/
theorem meanMap_modelJourney {θ₀ θ₁ : 𝕍} {t : ℝ} (ht : t ∈ modelJourneyDomain S ν θ₀ θ₁) :
    mean (modelJourney hS ν θ₀ θ₁ t : J → ℝ) =
      mean (θ₀ : J → ℝ) + t • (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) :=
  meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS ht

/-- **The model journey is `C^∞`** on its open domain. -/
theorem contDiffOn_modelJourney (θ₀ θ₁ : 𝕍) :
    ContDiffOn ℝ ∞ (modelJourney hS ν θ₀ θ₁) (modelJourneyDomain S ν θ₀ θ₁) := by
  have e : modelJourney hS ν θ₀ θ₁ =
      (fun z : 𝕍 ↦ θr (mean (0 : J → ℝ) + (z : J → ℝ))) ∘
        fun t : ℝ ↦ chV θ₀ + t • modelDir hS ν θ₀ θ₁ := by
    funext t
    simp only [Function.comp_def, modelJourney, modelDir, Submodule.coe_add, Submodule.coe_smul,
      chartV_apply]
    congr 1
    module
  rw [e]
  refine (contDiffOn_responseTheta_add hS ν).comp
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn fun t ht ↦ ?_
  change mean (0 : J → ℝ) + ((chV θ₀ + t • modelDir hS ν θ₀ θ₁ : 𝕍) : J → ℝ) ∈ Ω
  simp only [Submodule.coe_add, Submodule.coe_smul, chartV_apply, modelDir]
  have e2 : mean (0 : J → ℝ) + (mean (θ₀ : J → ℝ) - mean (0 : J → ℝ) +
      t • (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ))) =
      mean (θ₀ : J → ℝ) + t • (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) := by module
  rw [e2]
  exact ht

/-- The model journey velocity `θ'_t = A_{θ_t}⁻¹ Δ`. -/
noncomputable def modelVel (θ₀ θ₁ : 𝕍) (t : ℝ) : 𝕍 :=
  (CDE (modelJourney hS ν θ₀ θ₁ t)).symm (modelDir hS ν θ₀ θ₁)

theorem chartDeriv_modelVel (θ₀ θ₁ : 𝕍) (t : ℝ) :
    CD (modelJourney hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t) = modelDir hS ν θ₀ θ₁ :=
  chartDeriv_chartDerivEquiv_symm hS ν _ _

/-- **The velocity of the model journey** is the inverse-covariance transport of the mean
velocity. -/
theorem hasDerivAt_modelJourney (θ₀ θ₁ : 𝕍) {t : ℝ} (ht : t ∈ modelJourneyDomain S ν θ₀ θ₁) :
    HasDerivAt (modelJourney hS ν θ₀ θ₁) (modelVel hS ν θ₀ θ₁ t) t := by
  have hU := (isOpen_modelJourneyDomain hS ν θ₀ θ₁).mem_nhds ht
  have hd : HasDerivAt (modelJourney hS ν θ₀ θ₁) (deriv (modelJourney hS ν θ₀ θ₁) t) t :=
    (((contDiffOn_modelJourney hS ν θ₀ θ₁).differentiableOn (by simp)).differentiableAt
      hU).hasDerivAt
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hm := (hasStrictFDerivAt_meanMap measurable_const (integrable_const 1)
    (fun _ ↦ zero_le_one) (one_integral_pos ν) measurable_const h0 hS one_pos
    (modelJourney hS ν θ₀ θ₁ t : J → ℝ)).hasFDerivAt
  have hpath := hm.comp_hasDerivAt t ((𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t hd)
  set Δ := mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ) with hΔ
  have haff : HasDerivAt (fun s : ℝ ↦ mean (θ₀ : J → ℝ) + s • Δ) Δ t := by
    simpa using ((hasDerivAt_id t).smul_const Δ).const_add (mean (θ₀ : J → ℝ))
  have hev : (fun s ↦ mean (modelJourney hS ν θ₀ θ₁ s : J → ℝ)) =ᶠ[𝓝 t]
      fun s ↦ mean (θ₀ : J → ℝ) + s • Δ := by
    filter_upwards [hU] with s hs
    exact meanMap_modelJourney hS ν hs
  have hpath' : HasDerivAt (fun s ↦ mean (modelJourney hS ν θ₀ θ₁ s : J → ℝ))
      (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (modelJourney hS ν θ₀ θ₁ t)
        ((deriv (modelJourney hS ν θ₀ θ₁) t : 𝕍) : J → ℝ)) t := hpath
  have heq := (hpath'.congr_of_eventuallyEq hev.symm).unique haff
  have hV : CD (modelJourney hS ν θ₀ θ₁ t) (deriv (modelJourney hS ν θ₀ θ₁) t) =
      modelDir hS ν θ₀ θ₁ := by
    refine Subtype.ext ?_
    rw [chartDeriv_apply]
    exact heq
  have := congrArg (CDE (modelJourney hS ν θ₀ θ₁ t)).symm hV
  rw [chartDerivEquiv_symm_chartDeriv hS ν] at this
  rw [this] at hd
  exact hd

/-- The natural coordinate along the model journey, coerced. -/
theorem hasDerivAt_modelJourney_coe (θ₀ θ₁ : 𝕍) {t : ℝ} (ht : t ∈ modelJourneyDomain S ν θ₀ θ₁) :
    HasDerivAt (fun s ↦ (modelJourney hS ν θ₀ θ₁ s : J → ℝ)) (modelVel hS ν θ₀ θ₁ t : J → ℝ) t := by
  have h := (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_modelJourney hS ν θ₀ θ₁ ht)
  exact h

/-- The mean map along the model journey has constant derivative `Δ`. -/
theorem hasDerivAt_meanMap_modelJourney (θ₀ θ₁ : 𝕍) {t : ℝ}
    (ht : t ∈ modelJourneyDomain S ν θ₀ θ₁) :
    HasDerivAt (fun s ↦ mean (modelJourney hS ν θ₀ θ₁ s : J → ℝ))
      (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) t := by
  have hU := (isOpen_modelJourneyDomain hS ν θ₀ θ₁).mem_nhds ht
  have haff : HasDerivAt (fun s : ℝ ↦ mean (θ₀ : J → ℝ) +
      s • (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ))) (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) t := by
    simpa using ((hasDerivAt_id t).smul_const (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ))).const_add
      (mean (θ₀ : J → ℝ))
  refine haff.congr_of_eventuallyEq ?_
  filter_upwards [hU] with s hs
  exact meanMap_modelJourney hS ν hs

/-- The Fisher speed of the model journey: `G(θ',θ') = −⟨θ', Δ⟩`. -/
theorem fisherInner_modelVel (θ₀ θ₁ : 𝕍) (t : ℝ) :
    G (modelJourney hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t) =
      -dotJ (modelVel hS ν θ₀ θ₁ t : J → ℝ) (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) := by
  rw [fisherInner_eq_neg_dotJ hS ν, chartDeriv_modelVel hS ν]
  rfl

/-- **The divergence from the base model along the model journey** has derivative
`⟨θ₀ − θ_t, Δ⟩`. -/
theorem hasDerivAt_modelJourneyKL (θ₀ θ₁ : 𝕍) {t : ℝ} (ht : t ∈ modelJourneyDomain S ν θ₀ θ₁) :
    HasDerivAt (fun s ↦ (klDiv (Pfam (modelJourney hS ν θ₀ θ₁ s : J → ℝ))
        (Pfam (θ₀ : J → ℝ))).toReal)
      (dotJ ((θ₀ : J → ℝ) - (modelJourney hS ν θ₀ θ₁ t : J → ℝ))
        (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ))) t := by
  have e : (fun s ↦ (klDiv (Pfam (modelJourney hS ν θ₀ θ₁ s : J → ℝ))
      (Pfam (θ₀ : J → ℝ))).toReal) = fun s ↦
      dotJ ((θ₀ : J → ℝ) - (modelJourney hS ν θ₀ θ₁ s : J → ℝ))
          (mean (modelJourney hS ν θ₀ θ₁ s : J → ℝ)) +
        Real.log (famZ S ν (θ₀ : J → ℝ)) -
          Real.log (famZ S ν (modelJourney hS ν θ₀ θ₁ s : J → ℝ)) :=
    funext fun s ↦ toReal_klDiv_model_model hS ν _ _
  rw [e]
  have h1 := hasDerivAt_dotJ ((hasDerivAt_modelJourney_coe hS ν θ₀ θ₁ ht).const_sub (θ₀ : J → ℝ))
    (hasDerivAt_meanMap_modelJourney hS ν θ₀ θ₁ ht)
  have h2 := ((hasFDerivAt_famZ hS ν (modelJourney hS ν θ₀ θ₁ t : J → ℝ)).log
    (famZ_pos hS ν _).ne').comp_hasDerivAt t (hasDerivAt_modelJourney_coe hS ν θ₀ θ₁ ht)
  refine ((h1.add_const _).sub h2).congr_deriv ?_
  simp only [smul_apply, smul_eq_mul, dotCLM_apply, famMean_eq_meanMap hS ν,
    meanMap_modelJourney hS ν ht]
  have hZ : (famZ S ν (modelJourney hS ν θ₀ θ₁ t : J → ℝ))⁻¹ *
      (-famZ S ν (modelJourney hS ν θ₀ θ₁ t : J → ℝ)) = -1 := by
    rw [mul_neg, inv_mul_cancel₀ (famZ_pos hS ν _).ne']
  rw [← mul_assoc, hZ]
  simp only [dotJ_neg_left, dotJ_sub_left, (isLinearMap_dotJ _).map_add,
    (isLinearMap_dotJ _).map_sub, (isLinearMap_dotJ _).map_smul, smul_eq_mul]
  ring

/-- The moment pairing along the model journey has derivative the Fisher speed:
`d/dt ⟨θ₀ − θ_t, Δ⟩ = G_{θ_t}(θ'_t, θ'_t)`. -/
theorem hasDerivAt_modelJourneyMoment (θ₀ θ₁ : 𝕍) {t : ℝ} (ht : t ∈ modelJourneyDomain S ν θ₀ θ₁) :
    HasDerivAt (fun s ↦ dotJ ((θ₀ : J → ℝ) - (modelJourney hS ν θ₀ θ₁ s : J → ℝ))
        (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)))
      (G (modelJourney hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t)) t := by
  have h := hasDerivAt_dotJ ((hasDerivAt_modelJourney_coe hS ν θ₀ θ₁ ht).const_sub (θ₀ : J → ℝ))
    (hasDerivAt_const t (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)))
  refine h.congr_deriv ?_
  rw [dotJ_zero_right, add_zero, fisherInner_modelVel hS ν, dotJ_neg_left]

/-- The velocity is continuous on the model journey domain. -/
theorem continuousOn_modelVel (θ₀ θ₁ : 𝕍) :
    ContinuousOn (modelVel hS ν θ₀ θ₁) (modelJourneyDomain S ν θ₀ θ₁) := by
  have hγ : ContinuousOn (modelJourney hS ν θ₀ θ₁) (modelJourneyDomain S ν θ₀ θ₁) :=
    (contDiffOn_modelJourney hS ν θ₀ θ₁).continuousOn
  have hR : Continuous fun θ : 𝕍 ↦ ((CDE θ).symm : 𝕍 →L[ℝ] 𝕍) :=
    (contDiff_chartDerivEquiv_symm hS ν).continuous
  exact (hR.comp_continuousOn hγ).clm_apply continuousOn_const

/-- The Fisher speed is continuous on the model journey domain. -/
theorem continuousOn_modelSpeed (θ₀ θ₁ : 𝕍) :
    ContinuousOn (fun t ↦ G (modelJourney hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t)
      (modelVel hS ν θ₀ θ₁ t)) (modelJourneyDomain S ν θ₀ θ₁) := by
  have hγ : ContinuousOn (modelJourney hS ν θ₀ θ₁) (modelJourneyDomain S ν θ₀ θ₁) :=
    (contDiffOn_modelJourney hS ν θ₀ θ₁).continuousOn
  have hv := continuousOn_modelVel hS ν θ₀ θ₁
  have hmap : ContinuousOn (fun t ↦ (modelJourney hS ν θ₀ θ₁ t,
      (modelVel hS ν θ₀ θ₁ t, modelVel hS ν θ₀ θ₁ t))) (modelJourneyDomain S ν θ₀ θ₁) :=
    hγ.prodMk (hv.prodMk hv)
  have h := (continuous_fisherInner hS ν).comp_continuousOn hmap
  simpa only [Function.comp_def] using h

/-- **The information action between two model laws**:
`KL(P_{θ₁} ‖ P_{θ₀}) = ∫₀¹ (1 − t) G_{θ_t}(θ'_t, θ'_t) dt` along the model journey. -/
theorem toReal_klDiv_modelJourney_eq_action (θ₀ θ₁ : 𝕍) :
    (klDiv (Pfam (θ₁ : J → ℝ)) (Pfam (θ₀ : J → ℝ))).toReal =
      ∫ t in (0 : ℝ)..1, (1 - t) * G (modelJourney hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t)
        (modelVel hS ν θ₀ θ₁ t) := by
  set q : ℝ → ℝ := fun s ↦ (klDiv (Pfam (modelJourney hS ν θ₀ θ₁ s : J → ℝ))
    (Pfam (θ₀ : J → ℝ))).toReal with hq
  set p : ℝ → ℝ := fun s ↦ dotJ ((θ₀ : J → ℝ) - (modelJourney hS ν θ₀ θ₁ s : J → ℝ))
    (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) with hp
  set e : ℝ → ℝ := fun t ↦ G (modelJourney hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t)
    (modelVel hS ν θ₀ θ₁ t) with he
  have hsub := Icc_subset_modelJourneyDomain hS ν θ₀ θ₁
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t ↦ (1 - t) * p t + q t) ((1 - t) * e t) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hq' := hasDerivAt_modelJourneyKL hS ν θ₀ θ₁ (hsub ht)
    have hp' := hasDerivAt_modelJourneyMoment hS ν θ₀ θ₁ (hsub ht)
    have h := (((hasDerivAt_id t).const_sub 1).mul hp').add hq'
    refine h.congr_deriv ?_
    simp only [he, id_eq]
    ring
  have hint : IntervalIntegrable (fun t ↦ (1 - t) * e t) volume 0 1 := by
    refine (ContinuousOn.mul (continuous_const.sub continuous_id).continuousOn
      ((continuousOn_modelSpeed hS ν θ₀ θ₁).mono hsub)).intervalIntegrable_of_Icc zero_le_one
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  have hprob := isProbabilityMeasure_family hS ν (θ₀ : J → ℝ)
  have hq0 : q 0 = 0 := by
    simp only [hq, modelJourney_zero hS ν θ₀ θ₁, klDiv_self, ENNReal.toReal_zero]
  have hp0 : p 0 = 0 := by
    simp only [hp, modelJourney_zero hS ν θ₀ θ₁, sub_self, dotJ_zero_left]
  have hq1 : q 1 = (klDiv (Pfam (θ₁ : J → ℝ)) (Pfam (θ₀ : J → ℝ))).toReal := by
    simp only [hq, modelJourney_one hS ν θ₀ θ₁]
  rw [← hq1, hftc]
  simp only [hq0, hp0]
  ring

/-- **The reverse divergence as the weighted Fisher action**:
`KL(P_{θ₀} ‖ P_{θ₁}) = ∫₀¹ t G_{θ_t}(θ'_t, θ'_t) dt` along the model journey. -/
theorem toReal_klDiv_modelJourney_eq_action' (θ₀ θ₁ : 𝕍) :
    (klDiv (Pfam (θ₀ : J → ℝ)) (Pfam (θ₁ : J → ℝ))).toReal =
      ∫ t in (0 : ℝ)..1, t * G (modelJourney hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t)
        (modelVel hS ν θ₀ θ₁ t) := by
  set r : ℝ → ℝ := fun s ↦ (klDiv (Pfam (θ₀ : J → ℝ))
    (Pfam (modelJourney hS ν θ₀ θ₁ s : J → ℝ))).toReal with hr
  set e : ℝ → ℝ := fun t ↦ G (modelJourney hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t)
    (modelVel hS ν θ₀ θ₁ t) with he
  have hsub := Icc_subset_modelJourneyDomain hS ν θ₀ θ₁
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt r (t * e t) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hre : r = fun s ↦ dotJ ((modelJourney hS ν θ₀ θ₁ s : J → ℝ) - (θ₀ : J → ℝ))
        (mean (θ₀ : J → ℝ)) + Real.log (famZ S ν (modelJourney hS ν θ₀ θ₁ s : J → ℝ)) -
        Real.log (famZ S ν (θ₀ : J → ℝ)) :=
      funext fun s ↦ toReal_klDiv_model_model hS ν _ _
    rw [hre]
    have h1 := hasDerivAt_dotJ ((hasDerivAt_modelJourney_coe hS ν θ₀ θ₁ (hsub ht)).sub_const
      (θ₀ : J → ℝ)) (hasDerivAt_const t (mean (θ₀ : J → ℝ)))
    have h2 := ((hasFDerivAt_famZ hS ν (modelJourney hS ν θ₀ θ₁ t : J → ℝ)).log
      (famZ_pos hS ν _).ne').comp_hasDerivAt t (hasDerivAt_modelJourney_coe hS ν θ₀ θ₁ (hsub ht))
    refine ((h1.add h2).sub_const _).congr_deriv ?_
    simp only [smul_apply, smul_eq_mul, dotCLM_apply, famMean_eq_meanMap hS ν,
      meanMap_modelJourney hS ν (hsub ht), dotJ_zero_right, add_zero]
    have hZ : (famZ S ν (modelJourney hS ν θ₀ θ₁ t : J → ℝ))⁻¹ *
        (-famZ S ν (modelJourney hS ν θ₀ θ₁ t : J → ℝ)) = -1 := by
      rw [mul_neg, inv_mul_cancel₀ (famZ_pos hS ν _).ne']
    rw [← mul_assoc, hZ, he]
    simp only
    rw [fisherInner_modelVel hS ν]
    simp only [(isLinearMap_dotJ _).map_add, (isLinearMap_dotJ _).map_sub,
      (isLinearMap_dotJ _).map_smul, smul_eq_mul]
    ring
  have hint : IntervalIntegrable (fun t ↦ t * e t) volume 0 1 :=
    (continuous_id.continuousOn.mul
      ((continuousOn_modelSpeed hS ν θ₀ θ₁).mono hsub)).intervalIntegrable_of_Icc zero_le_one
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  have hprob := isProbabilityMeasure_family hS ν (θ₀ : J → ℝ)
  have hr0 : r 0 = 0 := by
    simp only [hr, modelJourney_zero hS ν θ₀ θ₁, klDiv_self, ENNReal.toReal_zero]
  have hr1 : r 1 = (klDiv (Pfam (θ₀ : J → ℝ)) (Pfam (θ₁ : J → ℝ))).toReal := by
    simp only [hr, modelJourney_one hS ν θ₀ θ₁]
  rw [← hr1, hftc, hr0, sub_zero]

/-- **The Jeffreys divergence between two model laws is the Fisher action of the model journey**,
`= −⟨θ₁ − θ₀, m(θ₁) − m(θ₀)⟩`. -/
theorem jeffreys_model_eq_action (θ₀ θ₁ : 𝕍) :
    (klDiv (Pfam (θ₁ : J → ℝ)) (Pfam (θ₀ : J → ℝ))).toReal +
      (klDiv (Pfam (θ₀ : J → ℝ)) (Pfam (θ₁ : J → ℝ))).toReal =
      ∫ t in (0 : ℝ)..1, G (modelJourney hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t)
        (modelVel hS ν θ₀ θ₁ t) := by
  rw [toReal_klDiv_modelJourney_eq_action hS ν, toReal_klDiv_modelJourney_eq_action' hS ν]
  have hsub := Icc_subset_modelJourneyDomain hS ν θ₀ θ₁
  have hc := (continuousOn_modelSpeed hS ν θ₀ θ₁).mono hsub
  have i1 : IntervalIntegrable (fun t ↦ (1 - t) * G (modelJourney hS ν θ₀ θ₁ t)
      (modelVel hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t)) volume 0 1 :=
    ((continuous_const.sub continuous_id).continuousOn.mul hc).intervalIntegrable_of_Icc
      zero_le_one
  have i2 : IntervalIntegrable (fun t ↦ t * G (modelJourney hS ν θ₀ θ₁ t)
      (modelVel hS ν θ₀ θ₁ t) (modelVel hS ν θ₀ θ₁ t)) volume 0 1 :=
    (continuous_id.continuousOn.mul hc).intervalIntegrable_of_Icc zero_le_one
  rw [← integral_add i1 i2]
  refine integral_congr fun t _ ↦ ?_
  ring

omit [Nonempty J] in
/-- The Jeffreys divergence in closed form: `−⟨θ₁ − θ₀, m(θ₁) − m(θ₀)⟩`. -/
theorem jeffreys_model_eq_neg_dotJ (θ₀ θ₁ : 𝕍) :
    (klDiv (Pfam (θ₁ : J → ℝ)) (Pfam (θ₀ : J → ℝ))).toReal +
      (klDiv (Pfam (θ₀ : J → ℝ)) (Pfam (θ₁ : J → ℝ))).toReal =
      -dotJ ((θ₁ : J → ℝ) - (θ₀ : J → ℝ)) (mean (θ₁ : J → ℝ) - mean (θ₀ : J → ℝ)) := by
  rw [toReal_klDiv_model_model hS ν, toReal_klDiv_model_model hS ν]
  simp only [dotJ_sub_left, (isLinearMap_dotJ _).map_sub]
  ring

/-- **The information decomposition from any model base point**: for a data law `ρ_g`, along the
model journey from `θ₀` to `Φ(g)`,
`KL(ρ_g ‖ P_{θ₀}) = KL(ρ_g ‖ P_{Φ(g)}) + ∫₀¹ (1 − t) G_{θ_t}(θ'_t, θ'_t) dt`. -/
theorem toReal_klDiv_eq_defect_add_model_action {g : X → ℝ} (hg : Bdd g) (θ₀ : 𝕍) :
    (klDiv (ν.tilted g) (Pfam (θ₀ : J → ℝ))).toReal =
      (klDiv (ν.tilted g) (Pfam (responseOf hS ν g : J → ℝ))).toReal +
        ∫ t in (0 : ℝ)..1, (1 - t) * G (modelJourney hS ν θ₀ (responseOf hS ν g) t)
          (modelVel hS ν θ₀ (responseOf hS ν g) t) (modelVel hS ν θ₀ (responseOf hS ν g) t) := by
  rw [toReal_klDiv_pythagoras hS ν hg, toReal_klDiv_modelJourney_eq_action hS ν]

end Endpoint

end Laplace.Multi
