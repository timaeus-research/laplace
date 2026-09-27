/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CanonicalDataJourney
import Laplace.Multi.ResponseLocalMetricControl
import Laplace.Multi.ExtremeMeanSupport

/-!
# The mixture journey and its response

The mixture segment `D_t = (1 − t) ν + t D` from the featureless law to a data law `D ≪ ν` has
mean `m_t = m_ν + t (m_D − m_ν)` (`mean_mixLaw`): its response depends only on the endpoint means,
`Φ(D_t) = θ(m_ν + t (m_D − m_ν))` (`mixResponse`, `mixResponse_eq`), in contrast with the
exponential journey, which can see features of `D` invisible to its mean.

* **Endpoints** (`mixResponse_zero`, `mixResponse_one`): `Φ(D_0) = 0`, `Φ(D_1) = θ(m_D)`.
* **Interior segment** (`mem_intrinsicInterior_segment`): between two relative-interior means the
  whole segment is relative-interior, so the response chart is defined along the journey.
* **Velocity** (`hasDerivAt_mixResponse`): `Φ(D_t)' = (Dm(Φ(D_t))|_W)⁻¹ (m_D − m_ν)` for
  `t ∈ [0, 1]`.
* **Length** (`fisherDist_mixResponse_le`):
  `d_F(0, θ(m_D)) ≤ ∫_0^1 |(Dm(θ_t)|_W)⁻¹ (m_D − m_ν)|_{F,θ_t} dt`, through the smooth clamp
  reparametrisation of the segment and a change of variables.

No ordering between the exponential and mixture response lengths is claimed.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Segment

variable {J : Type*} [Fintype J]

set_option linter.unusedFintypeInType false in
/-- **A segment between two relative-interior points is relative-interior.** -/
theorem mem_intrinsicInterior_segment {K : Set (J → ℝ)} (hK : Convex ℝ K) {a b : J → ℝ}
    (ha : a ∈ intrinsicInterior ℝ K) (hb : b ∈ intrinsicInterior ℝ K) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : a + t • (b - a) ∈ intrinsicInterior ℝ K := by
  rw [mem_intrinsicInterior_iff_forall_supporting hK] at ha hb ⊢
  have hmem : a + t • (b - a) ∈ K :=
    hK.add_smul_mem ha.1 (by rw [add_sub_cancel]; exact hb.1) ⟨ht0, ht1⟩
  refine ⟨hmem, fun e he y hy ↦ ?_⟩
  have hlin : dotJ e (a + t • (b - a)) = dotJ e a + t * (dotJ e b - dotJ e a) := by
    rw [(isLinearMap_dotJ e).map_add, (isLinearMap_dotJ e).map_smul,
      (isLinearMap_dotJ e).map_sub, smul_eq_mul]
  have hea := he a ha.1
  have heb := he b hb.1
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at he hmem ⊢
    exact ha.2 e he y hy
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hb' : dotJ e b = dotJ e (a + t • (b - a)) := by
      rw [hlin] at hea heb ⊢
      nlinarith
    have hmax : ∀ y' ∈ K, dotJ e y' ≤ dotJ e b := fun y' hy' ↦ (he y' hy').trans hb'.ge
    rw [← hb']
    exact hb.2 e hmax y hy

end Segment

section Mixture

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless mean. -/
local notation "mν" => (fun i ↦ ∫ x, S i x ∂ν : J → ℝ)

/-- The data mean. -/
local notation "mD" => (fun i ↦ ∫ x, S i x ∂D : J → ℝ)

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
variable (t : ℝ) in
/-- The mixture law `D_t = (1 − t) ν + t D`. -/
noncomputable def mixLaw : Measure X := ENNReal.ofReal (1 - t) • ν + ENNReal.ofReal t • D

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
theorem isProbabilityMeasure_mixLaw {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (mixLaw ν D t) := by
  refine ⟨?_⟩
  rw [mixLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add (sub_nonneg.2 ht1) ht0]
  simp

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- Integrals against the mixture law. -/
theorem integral_mixLaw {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {f : X → ℝ} (hf : Bdd f) :
    ∫ x, f x ∂mixLaw ν D t = (1 - t) * ∫ x, f x ∂ν + t * ∫ x, f x ∂D := by
  rw [mixLaw, integral_add_measure ((integrable_of_bdd_prob ν hf).smul_measure
    ENNReal.ofReal_ne_top) ((integrable_of_bdd_prob D hf).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (sub_nonneg.2 ht1),
    ENNReal.toReal_ofReal ht0, smul_eq_mul, smul_eq_mul]

omit [Nonempty X] [Fintype J] [Nonempty J] in
/-- **The mean of the mixture is the mean segment**: `m_t = m_ν + t (m_D − m_ν)`. -/
theorem mean_mixLaw {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun i ↦ ∫ x, S i x ∂mixLaw ν D t) = mν + t • (mD - mν) := by
  funext i
  rw [integral_mixLaw ν D ht0 ht1 (hS i), Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

variable (hDν : D ≪ ν)
include hDν

set_option linter.unusedFintypeInType false in
theorem mean_sub_mean_mem_dirSpan : mD - mν ∈ 𝕍 :=
  sub_mem_dirSpan_of_mem_momentBody' hS ν (mean_mem_momentBody_of_ac hS ν ν
    Measure.AbsolutelyContinuous.rfl) (mean_mem_momentBody_of_ac hS ν D hDν)

omit hDν in
/-- **The mixture response** `Φ(D_t) = θ(m_ν + t (m_D − m_ν))`. -/
noncomputable def mixResponse (t : ℝ) : 𝕍 := θr (mν + t • (mD - mν))

omit hDν in
/-- The mixture response is the response of the mixture law. -/
theorem mixResponse_eq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mixResponse hS ν D t = θr (fun i ↦ ∫ x, S i x ∂mixLaw ν D t) := by
  rw [mixResponse, mean_mixLaw hS ν D ht0 ht1]

omit [IsProbabilityMeasure D] hDν in
/-- **The mixture journey starts at the featureless response.** -/
theorem mixResponse_zero : mixResponse hS ν D 0 = 0 := by
  have hh : Bdd (logDens fun _ : X ↦ (1 : ℝ)) := ⟨measurable_const, 0, fun _ ↦ by simp [logDens]⟩
  have h := journeyResponse_zero hS ν hh
  rw [responseOf, tilted_zero_mul] at h
  rw [mixResponse, zero_smul, add_zero]
  exact h

omit [IsProbabilityMeasure D] hDν in
/-- **The mixture journey ends at the response of the data law.** -/
theorem mixResponse_one : mixResponse hS ν D 1 = θr mD := by
  rw [mixResponse, one_smul, add_sub_cancel]

variable (hrel : (fun i ↦ ∫ x, S i x ∂D : J → ℝ) ∈
  intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

omit [IsProbabilityMeasure D] hDν in
set_option linter.unusedFintypeInType false in
/-- The mean segment stays relative-interior. -/
theorem mean_segment_mem_intrinsicInterior {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mν + t • (mD - mν) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  have h0 := featureless_mem_intrinsicInterior hS ν
  rw [meanMap_zero_eq_mean ν] at h0
  exact mem_intrinsicInterior_segment (convex_momentBody S) h0 hrel ht0 ht1

/-- **The velocity of the mixture response**: `Φ(D_t)' = (Dm(Φ(D_t))|_W)⁻¹ (m_D − m_ν)`. -/
theorem hasDerivAt_mixResponse {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasDerivAt (mixResponse hS ν D)
      ((CDE (mixResponse hS ν D t)).symm ⟨mD - mν, mean_sub_mean_mem_dirSpan hS ν D hDν⟩) t := by
  have hV : ∀ s : ℝ, (mν + s • (mD - mν)) - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈
      𝕍 := fun s ↦ by
    rw [meanMap_zero_eq_mean ν, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (mean_sub_mean_mem_dirSpan hS ν D hDν)
  have hM' : HasDerivAt (fun s : ℝ ↦ mν + s • (mD - mν)) (mD - mν) t := by
    simpa using ((hasDerivAt_id t).smul_const (mD - mν)).const_add mν
  exact hasDerivAt_responseTheta_path measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hV (mean_segment_mem_intrinsicInterior hS ν D hrel ht0 ht1) hM'

/-- **The length bound for the mixture journey**:
`d_F(0, θ(m_D)) ≤ ∫_0^1 |(Dm(Φ(D_t))|_W)⁻¹ (m_D − m_ν)|_{F, Φ(D_t)} dt`. -/
theorem fisherDist_mixResponse_le :
    fisherDist S ν (mixResponse hS ν D 0) (mixResponse hS ν D 1) ≤
      ∫ s in (0 : ℝ)..1, fisherNorm S ν (mixResponse hS ν D s : J → ℝ)
        ((CDE (mixResponse hS ν D s)).symm ⟨mD - mν, mean_sub_mean_mem_dirSpan hS ν D hDν⟩ :
          J → ℝ) := by
  obtain ⟨v, hvdef⟩ : ∃ v : 𝕍, v = ⟨mD - mν, mean_sub_mean_mem_dirSpan hS ν D hDν⟩ := ⟨_, rfl⟩
  -- the clamp-reparametrised mean segment
  obtain ⟨Mt, hMt⟩ : ∃ Mt : ℝ → J → ℝ, Mt = fun s ↦ mν + clampStep s • (mD - mν) := ⟨_, rfl⟩
  have hMtV : ∀ s, Mt s - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈ 𝕍 := fun s ↦ by
    rw [hMt, meanMap_zero_eq_mean ν, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (mean_sub_mean_mem_dirSpan hS ν D hDν)
  have hMtint : ∀ s, Mt s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := fun s ↦ by
    rw [hMt]
    exact mean_segment_mem_intrinsicInterior hS ν D hrel (clampStep_mem_Icc s).1
      (clampStep_mem_Icc s).2
  have hMtc : Continuous Mt := by
    rw [hMt]
    exact continuous_const.add ((continuous_smoothStep.comp continuous_clampArg).smul
      continuous_const)
  have hθc : Continuous fun s ↦ θr (Mt s) := by
    rw [← continuousOn_univ]
    exact continuousOn_responseTheta_path hS ν hMtV (fun s _ ↦ hMtint s) hMtc.continuousOn
  have hMt' : ∀ s, HasDerivAt Mt (clampStepDeriv s • (mD - mν)) s := fun s ↦ by
    rw [hMt]
    simpa using ((hasDerivAt_clampStep s).smul_const (mD - mν)).const_add mν
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ → 𝕍, η' = fun s ↦ clampStepDeriv s • (CDE (θr (Mt s))).symm v :=
    ⟨_, rfl⟩
  have hd : ∀ s, HasDerivAt (fun s ↦ θr (Mt s)) (η' s) s := fun s ↦ by
    have h := hasDerivAt_responseTheta_path measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hMtV (hMtint s) (hMt' s)
    refine h.congr_deriv ?_
    rw [hη', hvdef]
    beta_reduce
    rw [← map_smul]
    rfl
  have hd' : Continuous η' := by
    rw [hη']
    exact continuous_clampStepDeriv.smul
      (((continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS).comp hθc).clm_apply continuous_const)
  have hle := fisherDist_le_integral hS ν (η := fun s ↦ (θr (Mt s) : J → ℝ))
    (η' := fun s ↦ (η' s : J → ℝ)) (fun s ↦ (θr (Mt s)).2)
    (fun s ↦ (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt s (hd s))
    (continuous_subtype_val.comp hd') zero_le_one
  have h0 : θr (Mt 0) = mixResponse hS ν D 0 := by rw [hMt, mixResponse]; simp [clampStep_zero]
  have h1 : θr (Mt 1) = mixResponse hS ν D 1 := by rw [hMt, mixResponse]; simp [clampStep_one]
  have e0 : (⟨(θr (Mt 0) : J → ℝ), (θr (Mt 0)).2⟩ : 𝕍) = mixResponse hS ν D 0 := by rw [← h0]
  have e1 : (⟨(θr (Mt 1) : J → ℝ), (θr (Mt 1)).2⟩ : 𝕍) = mixResponse hS ν D 1 := by rw [← h1]
  rw [e0, e1] at hle
  refine hle.trans (le_of_eq ?_)
  -- the speed along the clamp path is the clamp derivative times the speed along the segment
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun u ↦ fisherNorm S ν (mixResponse hS ν D u : J → ℝ)
      ((CDE (mixResponse hS ν D u)).symm v : J → ℝ) := ⟨_, rfl⟩
  have hspeed : ∀ s, fisherNorm S ν (θr (Mt s) : J → ℝ) (η' s : J → ℝ) =
      (g ∘ clampStep) s * clampStepDeriv s := fun s ↦ by
    rw [hη', hg, Function.comp_apply, mixResponse, hMt]
    simp only [Submodule.coe_smul, fisherNorm_smul hS ν, abs_of_nonneg (clampStepDeriv_nonneg s)]
    ring
  simp only [hspeed]
  rw [intervalIntegral.integral_comp_mul_deriv' (fun s _ ↦ hasDerivAt_clampStep s)
    continuous_clampStepDeriv.continuousOn, clampStep_zero, clampStep_one]
  · rw [hg, hvdef]
  · rw [hg]
    have hcont : ContinuousOn (fun u ↦ mixResponse hS ν D u) (Icc 0 1) := by
      have hV : ∀ s : ℝ, (mν + s • (mD - mν)) -
          meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈ 𝕍 := fun s ↦ by
        rw [meanMap_zero_eq_mean ν, add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (mean_sub_mean_mem_dirSpan hS ν D hDν)
      exact continuousOn_responseTheta_path hS ν hV
        (fun s hs ↦ mean_segment_mem_intrinsicInterior hS ν D hrel hs.1 hs.2)
        (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    refine ContinuousOn.mono (s := Icc (0 : ℝ) 1) ?_ fun u hu ↦ ?_
    swap
    · obtain ⟨s, -, rfl⟩ := hu
      exact clampStep_mem_Icc s
    have h1 : ContinuousOn (fun u ↦ (mixResponse hS ν D u : J → ℝ)) (Icc 0 1) :=
      continuous_subtype_val.comp_continuousOn hcont
    have h2 : ContinuousOn (fun u ↦ ((CDE (mixResponse hS ν D u)).symm v : J → ℝ)) (Icc 0 1) :=
      continuous_subtype_val.comp_continuousOn
        ((((continuous_chartDerivEquiv_symm measurable_const (integrable_const 1)
          (fun _ ↦ one_pos) (one_integral_pos ν) hS).comp_continuousOn hcont).clm_apply
          continuousOn_const))
    change ContinuousOn (fun u ↦ (fun p : (J → ℝ) × (J → ℝ) ↦ fisherNorm S ν p.1 p.2)
      ((mixResponse hS ν D u : J → ℝ), ((CDE (mixResponse hS ν D u)).symm v : J → ℝ))) (Icc 0 1)
    exact (continuous_fisherNorm hS ν).comp_continuousOn (h1.prodMk h2)

end Mixture

end Laplace.Multi
