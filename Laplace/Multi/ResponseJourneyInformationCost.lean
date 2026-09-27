/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseBoundaryJourney
import Laplace.Multi.ResponseEndpointInformationAction

/-!
# The information budget of the journey to any data law

Along the response journey `θ_t = m⁻¹(m_ν + t(m_D − m_ν))` towards **any** data law `D` on a
finite space with charged atoms (`ResponseBoundaryJourney`), the acquired information is an exact
Fisher action, up to and including the boundary:

* interior cutoff (`toReal_klDiv_polytopeJourney_eq_action`): for `T < 1`,
  `KL(P_{θ_T}‖ν) = ∫₀^T (T − t) G_{θ_t}(θ̇_t, θ̇_t) dt`, the model-journey action of
  `ResponseEndpointInformationAction` reparametrised to the cutoff;
* the squeeze (`tendsto_journeyAction`): the truncated budgets `∫₀^T (1 − t) G dt` are trapped
  between `KL(P_{θ_T}‖ν)` and `KL(R_D‖ν)` and converge to the latter;
* **the boundary information budget** (`integrableOn_journeyEnergy`, `integral_journeyEnergy`):
  the weighted Fisher energy `(1 − t) G_{θ_t}(θ̇_t, θ̇_t)` is Lebesgue integrable on `(0, 1]` and

  `KL(R_D‖ν) = ∫₀¹ (1 − t) G_{θ_t}(θ̇_t, θ̇_t) dt`;

* **the flagship budget** (`journey_information_budget`):
  `KL(D‖ν) = KL(D‖R_D) + ∫₀¹ (1 − t) G_{θ_t}(θ̇_t, θ̇_t) dt` — the information invisible to the
  features plus the Fisher action of the journey from the featureless law to the data's entropy
  response, for every data law, with no interior-mean hypothesis.
-/

open MeasureTheory InformationTheory Filter Topology Set

namespace Laplace.Multi

section Cutoff

/-- The cutoffs `1 − 1/(k+2)` converge to `1` from below. -/
theorem tendsto_cutoff : Tendsto (fun k : ℕ ↦ (1 : ℝ) - 1 / (k + 2)) atTop (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ ?_⟩
  · have h : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 2)) atTop (𝓝 0) := by
      have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      refine (h0.comp (tendsto_add_atTop_nat 1)).congr fun k ↦ ?_
      simp only [Function.comp_apply]
      push_cast
      ring_nf
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    rwa [sub_zero] at h1
  · change (1 : ℝ) - 1 / (k + 2) < 1
    have : (0 : ℝ) < 1 / (k + 2) := by positivity
    linarith

theorem cutoff_mem (k : ℕ) : (1 : ℝ) - 1 / (k + 2) ∈ Ico (0 : ℝ) 1 := by
  have h1 : (1 : ℝ) / (k + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h2 : (0 : ℝ) < 1 / (k + 2) := by positivity
  constructor <;> linarith

end Cutoff

section Budget

variable {X : Type*} [Fintype X] [MeasurableSpace X] [Nonempty X]
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

variable (D : Measure X) [IsProbabilityMeasure D]

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

/-- The velocity of the journey towards the data law, `θ̇_t = (Dm(θ_t)|_W)⁻¹ (m_D − m_ν)`. -/
noncomputable def journeyVelD (t : ℝ) : 𝕍 :=
  (CDE (polytopeJourney hS ν mD t)).symm ⟨mD - m₀, dataMean_sub_featureless_mem hS ν hν D⟩

/-- The Fisher energy `G_{θ_t}(θ̇_t, θ̇_t)` along the journey towards the data law. -/
noncomputable def journeyEnergy (t : ℝ) : ℝ :=
  fisherVar S ν (polytopeJourney hS ν mD t : J → ℝ) (journeyVelD hS ν hν D t : J → ℝ)

omit [Fintype X] in
theorem journeyEnergy_nonneg (t : ℝ) : 0 ≤ journeyEnergy hS ν hν D t :=
  fisherVar_nonneg hS ν _ _

/-- The journey towards the data law, cut at `T < 1`, is the model journey from the featureless
response to `θ_T`. -/
theorem polytopeJourney_mul_eq_modelJourney {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (s : ℝ) :
    polytopeJourney hS ν mD (T * s) = modelJourney hS ν 0 (polytopeJourney hS ν mD T) s := by
  unfold modelJourney
  rw [meanMap_polytopeJourney_lt_one hS ν hν D hT0 hT1, Submodule.coe_zero]
  unfold polytopeJourney
  congr 1
  module

/-- The velocity of the cut journey is `T` times the velocity of the journey towards the data. -/
theorem modelVel_eq_smul_journeyVelD {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (s : ℝ) :
    modelVel hS ν 0 (polytopeJourney hS ν mD T) s = T • journeyVelD hS ν hν D (T * s) := by
  unfold modelVel journeyVelD
  rw [← polytopeJourney_mul_eq_modelJourney hS ν hν D hT0 hT1, ← map_smul]
  congr 1
  apply Subtype.ext
  simp only [modelDir, Submodule.coe_smul, Submodule.coe_zero]
  rw [meanMap_polytopeJourney_lt_one hS ν hν D hT0 hT1, add_sub_cancel_left]

/-- The Fisher energy of the cut journey is `T²` times the journey energy. -/
theorem fisherInner_modelVel_eq_journeyEnergy {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (s : ℝ) :
    fisherInner S ν (modelJourney hS ν 0 (polytopeJourney hS ν mD T) s)
        (modelVel hS ν 0 (polytopeJourney hS ν mD T) s)
        (modelVel hS ν 0 (polytopeJourney hS ν mD T) s) =
      T ^ 2 * journeyEnergy hS ν hν D (T * s) := by
  rw [modelVel_eq_smul_journeyVelD hS ν hν D hT0 hT1, fisherInner_self,
    ← polytopeJourney_mul_eq_modelJourney hS ν hν D hT0 hT1, Submodule.coe_smul,
    fisherVar_smul hS ν]
  rfl

/-- **The interior information budget of the journey towards the data law**: for `T < 1`,
`KL(P_{θ_T}‖ν) = ∫₀^T (T − t) G_{θ_t}(θ̇_t, θ̇_t) dt`. -/
theorem toReal_klDiv_polytopeJourney_eq_action {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    (klDiv (Pfam (polytopeJourney hS ν mD T : J → ℝ)) ν).toReal =
      ∫ t in (0 : ℝ)..T, (T - t) * journeyEnergy hS ν hν D t := by
  have h := toReal_klDiv_modelJourney_eq_action hS ν 0 (polytopeJourney hS ν mD T)
  rw [Submodule.coe_zero, familyMeasure_zero_eq hS ν] at h
  rw [h]
  simp_rw [fisherInner_modelVel_eq_journeyEnergy hS ν hν D hT0 hT1]
  rcases eq_or_lt_of_le hT0 with rfl | hTpos
  · simp
  · have hc := intervalIntegral.smul_integral_comp_mul_left
      (f := fun t ↦ (T - t) * journeyEnergy hS ν hν D t) (a := 0) (b := 1) T
    rw [mul_zero, mul_one] at hc
    rw [← hc, smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    ring

/-- The journey energy is continuous on every `[0, T]` with `T < 1`. -/
theorem continuousOn_journeyEnergy {T : ℝ} (hT0 : 0 < T) (hT1 : T < 1) :
    ContinuousOn (journeyEnergy hS ν hν D) (Icc 0 T) := by
  have hsp := continuousOn_modelSpeed hS ν 0 (polytopeJourney hS ν mD T)
  have e : journeyEnergy hS ν hν D = fun t ↦ (T ^ 2)⁻¹ *
      fisherInner S ν (modelJourney hS ν 0 (polytopeJourney hS ν mD T) (t / T))
        (modelVel hS ν 0 (polytopeJourney hS ν mD T) (t / T))
        (modelVel hS ν 0 (polytopeJourney hS ν mD T) (t / T)) := by
    funext t
    rw [fisherInner_modelVel_eq_journeyEnergy hS ν hν D hT0.le hT1, mul_div_cancel₀ _ hT0.ne']
    field_simp
  rw [e]
  refine continuousOn_const.mul (hsp.comp (continuousOn_id.div_const T) fun t ht ↦ ?_)
  refine Icc_subset_modelJourneyDomain hS ν 0 _ ⟨div_nonneg ht.1 hT0.le, ?_⟩
  rw [div_le_one hT0]
  exact ht.2

/-- The truncated budget `∫₀^T (1 − t) G dt`. -/
noncomputable def journeyAction (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, (1 - t) * journeyEnergy hS ν hν D t

theorem intervalIntegrable_journeyEnergy_mul {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (c : ℝ) :
    IntervalIntegrable (fun t ↦ (c - t) * journeyEnergy hS ν hν D t) volume 0 T := by
  rcases eq_or_lt_of_le hT0 with rfl | hTpos
  · exact IntervalIntegrable.refl
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hTpos.le]
    exact (continuousOn_const.sub continuousOn_id).mul
      (continuousOn_journeyEnergy hS ν hν D hTpos hT1)

theorem intervalIntegrable_journeyEnergy {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    IntervalIntegrable (journeyEnergy hS ν hν D) volume 0 T := by
  rcases eq_or_lt_of_le hT0 with rfl | hTpos
  · exact IntervalIntegrable.refl
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hTpos.le]
    exact continuousOn_journeyEnergy hS ν hν D hTpos hT1

theorem intervalIntegrable_id_mul_journeyEnergy {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    IntervalIntegrable (fun t ↦ t * journeyEnergy hS ν hν D t) volume 0 T := by
  rcases eq_or_lt_of_le hT0 with rfl | hTpos
  · exact IntervalIntegrable.refl
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hTpos.le]
    exact continuousOn_id.mul (continuousOn_journeyEnergy hS ν hν D hTpos hT1)

/-- The cutoff budget lies below the truncated budget. -/
theorem toReal_klDiv_polytopeJourney_le_journeyAction {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    (klDiv (Pfam (polytopeJourney hS ν mD T : J → ℝ)) ν).toReal ≤ journeyAction hS ν hν D T := by
  rw [toReal_klDiv_polytopeJourney_eq_action hS ν hν D hT0 hT1]
  unfold journeyAction
  refine intervalIntegral.integral_mono_on hT0 (intervalIntegrable_journeyEnergy_mul hS ν hν D
    hT0 hT1 T) (intervalIntegrable_journeyEnergy_mul hS ν hν D hT0 hT1 1) fun t _ ↦ ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (journeyEnergy_nonneg hS ν hν D t)

/-- The truncated budget lies below the boundary information. -/
theorem journeyAction_le_toReal_klDiv [MeasurableSingletonClass X] {T : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T < 1) :
    journeyAction hS ν hν D T ≤ (klDiv (responseProjection hS ν mD) ν).toReal := by
  have hKL := tendsto_klDiv_polytopeJourney hS ν hν D
  -- the cut budget at `T'` dominates the `[0,T]` piece
  have hle : ∀ T' ∈ Ioo T 1, ∫ t in (0 : ℝ)..T, (T' - t) * journeyEnergy hS ν hν D t ≤
      (klDiv (Pfam (polytopeJourney hS ν mD T' : J → ℝ)) ν).toReal := by
    intro T' hT'
    have h1 : IntervalIntegrable (fun t ↦ (T' - t) * journeyEnergy hS ν hν D t) volume 0 T :=
      intervalIntegrable_journeyEnergy_mul hS ν hν D hT0 hT1 T'
    have h2 : IntervalIntegrable (fun t ↦ (T' - t) * journeyEnergy hS ν hν D t) volume T T' := by
      refine (intervalIntegrable_journeyEnergy_mul hS ν hν D (hT0.trans hT'.1.le) hT'.2 T').mono_set
        ?_
      rw [uIcc_of_le hT'.1.le, uIcc_of_le (hT0.trans hT'.1.le)]
      exact Icc_subset_Icc hT0 le_rfl
    rw [toReal_klDiv_polytopeJourney_eq_action hS ν hν D (hT0.trans hT'.1.le) hT'.2,
      ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    refine le_add_of_nonneg_right (intervalIntegral.integral_nonneg hT'.1.le fun u hu ↦ ?_)
    exact mul_nonneg (by linarith [hu.2]) (journeyEnergy_nonneg hS ν hν D u)
  -- the `[0,T]` piece depends affinely on `T'`
  have haff : ∀ T' : ℝ, ∫ t in (0 : ℝ)..T, (T' - t) * journeyEnergy hS ν hν D t =
      T' * (∫ t in (0 : ℝ)..T, journeyEnergy hS ν hν D t) -
        ∫ t in (0 : ℝ)..T, t * journeyEnergy hS ν hν D t := by
    intro T'
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((intervalIntegrable_journeyEnergy hS ν hν D hT0 hT1).const_mul T')
      (intervalIntegrable_id_mul_journeyEnergy hS ν hν D hT0 hT1)]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    ring
  have hlim : Tendsto (fun T' ↦ ∫ t in (0 : ℝ)..T, (T' - t) * journeyEnergy hS ν hν D t) (𝓝[<] 1)
      (𝓝 (journeyAction hS ν hν D T)) := by
    simp_rw [haff]
    unfold journeyAction
    rw [haff 1]
    exact (((continuous_id.mul continuous_const).sub continuous_const).tendsto 1).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hlim hKL ?_
  filter_upwards [Ioo_mem_nhdsLT hT1] with T' hT'
  exact hle T' hT'

/-- **The truncated budgets converge to the boundary information.** -/
theorem tendsto_journeyAction [MeasurableSingletonClass X] :
    Tendsto (journeyAction hS ν hν D) (𝓝[<] 1)
      (𝓝 (klDiv (responseProjection hS ν mD) ν).toReal) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_klDiv_polytopeJourney hS ν hν D)
    tendsto_const_nhds ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with T hT
    exact toReal_klDiv_polytopeJourney_le_journeyAction hS ν hν D hT.1.le hT.2
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with T hT
    exact journeyAction_le_toReal_klDiv hS ν hν D hT.1.le hT.2

/-- **The weighted Fisher energy is Lebesgue integrable on `(0, 1]`.** -/
theorem integrableOn_journeyEnergy [MeasurableSingletonClass X] :
    IntegrableOn (fun t ↦ (1 - t) * journeyEnergy hS ν hν D t) (Ioc (0 : ℝ) 1) := by
  refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
    (a := 0) (b := fun k : ℕ ↦ (1 : ℝ) - 1 / (k + 2)) (l := atTop)
    (I := (klDiv (responseProjection hS ν mD) ν).toReal) (fun k ↦ ?_)
    (tendsto_nhdsWithin_iff.1 (tendsto_cutoff)).1 (Eventually.of_forall fun k ↦ ?_)
  · have := intervalIntegrable_journeyEnergy_mul hS ν hν D (cutoff_mem k).1 (cutoff_mem k).2 1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (cutoff_mem k).1] at this
    exact this
  · have hnn : ∀ t ∈ Ioc (0 : ℝ) (1 - 1 / (k + 2)),
        ‖(1 - t) * journeyEnergy hS ν hν D t‖ = (1 - t) * journeyEnergy hS ν hν D t := by
      intro t ht
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (by linarith [ht.2, (cutoff_mem k).2]) (journeyEnergy_nonneg hS ν hν D t)
    rw [setIntegral_congr_fun measurableSet_Ioc hnn, ← intervalIntegral.integral_of_le
      (cutoff_mem k).1]
    exact journeyAction_le_toReal_klDiv hS ν hν D (cutoff_mem k).1 (cutoff_mem k).2

/-- **THE BOUNDARY INFORMATION BUDGET**: `KL(R_D‖ν) = ∫₀¹ (1 − t) G_{θ_t}(θ̇_t, θ̇_t) dt`, for
every data law. -/
theorem integral_journeyEnergy [MeasurableSingletonClass X] :
    ∫ t in Ioc (0 : ℝ) 1, (1 - t) * journeyEnergy hS ν hν D t =
      (klDiv (responseProjection hS ν mD) ν).toReal := by
  have hcover := aecover_Ioc_of_Ioc (μ := (volume : Measure ℝ)) (a := fun _ : ℕ ↦ (0 : ℝ))
    (b := fun k : ℕ ↦ (1 : ℝ) - 1 / (k + 2)) (l := atTop) tendsto_const_nhds
    (tendsto_nhdsWithin_iff.1 (tendsto_cutoff)).1
  have h1 := hcover.integral_tendsto_of_countably_generated (integrableOn_journeyEnergy hS ν hν D)
  have h2 : Tendsto (fun k : ℕ ↦ journeyAction hS ν hν D (1 - 1 / (k + 2))) atTop
      (𝓝 (klDiv (responseProjection hS ν mD) ν).toReal) :=
    (tendsto_journeyAction hS ν hν D).comp tendsto_cutoff
  refine tendsto_nhds_unique (h1.congr fun k ↦ ?_) h2
  rw [Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc, max_self,
    min_eq_left (cutoff_mem k).2.le]
  unfold journeyAction
  rw [intervalIntegral.integral_of_le (cutoff_mem k).1]

/-- **THE INFORMATION BUDGET OF THE JOURNEY TO ANY DATA LAW**:
`KL(D‖ν) = KL(D‖R_D) + ∫₀¹ (1 − t) G_{θ_t}(θ̇_t, θ̇_t) dt` — the information invisible to the
features plus the Fisher action of the journey from the featureless law to the entropy response of
the data. -/
theorem journey_information_budget [MeasurableSingletonClass X] :
    (klDiv D ν).toReal = (klDiv D (responseProjection hS ν mD)).toReal +
      ∫ t in Ioc (0 : ℝ) 1, (1 - t) * journeyEnergy hS ν hν D t := by
  rw [integral_journeyEnergy hS ν hν D]
  exact toReal_klDiv_data_eq_defect_add_response hS ν hν D

end Budget

end Laplace.Multi
