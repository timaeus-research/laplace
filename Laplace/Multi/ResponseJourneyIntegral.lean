/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseGlobalLipschitz
import Laplace.Multi.FiniteResponse

/-!
# The canonical journey integral of a posterior expectation

The polytope journey `M_t = (1 − t) m_ν + t m_D` from the featureless mean to the mean of a data
law `D` lifts to the canonical response journey `Q_t = R_{M_t}` from the featureless law `Q_0 = ν`
to the entropy response `Q_1 = R_{m_D}` of the data (`ResponseBoundaryJourney`). Along it every
posterior
expectation moves by the pairing of its regression direction with the displacement,
`d/dt E_{Q_t}F = ⟨u_F(θ(M_t)), m_D − m_ν⟩` (`hasDerivAt_journeyObs`), and the total change is the
integral of this response field along the journey, endpoint included:

`E_{R_{m_D}}F − E_ν F = ∫₀¹ ⟨u_F(θ(M_t)), m_D − m_ν⟩ dt`
(`integral_responseProjection_sub_eq_journey`).

The endpoint may lie on the boundary of the polytope, where the natural coordinate escapes to
infinity; the identity nevertheless holds because the response field is uniformly bounded along the
journey (`ResponseRegressionUniformBound`) and the laws converge to the entropy response
(`ResponseBoundaryJourney`). The endpoint is the data law itself under saturation. The change in
a posterior expectation between the featureless law and the data is thus an exact integral of the
response field along the canonical path through the data manifold.
-/

open MeasureTheory Filter Topology Set
open scoped Interval

namespace Laplace.Multi

section Journey

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The featureless mean. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The regression direction. -/
local notation "uF" => regressionDir hS ν

variable (D : Measure X) [IsProbabilityMeasure D]

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

/-- **The posterior expectation along the canonical journey**: `E_{Q_t} F`. -/
noncomputable def journeyObs (F : X → ℝ) (t : ℝ) : ℝ :=
  ∫ x, F x ∂Pfam (polytopeJourney hS ν mD t : J → ℝ)

/-- **The response field along the journey**: `⟨u_F(θ(M_t)), m_D − m_ν⟩`. -/
noncomputable def journeyField (F : X → ℝ) (t : ℝ) : ℝ :=
  dotJ (uF F (polytopeJourney hS ν mD t) : J → ℝ) (mD - m₀)

omit [Fintype X] [MeasurableSingletonClass X] hν [IsProbabilityMeasure D] in
/-- The journey starts at the featureless law. -/
theorem journeyObs_zero (F : X → ℝ) : journeyObs hS ν D F 0 = ∫ x, F x ∂ν := by
  unfold journeyObs
  rw [polytopeJourney_zero hS ν _, Submodule.coe_zero, familyMeasure_zero_eq hS ν]

omit [MeasurableSingletonClass X] in
/-- **The first response along the journey**: `d/dt E_{Q_t} F = ⟨u_F(θ(M_t)), m_D − m_ν⟩`. -/
theorem hasDerivAt_journeyObs {F : X → ℝ} (hF : Bdd F) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt (journeyObs hS ν D F) (journeyField hS ν D F t) t := by
  have hθ := hasDerivAt_polytopeJourney_lt_one hS ν hν D ht0 ht1
  have hθ' : HasDerivAt (fun s ↦ (polytopeJourney hS ν mD s : J → ℝ))
      (((CDE (polytopeJourney hS ν mD t)).symm
        ⟨mD - m₀, dataMean_sub_featureless_mem hS ν hν D⟩ : 𝕍) : J → ℝ) t :=
    (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t hθ
  have h := hasDerivAt_integral_familyMeasure_path hS ν hθ' hF
  refine h.congr_deriv ?_
  unfold journeyField
  rw [← fisherInner_regressionDir hS ν hF, fisherInner_chartDerivEquiv_symm' hS ν, neg_neg]

/-- The journey ends at the entropy response of the data law. -/
theorem tendsto_journeyObs_one (F : X → ℝ) :
    Tendsto (journeyObs hS ν D F) (𝓝[<] 1) (𝓝 (∫ x, F x ∂responseProjection hS ν mD)) := by
  rw [integral_responseProjection_dataMean hS ν hν D F]
  have h := tendsto_finsetSum (Finset.univ : Finset X) fun x _ ↦
    (((continuous_apply x).tendsto _).comp (tendsto_atomMass_polytopeJourney hS ν hν D)).mul_const
      (F x)
  refine h.congr' (Eventually.of_forall fun t ↦ ?_)
  unfold journeyObs
  rw [integral_familyMeasure_eq_sum hS ν]
  rfl

omit [IsProbabilityMeasure D] in
/-- The response field is uniformly bounded along the journey. -/
theorem exists_journeyField_bound {F : X → ℝ} (hF : Bdd F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |journeyField hS ν D F t| ≤ C := by
  obtain ⟨L, hL0, hL⟩ :=
    exists_uniform_sum_abs_regressionDir_bound hS ν (fun x ↦ (hν x).ne') hF
  refine ⟨L * ‖mD - m₀‖, by positivity, fun t ↦ ?_⟩
  unfold journeyField
  exact (abs_dotJ_le _ _).trans (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _))

/-- The response field is integrable on the journey (it agrees a.e. with the measurable derivative
of the posterior expectation, which is bounded on `[0, 1)`). -/
theorem intervalIntegrable_journeyField {F : X → ℝ} (hF : Bdd F) {T : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) : IntervalIntegrable (journeyField hS ν D F) volume 0 T := by
  obtain ⟨C, -, hC⟩ := exists_journeyField_bound hS ν hν D hF
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
    rw [ae_iff]
    simp
  have hae : ∀ᵐ t ∂(volume.restrict (Ι 0 T)),
      journeyField hS ν D F t = deriv (journeyObs hS ν D F) t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae h1] with t ht ht1
    rw [uIoc_of_le hT0] at ht
    exact ((hasDerivAt_journeyObs hS ν hν D hF ht.1.le
      (lt_of_le_of_ne (ht.2.trans hT1) ht1)).deriv).symm
  rw [intervalIntegrable_iff]
  refine (Measure.integrableOn_of_bounded (f := deriv (journeyObs hS ν D F)) (M := C)
    measure_Ioc_lt_top.ne ?_ ?_).congr_fun_ae ?_
  · exact (measurable_deriv _).aestronglyMeasurable
  · filter_upwards [hae] with t ht
    rw [← ht, Real.norm_eq_abs]
    exact hC t
  · exact Filter.EventuallyEq.symm hae

/-- The fundamental theorem of calculus along the journey, before the endpoint. -/
theorem journeyObs_sub_eq_integral {F : X → ℝ} (hF : Bdd F) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    journeyObs hS ν D F T - journeyObs hS ν D F 0 =
      ∫ t in (0 : ℝ)..T, journeyField hS ν D F t := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_)
    (intervalIntegrable_journeyField hS ν hν D hF hT0 hT1.le)).symm
  rw [uIcc_of_le hT0] at ht
  exact hasDerivAt_journeyObs hS ν hν D hF ht.1 (lt_of_le_of_lt ht.2 hT1)

/-- **THE CANONICAL JOURNEY INTEGRAL**: the change of a posterior expectation from the featureless
law to the entropy response of the data is the integral of the response field along the canonical
journey, endpoint included:
`E_{R_{m_D}}F − E_ν F = ∫₀¹ ⟨u_F(θ(M_t)), m_D − m_ν⟩ dt`. -/
theorem integral_responseProjection_sub_eq_journey {F : X → ℝ} (hF : Bdd F) :
    (∫ x, F x ∂responseProjection hS ν mD) - ∫ x, F x ∂ν =
      ∫ t in (0 : ℝ)..1, journeyField hS ν D F t := by
  obtain ⟨C, -, hC⟩ := exists_journeyField_bound hS ν hν D hF
  have hint := intervalIntegrable_journeyField hS ν hν D hF zero_le_one le_rfl
  -- the left-hand side is the limit of the pre-endpoint differences
  have hL : Tendsto (fun T ↦ journeyObs hS ν D F T - journeyObs hS ν D F 0) (𝓝[<] 1)
      (𝓝 ((∫ x, F x ∂responseProjection hS ν mD) - ∫ x, F x ∂ν)) := by
    rw [← journeyObs_zero hS ν D F]
    exact (tendsto_journeyObs_one hS ν hν D F).sub_const _
  -- the right-hand side is the limit of the pre-endpoint integrals
  have hR : Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, journeyField hS ν D F t) (𝓝[<] 1)
      (𝓝 (∫ t in (0 : ℝ)..1, journeyField hS ν D F t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbd : Tendsto (fun T : ℝ ↦ C * |1 - T|) (𝓝[<] 1) (𝓝 0) := by
      have : Tendsto (fun T : ℝ ↦ C * |1 - T|) (𝓝 1) (𝓝 (C * |1 - 1|)) :=
        (continuous_const.mul ((continuous_const.sub continuous_id).abs)).tendsto 1
      rw [sub_self, abs_zero, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun T ↦ norm_nonneg _) ?_ hbd
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with T hT
    have hT' : IntervalIntegrable (journeyField hS ν D F) volume 0 T :=
      intervalIntegrable_journeyField hS ν hν D hF hT.1.le hT.2.le
    rw [← norm_neg, neg_sub, intervalIntegral.integral_interval_sub_left hint hT']
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦ by
      rw [Real.norm_eq_abs]
      exact hC t
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with T hT
  exact (journeyObs_sub_eq_integral hS ν hν D hF hT.1.le hT.2).symm

end Journey

end Laplace.Multi
