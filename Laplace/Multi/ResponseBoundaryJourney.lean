/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseMeanPolytopeJourney
import Laplace.Multi.ResponseSimplexIdentification
import Laplace.Multi.FiniteCompletionContinuity

/-!
# The boundary journey: every finite data law is reachable in response

For a finite space with charged atoms and **any** data law `D` — no saturation, no full support of
`D`, its mean possibly on the boundary of the moment polytope — the affine mean journey
`m_t = m_ν + t(m_D − m_ν)` stays in the relative interior for `t < 1`
(`mem_intrinsicInterior_segment_of_mem`), so the response journey `θ_t = m⁻¹(m_t)` is defined and
`C¹` on `[0,1)` with the prescribed means (`meanMap_polytopeJourney_lt_one`,
`hasDerivAt_polytopeJourney_lt_one`). Its laws are the entropy projections of the means
(`atomMass_polytopeJourney_eq_qStarVec`), and as `t ↑ 1` they converge to the **entropy response**
`R_D` of the data law — the unique minimiser of `KL(·‖ν)` on the fibre of `m_D`
(`tendsto_atomMass_polytopeJourney`, `tendsto_integral_polytopeJourney`,
`tendsto_klDiv_polytopeJourney`), even when the natural coordinate escapes to infinity.

The exact information budget (`toReal_klDiv_data_eq_defect_add_response`):

`KL(D‖ν) = KL(D‖R_D) + KL(R_D‖ν)`,

the first term being the information invisible to the features, the second the information acquired
by the response. The flagship `boundary_journey` bundles these: **the chart may end, but the
response journey does not.** In saturation `R_D = D` (J2), the defect vanishes and the journey is
the mixture segment up to its boundary endpoint.
-/

open MeasureTheory InformationTheory Filter Topology Set

namespace Laplace.Multi

section Segment

variable {J : Type*} [Fintype J]

set_option linter.unusedFintypeInType false in
/-- **The open segment from a relative-interior point to any point of a convex set is
relative-interior.** -/
theorem mem_intrinsicInterior_segment_of_mem {K : Set (J → ℝ)} (hK : Convex ℝ K) {a b : J → ℝ}
    (ha : a ∈ intrinsicInterior ℝ K) (hb : b ∈ K) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    a + t • (b - a) ∈ intrinsicInterior ℝ K := by
  rw [mem_intrinsicInterior_iff_forall_supporting hK] at ha ⊢
  have hmem : a + t • (b - a) ∈ K :=
    hK.add_smul_mem ha.1 (by rw [add_sub_cancel]; exact hb) ⟨ht0, ht1.le⟩
  refine ⟨hmem, fun e he y hy ↦ ?_⟩
  have hlin : dotJ e (a + t • (b - a)) = dotJ e a + t * (dotJ e b - dotJ e a) := by
    rw [(isLinearMap_dotJ e).map_add, (isLinearMap_dotJ e).map_smul,
      (isLinearMap_dotJ e).map_sub, smul_eq_mul]
  have hea := he a ha.1
  have heb := he b hb
  rw [hlin] at hea heb
  have h4 : dotJ e b - dotJ e a ≤ 0 := by
    by_contra h
    push Not at h
    have := mul_pos (sub_pos.2 ht1) h
    nlinarith
  have h5 : t * (dotJ e b - dotJ e a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 h4
  have hc : dotJ e (a + t • (b - a)) = dotJ e a := by
    rw [hlin]
    linarith
  have hmax : ∀ y' ∈ K, dotJ e y' ≤ dotJ e a := fun y' hy' ↦ (he y' hy').trans hc.le
  rw [hc]
  exact ha.2 e hmax y hy

end Segment

section Boundary

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

variable (D : Measure X) [IsProbabilityMeasure D]

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

omit [MeasurableSingletonClass X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The mean of any data law lies in the moment polytope. -/
theorem dataLawMean_mem_polytope : mD ∈ hull := by
  rw [← momentBody_eq_convexHull hS ν hν]
  exact mean_mem_momentBody_of_ac hS ν D (absolutelyContinuous_of_full_support hν D)

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem dataMean_mem_momentBody : mD ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S :=
  mean_mem_momentBody_of_ac hS ν D (absolutelyContinuous_of_full_support hν D)

omit [Fintype X] [MeasurableSingletonClass X] in
/-- The data mean differs from the featureless mean by a direction. -/
theorem dataMean_sub_featureless_mem : mD - m₀ ∈ 𝕍 :=
  sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (dataMean_mem_momentBody hS ν hν D)

omit [MeasurableSingletonClass X] in
/-- **The mean journey towards any data law is relative-interior for `t < 1`.** -/
theorem boundary_segment_mem {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    m₀ + t • (mD - m₀) ∈ intrinsicInterior ℝ hull :=
  mem_intrinsicInterior_segment_of_mem (convex_convexHull ℝ _) (featureless_mem_polytope hS ν hν)
    (dataLawMean_mem_polytope hS ν hν D) ht0 ht1

omit [MeasurableSingletonClass X] in
theorem boundary_segment_mem_Ω {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    m₀ + t • (mD - m₀) ∈ Ω := by
  rw [intrinsicInterior_momentBody_eq_polytope hS ν hν]
  exact boundary_segment_mem hS ν hν D ht0 ht1

omit [MeasurableSingletonClass X] in
/-- **The response journey towards any data law has the prescribed means on `[0,1)`.** -/
theorem meanMap_polytopeJourney_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    mean (polytopeJourney hS ν mD t : J → ℝ) = m₀ + t • (mD - m₀) :=
  meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (boundary_segment_mem_Ω hS ν hν D ht0 ht1)

omit [MeasurableSingletonClass X] in
/-- **The response journey towards any data law is `C¹` on `[0,1)`.** -/
theorem hasDerivAt_polytopeJourney_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt (polytopeJourney hS ν mD)
      ((CDE (polytopeJourney hS ν mD t)).symm
        ⟨mD - m₀, dataMean_sub_featureless_mem hS ν hν D⟩) t := by
  have hV : ∀ s : ℝ, (m₀ + s • (mD - m₀)) - m₀ ∈ 𝕍 := fun s ↦ by
    rw [add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (dataMean_sub_featureless_mem hS ν hν D)
  have hM' : HasDerivAt (fun s : ℝ ↦ m₀ + s • (mD - m₀)) (mD - m₀) t := by
    simpa using ((hasDerivAt_id t).smul_const (mD - m₀)).const_add m₀
  exact hasDerivAt_responseTheta_path measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hV (boundary_segment_mem_Ω hS ν hν D ht0 ht1) hM'

omit hν in
/-- The atom masses of an interior response are the entropy projection of its mean. -/
theorem atomMass_responseTheta_eq_qStarVec {M : J → ℝ} (hM : M ∈ Ω) :
    atomMass S ν (θr M : J → ℝ) = qStarVec hS ν M := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hM
  funext x
  unfold atomMass
  rw [← vecMeasure_qStarVec_eq_familyMeasure hS ν hM, measureReal_def,
    vecMeasure_apply_singleton, ENNReal.toReal_ofReal ((qStarVec_mem_stdSimplex hS ν hfin).1 x)]

/-- **The laws along the journey are the entropy projections of the means.** -/
theorem atomMass_polytopeJourney_eq_qStarVec {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    atomMass S ν (polytopeJourney hS ν mD t : J → ℝ) = qStarVec hS ν (m₀ + t • (mD - m₀)) :=
  atomMass_responseTheta_eq_qStarVec hS ν (boundary_segment_mem_Ω hS ν hν D ht0 ht1)

omit [MeasurableSingletonClass X] in
/-- The mean journey converges to the data mean inside the polytope. -/
theorem tendsto_segment_dataMean :
    Tendsto (fun t : ℝ ↦ m₀ + t • (mD - m₀)) (𝓝[<] 1) (𝓝[hull] mD) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun t : ℝ ↦ m₀ + t • (mD - m₀)) (𝓝 1) (𝓝 (m₀ + (1 : ℝ) • (mD - m₀))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 1
    rw [one_smul, add_sub_cancel] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
    exact intrinsicInterior_subset (boundary_segment_mem hS ν hν D ht.1.le ht.2)

/-- **THE BOUNDARY JOURNEY CONVERGES**: the laws of the response journey towards any data law
converge, as `t ↑ 1`, to the entropy response `R_D = q*(m_D)` of the data law — even when the
natural coordinate escapes to infinity. -/
theorem tendsto_atomMass_polytopeJourney :
    Tendsto (fun t : ℝ ↦ atomMass S ν (polytopeJourney hS ν mD t : J → ℝ)) (𝓝[<] 1)
      (𝓝 (qStarVec hS ν mD)) := by
  have hq : Tendsto (qStarVec hS ν) (𝓝[hull] mD) (𝓝 (qStarVec hS ν mD)) :=
    (continuousOn_qStarVec hS ν hν).continuousWithinAt (dataLawMean_mem_polytope hS ν hν D)
  have h := hq.comp (tendsto_segment_dataMean hS ν hν D)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
  exact (atomMass_polytopeJourney_eq_qStarVec hS ν hν D ht.1.le ht.2).symm

/-- The entropy response of the data law is a probability law with atom masses `q*(m_D)`. -/
theorem vecMeasure_qStarVec_dataMean :
    vecMeasure (qStarVec hS ν mD) = responseProjection hS ν mD :=
  vecMeasure_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν
    (dataLawMean_mem_polytope hS ν hν D))

/-- Integrals against the entropy response are barycentric sums. -/
theorem integral_responseProjection_dataMean (F : X → ℝ) :
    ∫ x, F x ∂responseProjection hS ν mD = ∑ x, qStarVec hS ν mD x * F x := by
  rw [← vecMeasure_qStarVec_dataMean hS ν hν D]
  exact integral_vecMeasure (qStarVec_mem_stdSimplex hS ν
    (genRate_ne_top_of_mem_convexHull hS ν hν (dataLawMean_mem_polytope hS ν hν D))).1 F

/-- **Every posterior expectation converges along the boundary journey** to its value under the
entropy response of the data law. -/
theorem tendsto_integral_polytopeJourney (F : X → ℝ) :
    Tendsto (fun t : ℝ ↦ ∫ x, F x ∂Pfam (polytopeJourney hS ν mD t : J → ℝ)) (𝓝[<] 1)
      (𝓝 (∫ x, F x ∂responseProjection hS ν mD)) := by
  have hc : Continuous fun p : X → ℝ ↦ ∑ x, p x * F x := by fun_prop
  have h := (hc.tendsto _).comp (tendsto_atomMass_polytopeJourney hS ν hν D)
  rw [integral_responseProjection_dataMean hS ν hν D]
  refine h.congr' (Eventually.of_forall fun t ↦ ?_)
  simp only [Function.comp_def]
  exact (integral_familyMeasure_eq_sum hS ν _ F).symm

/-- The relative entropy of an interior response is the entropy of its atom masses. -/
theorem toReal_klDiv_responseTheta {M : J → ℝ} (hM : M ∈ Ω) :
    (klDiv (Pfam (θr M : J → ℝ)) ν).toReal = entVec ν (qStarVec hS ν M) := by
  rw [← vecMeasure_qStarVec_eq_familyMeasure hS ν hM]
  exact toReal_klDiv_vecMeasure ν hν
    (qStarVec_mem_stdSimplex hS ν (genRate_ne_top_of_mem_intrinsicInterior hS ν hM))

/-- The relative entropy of the entropy response is the entropy of its atom masses. -/
theorem toReal_klDiv_responseProjection_dataMean :
    (klDiv (responseProjection hS ν mD) ν).toReal = entVec ν (qStarVec hS ν mD) := by
  rw [← vecMeasure_qStarVec_dataMean hS ν hν D]
  exact toReal_klDiv_vecMeasure ν hν (qStarVec_mem_stdSimplex hS ν
    (genRate_ne_top_of_mem_convexHull hS ν hν (dataLawMean_mem_polytope hS ν hν D)))

/-- **The information acquired along the boundary journey converges** to the relative entropy of
the entropy response. -/
theorem tendsto_klDiv_polytopeJourney :
    Tendsto (fun t : ℝ ↦ (klDiv (Pfam (polytopeJourney hS ν mD t : J → ℝ)) ν).toReal) (𝓝[<] 1)
      (𝓝 (klDiv (responseProjection hS ν mD) ν).toReal) := by
  have h := ((continuous_entVec ν hν).tendsto _).comp (tendsto_atomMass_polytopeJourney hS ν hν D)
  rw [toReal_klDiv_responseProjection_dataMean hS ν hν D]
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
  simp only [Function.comp_def]
  rw [atomMass_polytopeJourney_eq_qStarVec hS ν hν D ht.1.le ht.2]
  exact (toReal_klDiv_responseTheta hS ν hν (boundary_segment_mem_Ω hS ν hν D ht.1.le ht.2)).symm

/-- **The exact information budget of a data law**: `KL(D‖ν) = KL(D‖R_D) + KL(R_D‖ν)` — the
information invisible to the features plus the information acquired by the response. -/
theorem toReal_klDiv_data_eq_defect_add_response :
    (klDiv D ν).toReal =
      (klDiv D (responseProjection hS ν mD)).toReal +
        (klDiv (responseProjection hS ν mD) ν).toReal := by
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν (dataLawMean_mem_polytope hS ν hν D)
  obtain ⟨_, _, hR, hpyth⟩ := responseProjection_spec hS ν hfin
  have h := hpyth D inferInstance rfl
  rw [← hR] at h
  have hDν : klDiv D ν ≠ ⊤ := klDiv_ne_top_of_full_support hν D
  rw [h] at hDν
  obtain ⟨h1, h2⟩ := ENNReal.add_ne_top.1 hDν
  rw [h, ENNReal.toReal_add h1 h2]

/-- **THE BOUNDARY JOURNEY THEOREM**: for a finite space with charged atoms and any data law `D`,
the response journey `θ_t = m⁻¹(m_ν + t(m_D − m_ν))` is defined on `[0,1)` with the prescribed
means, its laws converge to the entropy response `R_D` as `t ↑ 1`, every posterior expectation
converges to its `R_D`-value, and the information budget is exact:
`KL(D‖ν) = KL(D‖R_D) + KL(R_D‖ν)`. The chart may end, but the response journey does not. -/
theorem boundary_journey :
    (∀ t : ℝ, 0 ≤ t → t < 1 → mean (polytopeJourney hS ν mD t : J → ℝ) = m₀ + t • (mD - m₀)) ∧
    Tendsto (fun t : ℝ ↦ atomMass S ν (polytopeJourney hS ν mD t : J → ℝ)) (𝓝[<] 1)
      (𝓝 (qStarVec hS ν mD)) ∧
    (∀ F : X → ℝ, Tendsto (fun t : ℝ ↦ ∫ x, F x ∂Pfam (polytopeJourney hS ν mD t : J → ℝ))
      (𝓝[<] 1) (𝓝 (∫ x, F x ∂responseProjection hS ν mD))) ∧
    (klDiv D ν).toReal =
      (klDiv D (responseProjection hS ν mD)).toReal +
        (klDiv (responseProjection hS ν mD) ν).toReal :=
  ⟨fun _ ht0 ht1 ↦ meanMap_polytopeJourney_lt_one hS ν hν D ht0 ht1,
    tendsto_atomMass_polytopeJourney hS ν hν D, tendsto_integral_polytopeJourney hS ν hν D,
    toReal_klDiv_data_eq_defect_add_response hS ν hν D⟩

end Boundary

end Laplace.Multi
