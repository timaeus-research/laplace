/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFeaturelessJourney
import Laplace.Multi.ResponseFisherEnergyVariation
import Laplace.Multi.MeanSegment

/-!
# The information of a data law as the Fisher action of its response journey

Along the featureless journey `θ_t = θ(m₀ + tΔ)` from the reference law to a data law `ρ_g`
(`featurelessJourney`, an m-geodesic with `A_{θ_t} θ'_t = Δ`), the divergence of the model law
`P_{θ_t}` from the reference law has derivative `−⟨θ_t, Δ⟩` and second derivative the Fisher speed
`G_{θ_t}(θ'_t, θ'_t)` (`hasDerivAt_journeyKL`, `hasDerivAt_journeyMoment`). Integrating by parts,

  `KL(P_{Φ(g)} ‖ ν) = ∫₀¹ (1 − t) G_{θ_t}(θ'_t, θ'_t) dt`
  (`toReal_klDiv_response_featureless_eq_action`),
  `KL(ν ‖ P_{Φ(g)}) = ∫₀¹ t G_{θ_t}(θ'_t, θ'_t) dt`
  (`toReal_klDiv_featureless_response_eq_action`),

so the Jeffreys divergence is the unweighted Fisher action of the journey
(`jeffreys_eq_action`). Combined with the KL Pythagorean theorem this is the **information
decomposition of a data law along its response journey**:

  `KL(ρ_g ‖ ν) = KL(ρ_g ‖ P_{Φ(g)}) + ∫₀¹ (1 − t) G_{θ_t}(θ'_t, θ'_t) dt`
  (`toReal_klDiv_eq_defect_add_action`):

the information of the data relative to the featureless law is the information invisible to the
response plus a Fisher action accumulated along the canonical mean-affine journey of the response.
-/

open MeasureTheory Filter Topology Set InformationTheory intervalIntegral

namespace Laplace.Multi

section Action

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

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

omit [Nonempty J] in
/-- The divergence of the reference law from a model law: `KL(ν ‖ P_θ) = ⟨θ, m₀⟩ + log Z(θ)`. -/
theorem toReal_klDiv_featureless_model (θ : J → ℝ) :
    (klDiv ν (Pfam θ)).toReal = dotJ θ m₀ + Real.log (famZ S ν θ) := by
  have e0 : ν.tilted (fun _ : X ↦ (0 : ℝ)) = ν := by simp
  have h := toReal_klDiv_tilted_tilted ν (Bdd.const (0 : ℝ)) (bdd_modelTilt hS θ)
  rw [e0, tilted_modelTilt hS ν θ, integral_exp_modelTilt] at h
  rw [h, integral_sub (integrable_const _) (integrable_of_bdd_prob _ (bdd_modelTilt hS θ)),
    integral_modelTilt hS θ ν]
  have hm : (fun i ↦ ∫ x, S i x ∂ν) = m₀ := by
    have := mean_familyMeasure_one_zero hS ν 0
    rwa [familyMeasure_zero_eq hS ν] at this
  rw [hm]
  simp

/-- The mean map along the featureless journey has constant derivative `Δ`. -/
theorem hasDerivAt_meanMap_featurelessJourney {g : X → ℝ} (hg : Bdd g) {t : ℝ}
    (ht : t ∈ journeyDomain S ν g) :
    HasDerivAt (fun s ↦ mean (featurelessJourney hS ν g s : J → ℝ))
      (tiltedMean S ν g - m₀) t := by
  have hU := (isOpen_journeyDomain hS ν hg).mem_nhds ht
  have haff : HasDerivAt (fun s : ℝ ↦ m₀ + s • (tiltedMean S ν g - m₀))
      (tiltedMean S ν g - m₀) t := by
    simpa using ((hasDerivAt_id t).smul_const (tiltedMean S ν g - m₀)).const_add m₀
  refine haff.congr_of_eventuallyEq ?_
  filter_upwards [hU] with s hs
  exact meanMap_featurelessJourney hS ν hs

/-- The natural coordinate along the journey, coerced. -/
theorem hasDerivAt_featurelessJourney_coe {g : X → ℝ} (hg : Bdd g) {t : ℝ}
    (ht : t ∈ journeyDomain S ν g) :
    HasDerivAt (fun s ↦ (featurelessJourney hS ν g s : J → ℝ))
      (journeyVel hS ν hg t : J → ℝ) t := by
  have h := (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_featurelessJourney hS ν hg ht)
  exact h

/-- **The Fisher speed of the journey is minus the pairing of the velocity with the mean
velocity**: `G(θ',θ') = −⟨θ', Δ⟩`. -/
theorem fisherInner_journeyVel {g : X → ℝ} (hg : Bdd g) (t : ℝ) :
    G (featurelessJourney hS ν g t) (journeyVel hS ν hg t) (journeyVel hS ν hg t) =
      -dotJ (journeyVel hS ν hg t : J → ℝ) (tiltedMean S ν g - m₀) := by
  rw [fisherInner_eq_neg_dotJ hS ν, chartDeriv_journeyVel hS ν hg]
  rfl

/-- **The divergence of the journey's model law from the reference law** has derivative
`−⟨θ_t, Δ⟩`. -/
theorem hasDerivAt_journeyKL {g : X → ℝ} (hg : Bdd g) {t : ℝ} (ht : t ∈ journeyDomain S ν g) :
    HasDerivAt (fun s ↦ (klDiv (Pfam (featurelessJourney hS ν g s : J → ℝ)) ν).toReal)
      (-dotJ (featurelessJourney hS ν g t : J → ℝ) (tiltedMean S ν g - m₀)) t := by
  have e : (fun s ↦ (klDiv (Pfam (featurelessJourney hS ν g s : J → ℝ)) ν).toReal) = fun s ↦
      -dotJ (featurelessJourney hS ν g s : J → ℝ) (mean (featurelessJourney hS ν g s : J → ℝ)) -
        Real.log (famZ S ν (featurelessJourney hS ν g s : J → ℝ)) :=
    funext fun s ↦ toReal_klDiv_model_featureless hS ν _
  rw [e]
  have h1 := hasDerivAt_dotJ (hasDerivAt_featurelessJourney_coe hS ν hg ht)
    (hasDerivAt_meanMap_featurelessJourney hS ν hg ht)
  have h2 := ((hasFDerivAt_famZ hS ν (featurelessJourney hS ν g t : J → ℝ)).log
    (famZ_pos hS ν _).ne').comp_hasDerivAt t (hasDerivAt_featurelessJourney_coe hS ν hg ht)
  refine (h1.neg.sub h2).congr_deriv ?_
  simp only [smul_apply, smul_eq_mul, dotCLM_apply, famMean_eq_meanMap hS ν,
    meanMap_featurelessJourney hS ν ht]
  have hZ : (famZ S ν (featurelessJourney hS ν g t : J → ℝ))⁻¹ *
      (-famZ S ν (featurelessJourney hS ν g t : J → ℝ)) = -1 := by
    rw [mul_neg, inv_mul_cancel₀ (famZ_pos hS ν _).ne']
  rw [← mul_assoc, hZ]
  ring

/-- The moment pairing along the journey has derivative the Fisher speed:
`d/dt (−⟨θ_t, Δ⟩) = G_{θ_t}(θ'_t, θ'_t)`. -/
theorem hasDerivAt_journeyMoment {g : X → ℝ} (hg : Bdd g) {t : ℝ}
    (ht : t ∈ journeyDomain S ν g) :
    HasDerivAt (fun s ↦ -dotJ (featurelessJourney hS ν g s : J → ℝ) (tiltedMean S ν g - m₀))
      (G (featurelessJourney hS ν g t) (journeyVel hS ν hg t) (journeyVel hS ν hg t)) t := by
  have h := (hasDerivAt_dotJ (hasDerivAt_featurelessJourney_coe hS ν hg ht)
    (hasDerivAt_const t (tiltedMean S ν g - m₀))).neg
  refine h.congr_deriv ?_
  rw [dotJ_zero_right, add_zero, fisherInner_journeyVel hS ν hg]

/-- The velocity is continuous on the journey domain. -/
theorem continuousOn_journeyVel {g : X → ℝ} (hg : Bdd g) :
    ContinuousOn (journeyVel hS ν hg) (journeyDomain S ν g) := by
  have hγ : ContinuousOn (featurelessJourney hS ν g) (journeyDomain S ν g) :=
    (contDiffOn_featurelessJourney hS ν hg).continuousOn
  have hR : Continuous fun θ : 𝕍 ↦ ((CDE θ).symm : 𝕍 →L[ℝ] 𝕍) :=
    (contDiff_chartDerivEquiv_symm hS ν).continuous
  exact (hR.comp_continuousOn hγ).clm_apply continuousOn_const

/-- The Fisher speed is continuous on the journey domain. -/
theorem continuousOn_journeySpeed {g : X → ℝ} (hg : Bdd g) :
    ContinuousOn (fun t ↦ G (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
      (journeyVel hS ν hg t)) (journeyDomain S ν g) := by
  have hγ : ContinuousOn (featurelessJourney hS ν g) (journeyDomain S ν g) :=
    (contDiffOn_featurelessJourney hS ν hg).continuousOn
  have hv := continuousOn_journeyVel hS ν hg
  have hmap : ContinuousOn (fun t ↦ (featurelessJourney hS ν g t,
      (journeyVel hS ν hg t, journeyVel hS ν hg t))) (journeyDomain S ν g) :=
    hγ.prodMk (hv.prodMk hv)
  have h := (continuous_fisherInner hS ν).comp_continuousOn hmap
  simpa only [Function.comp_def] using h

/-- **The information of the response as the weighted Fisher action of its journey**:
`KL(P_{Φ(g)} ‖ ν) = ∫₀¹ (1 − t) G_{θ_t}(θ'_t, θ'_t) dt`. -/
theorem toReal_klDiv_response_featureless_eq_action {g : X → ℝ} (hg : Bdd g) :
    (klDiv (Pfam (responseOf hS ν g : J → ℝ)) ν).toReal =
      ∫ t in (0 : ℝ)..1, (1 - t) * G (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
        (journeyVel hS ν hg t) := by
  set q : ℝ → ℝ := fun s ↦ (klDiv (Pfam (featurelessJourney hS ν g s : J → ℝ)) ν).toReal
    with hq
  set p : ℝ → ℝ := fun s ↦ -dotJ (featurelessJourney hS ν g s : J → ℝ) (tiltedMean S ν g - m₀)
    with hp
  set e : ℝ → ℝ := fun t ↦ G (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
    (journeyVel hS ν hg t) with he
  have hsub := Icc_subset_journeyDomain hS ν hg
  -- the primitive `(1 − t) p(t) + q(t)` of `(1 − t) e(t)`
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t ↦ (1 - t) * p t + q t) ((1 - t) * e t) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hq' := hasDerivAt_journeyKL hS ν hg (hsub ht)
    have hp' := hasDerivAt_journeyMoment hS ν hg (hsub ht)
    have h := (((hasDerivAt_id t).const_sub 1).mul hp').add hq'
    refine h.congr_deriv ?_
    simp only [he, id_eq]
    ring
  have hint : IntervalIntegrable (fun t ↦ (1 - t) * e t) volume 0 1 := by
    refine (ContinuousOn.mul (continuous_const.sub continuous_id).continuousOn
      ((continuousOn_journeySpeed hS ν hg).mono hsub)).intervalIntegrable_of_Icc zero_le_one
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  -- endpoint values
  have hq0 : q 0 = 0 := by
    simp only [hq, featurelessJourney_zero hS ν g, Submodule.coe_zero, familyMeasure_zero_eq hS ν,
      klDiv_self, ENNReal.toReal_zero]
  have hp0 : p 0 = 0 := by
    simp only [hp, featurelessJourney_zero hS ν g, Submodule.coe_zero, dotJ_zero_left, neg_zero]
  have hq1 : q 1 = (klDiv (Pfam (responseOf hS ν g : J → ℝ)) ν).toReal := by
    simp only [hq, featurelessJourney_one hS ν g]
  rw [← hq1, hftc]
  simp only [hq0, hp0]
  ring

/-- **The reverse divergence as the weighted Fisher action**:
`KL(ν ‖ P_{Φ(g)}) = ∫₀¹ t G_{θ_t}(θ'_t, θ'_t) dt`. -/
theorem toReal_klDiv_featureless_response_eq_action {g : X → ℝ} (hg : Bdd g) :
    (klDiv ν (Pfam (responseOf hS ν g : J → ℝ))).toReal =
      ∫ t in (0 : ℝ)..1, t * G (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
        (journeyVel hS ν hg t) := by
  set r : ℝ → ℝ := fun s ↦ (klDiv ν (Pfam (featurelessJourney hS ν g s : J → ℝ))).toReal
    with hr
  set e : ℝ → ℝ := fun t ↦ G (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
    (journeyVel hS ν hg t) with he
  have hsub := Icc_subset_journeyDomain hS ν hg
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt r (t * e t) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hre : r = fun s ↦ dotJ (featurelessJourney hS ν g s : J → ℝ) m₀ +
        Real.log (famZ S ν (featurelessJourney hS ν g s : J → ℝ)) :=
      funext fun s ↦ toReal_klDiv_featureless_model hS ν _
    rw [hre]
    have h1 := hasDerivAt_dotJ (hasDerivAt_featurelessJourney_coe hS ν hg (hsub ht))
      (hasDerivAt_const t m₀)
    have h2 := ((hasFDerivAt_famZ hS ν (featurelessJourney hS ν g t : J → ℝ)).log
      (famZ_pos hS ν _).ne').comp_hasDerivAt t (hasDerivAt_featurelessJourney_coe hS ν hg (hsub ht))
    refine (h1.add h2).congr_deriv ?_
    simp only [smul_apply, smul_eq_mul, dotCLM_apply, famMean_eq_meanMap hS ν,
      meanMap_featurelessJourney hS ν (hsub ht), dotJ_zero_right, add_zero]
    have hZ : (famZ S ν (featurelessJourney hS ν g t : J → ℝ))⁻¹ *
        (-famZ S ν (featurelessJourney hS ν g t : J → ℝ)) = -1 := by
      rw [mul_neg, inv_mul_cancel₀ (famZ_pos hS ν _).ne']
    rw [← mul_assoc, hZ, he]
    simp only
    rw [fisherInner_journeyVel hS ν hg, (isLinearMap_dotJ _).map_add, (isLinearMap_dotJ _).map_smul,
      smul_eq_mul]
    ring
  have hint : IntervalIntegrable (fun t ↦ t * e t) volume 0 1 :=
    (continuous_id.continuousOn.mul
      ((continuousOn_journeySpeed hS ν hg).mono hsub)).intervalIntegrable_of_Icc zero_le_one
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  have hr0 : r 0 = 0 := by
    simp only [hr, featurelessJourney_zero hS ν g, Submodule.coe_zero, familyMeasure_zero_eq hS ν,
      klDiv_self, ENNReal.toReal_zero]
  have hr1 : r 1 = (klDiv ν (Pfam (responseOf hS ν g : J → ℝ))).toReal := by
    simp only [hr, featurelessJourney_one hS ν g]
  rw [← hr1, hftc, hr0, sub_zero]

/-- **The Jeffreys divergence is the Fisher action of the journey.** -/
theorem jeffreys_eq_action {g : X → ℝ} (hg : Bdd g) :
    (klDiv (Pfam (responseOf hS ν g : J → ℝ)) ν).toReal +
      (klDiv ν (Pfam (responseOf hS ν g : J → ℝ))).toReal =
      ∫ t in (0 : ℝ)..1, G (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
        (journeyVel hS ν hg t) := by
  rw [toReal_klDiv_response_featureless_eq_action hS ν hg,
    toReal_klDiv_featureless_response_eq_action hS ν hg]
  have hsub := Icc_subset_journeyDomain hS ν hg
  have hc := (continuousOn_journeySpeed hS ν hg).mono hsub
  have i1 : IntervalIntegrable (fun t ↦ (1 - t) * G (featurelessJourney hS ν g t)
      (journeyVel hS ν hg t) (journeyVel hS ν hg t)) volume 0 1 :=
    ((continuous_const.sub continuous_id).continuousOn.mul hc).intervalIntegrable_of_Icc
      zero_le_one
  have i2 : IntervalIntegrable (fun t ↦ t * G (featurelessJourney hS ν g t)
      (journeyVel hS ν hg t) (journeyVel hS ν hg t)) volume 0 1 :=
    (continuous_id.continuousOn.mul hc).intervalIntegrable_of_Icc zero_le_one
  rw [← integral_add i1 i2]
  refine integral_congr fun t _ ↦ ?_
  ring

/-- **The information decomposition of a data law along its response journey**:
`KL(ρ_g ‖ ν) = KL(ρ_g ‖ P_{Φ(g)}) + ∫₀¹ (1 − t) G_{θ_t}(θ'_t, θ'_t) dt`. -/
theorem toReal_klDiv_eq_defect_add_action {g : X → ℝ} (hg : Bdd g) :
    (klDiv (ν.tilted g) ν).toReal =
      responseInformationDefect hS ν g +
        ∫ t in (0 : ℝ)..1, (1 - t) * G (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
          (journeyVel hS ν hg t) := by
  rw [toReal_klDiv_pythagoras_featureless hS ν hg,
    toReal_klDiv_response_featureless_eq_action hS ν hg]
  rfl

/-- **Fisher length squared is at most the Jeffreys divergence**: the Fisher length
`∫₀¹ √G(θ'_t, θ'_t) dt` of the featureless journey satisfies
`L² ≤ KL(P_{Φ(g)} ‖ ν) + KL(ν ‖ P_{Φ(g)})` (Cauchy–Schwarz against the constant weight `1`). -/
theorem sq_journeyLength_le_jeffreys {g : X → ℝ} (hg : Bdd g) :
    (∫ t in (0 : ℝ)..1, Real.sqrt (G (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
        (journeyVel hS ν hg t))) ^ 2 ≤
      (klDiv (Pfam (responseOf hS ν g : J → ℝ)) ν).toReal +
        (klDiv ν (Pfam (responseOf hS ν g : J → ℝ))).toReal := by
  rw [jeffreys_eq_action hS ν hg]
  have hsub := Icc_subset_journeyDomain hS ν hg
  have hc := (continuousOn_journeySpeed hS ν hg).mono hsub
  have hnn : ∀ (θ v : 𝕍), 0 ≤ G θ v v := by
    intro θ v
    by_cases hv : v = 0
    · simp [hv, fisherInner_zero_left]
    · exact (fisherInner_self_pos hS ν θ hv).le
  have h := sq_integral_sqrt_mul_le hc continuousOn_const
    (fun t _ ↦ hnn _ _) (fun _ _ ↦ zero_le_one)
  simpa [intervalIntegral.integral_const] using h

end Action

end Laplace.Multi
