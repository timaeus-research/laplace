/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseGlobalInformationLandscape
import Laplace.Multi.ResponseSamplingGeometry

/-!
# The featureless law as maximal entropy, and the model information as a convex potential

Three precise versions of "from the featureless law of maximal entropy":

* **Reference-relative entropy.** `H_ν(ρ) = −KL(ρ ‖ ν)` is at most `0` on the data manifold, with
  equality exactly at `ρ = ν` (`relativeEntropy_nonpos`, `relativeEntropy_eq_zero_iff`). This is a
  Shannon-entropy statement only when the reference is uniform on a finite set.
* **The model is the maximum-entropy section of the response fibres.** Among the data laws with a
  given response, the model law of that response has the largest relative entropy
  (`totalInfo_model_le`), with equality only for the model law itself.
* **The model information is a convex potential in mean coordinates.** Along a response line
  `t ↦ m(θ₀) + t e`, `𝓘(t) = KL(P_{θ_t} ‖ ν)` has `𝓘' = −⟨θ_t, e⟩` and `𝓘'' = G_{θ_t}(V_t, V_t) ≥ 0`
  (`hasDerivAt_modelInfoLine`, `hasDerivAt_deriv_modelInfoLine`); along the featureless journey
  it starts flat and **rises monotonically** (`monotoneOn_journeyKL`): the response accumulates
  information from the featureless law all the way to the data.

Caution (not formalised): along the *power-tilt* path `ν.tilted(t g)` the projected model
information need not be monotone (three-point counterexample in the round-97 consult); the
monotone statement is for the canonical mean-affine journey.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Entropy

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty X] [Nonempty J] hS [Fintype J] [IsProbabilityMeasure ν] in
/-- **The reference-relative entropy** `H_ν(ρ_g) = −KL(ρ_g ‖ ν)`. -/
noncomputable def relativeEntropy (g : X → ℝ) : ℝ := -totalInfo ν g

omit [Nonempty X] [Nonempty J] hS [Fintype J] [IsProbabilityMeasure ν] in
theorem relativeEntropy_nonpos (g : X → ℝ) : relativeEntropy ν g ≤ 0 := by
  unfold relativeEntropy totalInfo
  linarith [ENNReal.toReal_nonneg (a := klDiv (ν.tilted g) ν)]

omit [Nonempty X] [Nonempty J] hS [Fintype J] in
/-- **The featureless law is the unique maximiser of the relative entropy** on the data manifold.
-/
theorem relativeEntropy_eq_zero_iff {g : X → ℝ} (hg : Bdd g) :
    relativeEntropy ν g = 0 ↔ ν.tilted g = ν := by
  have hP := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  unfold relativeEntropy totalInfo
  rw [neg_eq_zero, ENNReal.toReal_eq_zero_iff, or_iff_left (klDiv_tilted_ne_top ν hg),
    klDiv_eq_zero_iff]

omit [Nonempty J] in
/-- The total information of the model law of a response is its response information. -/
theorem totalInfo_modelTilt (θ : 𝕍) :
    totalInfo ν (modelTilt S (θ : J → ℝ)) = (klDiv (Pfam (θ : J → ℝ)) ν).toReal := by
  unfold totalInfo
  rw [tilted_modelTilt hS ν]

/-- **The model law is the maximum-entropy member of its response fibre**: every data law with
response `Φ(g)` carries at least the information of the model law `P_{Φ(g)}`. -/
theorem totalInfo_model_le {g : X → ℝ} (hg : Bdd g) :
    totalInfo ν (modelTilt S (responseOf hS ν g : J → ℝ)) ≤ totalInfo ν g := by
  rw [totalInfo_modelTilt hS ν]
  exact responseInfo_le_totalInfo hS ν hg

/-- Equality in the maximum-entropy section holds exactly for the model law. -/
theorem totalInfo_model_eq_iff {g : X → ℝ} (hg : Bdd g) :
    totalInfo ν (modelTilt S (responseOf hS ν g : J → ℝ)) = totalInfo ν g ↔
      ν.tilted g = Pfam (responseOf hS ν g : J → ℝ) := by
  rw [totalInfo_modelTilt hS ν, totalInfo_eq_defect_add_responseInfo hS ν hg,
    ← responseInformationDefect_eq_zero_iff hS ν hg]
  unfold responseInfo
  constructor
  · intro h; linarith
  · intro h; linarith

end Entropy

section Potential

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

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The response line. -/
local notation "θl" => responseLine hS ν

/-- The response line velocity. -/
local notation "Vl" => responseLineVel hS ν

/-- **The model information along a response line**, `𝓘(t) = KL(P_{θ_t} ‖ ν)`. -/
noncomputable def modelInfoLine (θ₀ e : 𝕍) (t : ℝ) : ℝ :=
  (klDiv (Pfam (θl θ₀ e t : J → ℝ)) ν).toReal

/-- The response line is mean-affine on its domain. -/
theorem meanMap_responseLine (θ₀ e : 𝕍) {t : ℝ} (ht : t ∈ responseLineDomain S ν θ₀ e) :
    mean (θl θ₀ e t : J → ℝ) = mean (θ₀ : J → ℝ) + t • (e : J → ℝ) :=
  meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS ht

/-- The mean along a response line moves with constant velocity `e`. -/
theorem hasDerivAt_meanMap_responseLine (θ₀ e : 𝕍) {t : ℝ}
    (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (fun s ↦ mean (θl θ₀ e s : J → ℝ)) (e : J → ℝ) t := by
  have hU := (isOpen_responseLineDomain hS ν θ₀ e).mem_nhds ht
  have haff : HasDerivAt (fun s : ℝ ↦ mean (θ₀ : J → ℝ) + s • (e : J → ℝ)) (e : J → ℝ) t := by
    simpa using ((hasDerivAt_id t).smul_const (e : J → ℝ)).const_add (mean (θ₀ : J → ℝ))
  refine haff.congr_of_eventuallyEq ?_
  filter_upwards [hU] with s hs
  exact meanMap_responseLine hS ν θ₀ e hs

/-- The response line, coerced. -/
theorem hasDerivAt_responseLine_coe' (θ₀ e : 𝕍) {t : ℝ} (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (fun s ↦ (θl θ₀ e s : J → ℝ)) (Vl θ₀ e t : J → ℝ) t := by
  have h := (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_responseLine hS ν θ₀ e ht)
  exact h

/-- **The model information has mean-coordinate differential `−⟨θ, e⟩`**:
`d/dt KL(P_{θ_t} ‖ ν) = −⟨θ_t, e⟩` along a response line. -/
theorem hasDerivAt_modelInfoLine (θ₀ e : 𝕍) {t : ℝ} (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (modelInfoLine hS ν θ₀ e) (-dotJ (θl θ₀ e t : J → ℝ) (e : J → ℝ)) t := by
  have eq : modelInfoLine hS ν θ₀ e = fun s ↦
      -dotJ (θl θ₀ e s : J → ℝ) (mean (θl θ₀ e s : J → ℝ)) -
        Real.log (famZ S ν (θl θ₀ e s : J → ℝ)) :=
    funext fun s ↦ toReal_klDiv_model_featureless hS ν _
  rw [eq]
  have h1 := hasDerivAt_dotJ (hasDerivAt_responseLine_coe' hS ν θ₀ e ht)
    (hasDerivAt_meanMap_responseLine hS ν θ₀ e ht)
  have h2 := ((hasFDerivAt_famZ hS ν (θl θ₀ e t : J → ℝ)).log
    (famZ_pos hS ν _).ne').comp_hasDerivAt t (hasDerivAt_responseLine_coe' hS ν θ₀ e ht)
  refine (h1.neg.sub h2).congr_deriv ?_
  simp only [smul_apply, smul_eq_mul, dotCLM_apply, famMean_eq_meanMap hS ν,
    meanMap_responseLine hS ν θ₀ e ht]
  have hZ : (famZ S ν (θl θ₀ e t : J → ℝ))⁻¹ * (-famZ S ν (θl θ₀ e t : J → ℝ)) = -1 := by
    rw [mul_neg, inv_mul_cancel₀ (famZ_pos hS ν _).ne']
  rw [← mul_assoc, hZ]
  ring

/-- **The model information is convex in mean coordinates**: its second derivative along a
response line is the Fisher speed `G_{θ_t}(V_t, V_t)`. -/
theorem hasDerivAt_deriv_modelInfoLine (θ₀ e : 𝕍) {t : ℝ}
    (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (fun s ↦ -dotJ (θl θ₀ e s : J → ℝ) (e : J → ℝ))
      (G (θl θ₀ e t) (Vl θ₀ e t) (Vl θ₀ e t)) t := by
  have h := (hasDerivAt_dotJ (hasDerivAt_responseLine_coe' hS ν θ₀ e ht)
    (hasDerivAt_const t (e : J → ℝ))).neg
  refine h.congr_deriv ?_
  rw [dotJ_zero_right, add_zero, fisherInner_eq_neg_dotJ hS ν]
  unfold responseLineVel
  rw [chartDeriv_chartDerivEquiv_symm hS ν]

/-- The second derivative of the model information is nonnegative: the potential is convex. -/
theorem fisherInner_responseLineVel_nonneg (θ₀ e : 𝕍) (t : ℝ) :
    0 ≤ G (θl θ₀ e t) (Vl θ₀ e t) (Vl θ₀ e t) :=
  fisherVar_nonneg hS ν _ _

/-- The featureless journey's information slope `−⟨θ_t, Δ⟩` starts at zero. -/
theorem journeySlope_zero {g : X → ℝ} :
    -dotJ (featurelessJourney hS ν g 0 : J → ℝ) (tiltedMean S ν g - meanMap ν (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 0) = 0 := by
  rw [featurelessJourney_zero hS ν g, Submodule.coe_zero, dotJ_zero_left, neg_zero]

/-- The information slope of the featureless journey is monotone on `[0,1]`. -/
theorem monotoneOn_journeySlope {g : X → ℝ} (hg : Bdd g) :
    MonotoneOn (fun t ↦ -dotJ (featurelessJourney hS ν g t : J → ℝ)
      (tiltedMean S ν g - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) (Icc 0 1) := by
  have hsub := Icc_subset_journeyDomain hS ν hg
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
  · exact fun t ht ↦ (hasDerivAt_journeyMoment hS ν hg (hsub ht)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_journeyMoment hS ν hg (hsub (Ioo_subset_Icc_self ht))).differentiableAt
      |>.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_journeyMoment hS ν hg (hsub (Ioo_subset_Icc_self ht))).deriv]
    exact fisherVar_nonneg hS ν _ _

/-- The information slope of the featureless journey is nonnegative on `[0,1]`. -/
theorem journeySlope_nonneg {g : X → ℝ} (hg : Bdd g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ -dotJ (featurelessJourney hS ν g t : J → ℝ)
      (tiltedMean S ν g - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  have h := monotoneOn_journeySlope hS ν hg (left_mem_Icc.mpr zero_le_one) ht ht.1
  beta_reduce at h
  rw [journeySlope_zero hS ν] at h
  exact h

/-- **The model information rises monotonically along the featureless journey**:
`t ↦ KL(P_{θ_t} ‖ ν)` is monotone on `[0,1]`, from `0` at the featureless law to `KL(P_{Φ(g)} ‖ ν)`
at the data. -/
theorem monotoneOn_journeyKL {g : X → ℝ} (hg : Bdd g) :
    MonotoneOn (fun t ↦ (klDiv (Pfam (featurelessJourney hS ν g t : J → ℝ)) ν).toReal)
      (Icc 0 1) := by
  have hsub := Icc_subset_journeyDomain hS ν hg
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
  · exact fun t ht ↦ (hasDerivAt_journeyKL hS ν hg (hsub ht)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_journeyKL hS ν hg (hsub (Ioo_subset_Icc_self ht))).differentiableAt
      |>.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_journeyKL hS ν hg (hsub (Ioo_subset_Icc_self ht))).deriv]
    exact journeySlope_nonneg hS ν hg (Ioo_subset_Icc_self ht)

end Potential

end Laplace.Multi
