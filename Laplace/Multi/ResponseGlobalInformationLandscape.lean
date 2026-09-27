/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseInformationAction
import Laplace.Multi.ResponseTiltPathBudget

/-!
# The global information landscape over the data manifold

Three functions of a data law `ρ_g = ν.tilted g` (`g` a bounded tilt):

* the **total information** `T(g) = KL(ρ_g ‖ ν)`,
* the **response information** `I(g) = KL(P_{Φ(g)} ‖ ν)`, a function of the response alone
  (constant on every response fibre) and equal to the weighted Fisher action of the featureless
  journey,
* the **defect** `D(g) = KL(ρ_g ‖ P_{Φ(g)})` (`responseInformationDefect`), nonnegative and zero
  exactly on the model,

with the global identity `T = D + I` (`totalInfo_eq_defect_add_responseInfo`).

Along a coefficient path `g_t = ⟨a_t, h⟩` through the data manifold the three move by
covariances with the data velocity `ġ_t` (`δμ_t = Cov_{ρ_t}(S, ġ_t)` the forcing,
`θ_t = Φ(g_t)`):

* `hasDerivAt_totalInfo_coeff`: `T' = Cov_{ρ_t}(g_t, ġ_t)`,
* `hasDerivAt_responseInfo_coeff`: `I' = −⟨θ_t, δμ_t⟩`,
* `hasDerivAt_defect_coeff`: `D' = Cov_{ρ_t}(g_t + ⟨θ_t, S⟩, ġ_t)`.

The response information moves only through the pairing of the response with the mean velocity;
the defect moves by the covariance of the data velocity with the log-likelihood ratio
`g + ⟨θ, S⟩ = log(dρ_g/dP_θ) + const` of the data law against its own information projection.
These formulas separate the information that moves the response from the information that stays
unresolved within its fibre.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Landscape

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

omit [Nonempty X] [Nonempty J] hS [Fintype J] [IsProbabilityMeasure ν] in
/-- **The total information** of a data law relative to the reference law. -/
noncomputable def totalInfo (g : X → ℝ) : ℝ := (klDiv (ν.tilted g) ν).toReal

/-- **The response information**: the information of the response's model law. -/
noncomputable def responseInfo (g : X → ℝ) : ℝ :=
  (klDiv (Pfam (responseOf hS ν g : J → ℝ)) ν).toReal

/-- **The global information identity** `T = D + I` on the data manifold. -/
theorem totalInfo_eq_defect_add_responseInfo {g : X → ℝ} (hg : Bdd g) :
    totalInfo ν g = responseInformationDefect hS ν g + responseInfo hS ν g :=
  toReal_klDiv_pythagoras_featureless hS ν hg

/-- The response information is constant on response fibres. -/
theorem responseInfo_eq_of_responseOf_eq {g k : X → ℝ} (h : responseOf hS ν g = responseOf hS ν k) :
    responseInfo hS ν g = responseInfo hS ν k := by
  unfold responseInfo
  rw [h]

/-- The response information is the weighted Fisher action of the featureless journey. -/
theorem responseInfo_eq_action {g : X → ℝ} (hg : Bdd g) :
    responseInfo hS ν g =
      ∫ t in (0 : ℝ)..1, (1 - t) * G (featurelessJourney hS ν g t) (journeyVel hS ν hg t)
        (journeyVel hS ν hg t) :=
  toReal_klDiv_response_featureless_eq_action hS ν hg

/-- The response information is nonnegative and bounded by the total information. -/
theorem responseInfo_le_totalInfo {g : X → ℝ} (hg : Bdd g) :
    responseInfo hS ν g ≤ totalInfo ν g := by
  rw [totalInfo_eq_defect_add_responseInfo hS ν hg]
  linarith [responseInformationDefect_nonneg hS ν g]

omit [Nonempty X] [Nonempty J] hS in
/-- The normaliser of the featureless member is one. -/
theorem famZ_zero_eq_one : famZ S ν 0 = 1 := by
  simp [famZ, famWeight, dirLoss_zero]

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- The total information in closed form: `T(g) = E_{ρ_g} g − log ∫ e^g dν`. -/
theorem totalInfo_eq {g : X → ℝ} (hg : Bdd g) :
    totalInfo ν g = ∫ x, g x ∂ν.tilted g - Real.log (∫ x, Real.exp (g x) ∂ν) := by
  have h := toReal_klDiv_tilted_model hS ν hg 0
  rw [familyMeasure_zero_eq hS ν, dotJ_zero_left, famZ_zero_eq_one ν, Real.log_one] at h
  unfold totalInfo
  rw [h]
  ring

end Landscape

section Derivatives

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ j, Bdd (h j)) {a a' : ℝ → ι → ℝ}
  (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
include hS hh ha ha'

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] [Fintype J] [Nonempty J] hS ha ha' in
/-- The expectation of the data velocity along the path is the pairing of the coefficient
velocity with the feature means. -/
theorem integral_dirLoss_deriv_eq_dotJ (t : ℝ) :
    ∫ x, dirLoss h (a' t) x ∂ν.tilted (dirLoss h (a t)) = dotJ (a' t) (coeffMean h ν h a t) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t)))
  exact integral_dirLoss_eq_dotJ (u := a' t) _ hh

omit [Nonempty X] [Fintype J] [Nonempty J] hS ha ha' in
/-- The expectation of the tilt along the path is the pairing of the coefficients with the
feature means. -/
theorem integral_dirLoss_self_eq_dotJ (t : ℝ) :
    ∫ x, dirLoss h (a t) x ∂ν.tilted (dirLoss h (a t)) = dotJ (a t) (coeffMean h ν h a t) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t)))
  exact integral_dirLoss_eq_dotJ (u := a t) _ hh

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **The total information moves by the covariance of the tilt with the data velocity**:
`d/dt KL(ρ_t ‖ ν) = Cov_{ρ_t}(g_t, ġ_t)`. -/
theorem hasDerivAt_totalInfo_coeff (t₀ : ℝ) :
    HasDerivAt (fun t ↦ totalInfo ν (dirLoss h (a t)))
      (lawCov (ν.tilted (dirLoss h (a t₀))) (dirLoss h (a t₀)) (dirLoss h (a' t₀))) t₀ := by
  have hP : ∀ t, IsProbabilityMeasure (ν.tilted (dirLoss h (a t))) := fun t ↦
    isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t)))
  have e : (fun t ↦ totalInfo ν (dirLoss h (a t))) = fun t ↦
      dotJ (a t) (coeffMean h ν h a t) -
        Real.log (∫ x, (1 : ℝ) * Real.exp (dirLoss h (a t) x) ∂ν) := by
    funext t
    rw [totalInfo_eq hS ν (bdd_dirLoss hh (a t)), integral_dirLoss_self_eq_dotJ ν hh]
    simp only [one_mul]
  rw [e]
  have hZ : 0 < ∫ x, (1 : ℝ) * Real.exp (dirLoss h (a t₀) x) ∂ν := by
    simp only [one_mul]
    exact integral_exp_pos (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t₀)))
  have h1 := hasDerivAt_dotJ (ha t₀) (hasDerivAt_coeffMean hh ν hh ha ha' t₀)
  have h2 := (hasDerivAt_integral_mul_exp_dirLoss ν hh ha ha' (Bdd.const (1 : ℝ)) t₀).log hZ.ne'
  refine (h1.sub h2).congr_deriv ?_
  -- the log-partition derivative is the expectation of the data velocity
  have hE : (∫ x, (1 : ℝ) * Real.exp (dirLoss h (a t₀) x) * dirLoss h (a' t₀) x ∂ν) /
      ∫ x, (1 : ℝ) * Real.exp (dirLoss h (a t₀) x) ∂ν = dotJ (a' t₀) (coeffMean h ν h a t₀) := by
    rw [← integral_dirLoss_deriv_eq_dotJ ν hh t₀, integral_tilted_dirLoss_eq_div ν]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [hE, lawCov_dirLoss_left hh (ν.tilted (dirLoss h (a t₀))) _ _ (bdd_dirLoss hh (a' t₀))]
  simp only [forcing, dotJ]
  ring

/-- The response along the path, coerced to the coordinate space, is differentiable. -/
theorem hasDerivAt_coeffResponse_coe (t₀ : ℝ) :
    HasDerivAt (fun t ↦ (coeffResponse hS ν h a t : J → ℝ))
      (responseVel hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a' t₀)) : J → ℝ) t₀ := by
  have hd := (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t₀
    (hasDerivAt_coeffResponse hS ν hh ha ha' t₀)
  exact hd

omit ha ha' in
/-- The response matches the data means along the path. -/
theorem meanMap_coeffResponse (t : ℝ) :
    mean (coeffResponse hS ν h a t : J → ℝ) = coeffMean S ν h a t :=
  ((responseOf_eq_iff_tiltedMean_eq_meanMap hS ν (bdd_dirLoss hh (a t)) _).1 rfl).symm

/-- **The response information moves by the pairing of the response with the mean velocity**:
`d/dt KL(P_{Φ(g_t)} ‖ ν) = −⟨θ_t, δμ_t⟩`, `δμ_t = Cov_{ρ_t}(S, ġ_t)`. -/
theorem hasDerivAt_responseInfo_coeff (t₀ : ℝ) :
    HasDerivAt (fun t ↦ responseInfo hS ν (dirLoss h (a t)))
      (-dotJ (coeffResponse hS ν h a t₀ : J → ℝ)
        (forcing S ν (dirLoss h (a t₀)) (dirLoss h (a' t₀)))) t₀ := by
  have e : (fun t ↦ responseInfo hS ν (dirLoss h (a t))) = fun t ↦
      -dotJ (coeffResponse hS ν h a t : J → ℝ) (coeffMean S ν h a t) -
        Real.log (famZ S ν (coeffResponse hS ν h a t : J → ℝ)) := by
    funext t
    unfold responseInfo
    rw [toReal_klDiv_model_featureless hS ν]
    have hm := meanMap_coeffResponse hS ν hh (a := a) t
    unfold coeffResponse at hm
    rw [hm]
    rfl
  rw [e]
  have h1 := hasDerivAt_dotJ (hasDerivAt_coeffResponse_coe hS ν hh ha ha' t₀)
    (hasDerivAt_coeffMean hS ν hh ha ha' t₀)
  have h2 := ((hasFDerivAt_famZ hS ν (coeffResponse hS ν h a t₀ : J → ℝ)).log
    (famZ_pos hS ν _).ne').comp_hasDerivAt t₀ (hasDerivAt_coeffResponse_coe hS ν hh ha ha' t₀)
  refine (h1.neg.sub h2).congr_deriv ?_
  simp only [smul_apply, smul_eq_mul, dotCLM_apply, famMean_eq_meanMap hS ν,
    meanMap_coeffResponse hS ν hh (a := a) t₀]
  have hZ : (famZ S ν (coeffResponse hS ν h a t₀ : J → ℝ))⁻¹ *
      (-famZ S ν (coeffResponse hS ν h a t₀ : J → ℝ)) = -1 := by
    rw [mul_neg, inv_mul_cancel₀ (famZ_pos hS ν _).ne']
  rw [← mul_assoc, hZ]
  ring

/-- **The defect moves by the covariance of the data velocity with the log-likelihood ratio**
`g_t + ⟨θ_t, S⟩` of the data law against its information projection:
`d/dt KL(ρ_t ‖ P_{Φ(g_t)}) = Cov_{ρ_t}(g_t + ⟨θ_t, S⟩, ġ_t)`. -/
theorem hasDerivAt_defect_coeff (t₀ : ℝ) :
    HasDerivAt (fun t ↦ responseInformationDefect hS ν (dirLoss h (a t)))
      (lawCov (ν.tilted (dirLoss h (a t₀)))
        (fun x ↦ dirLoss h (a t₀) x + dirLoss S (coeffResponse hS ν h a t₀ : J → ℝ) x)
        (dirLoss h (a' t₀))) t₀ := by
  have hP := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t₀)))
  have e : (fun t ↦ responseInformationDefect hS ν (dirLoss h (a t))) = fun t ↦
      totalInfo ν (dirLoss h (a t)) - responseInfo hS ν (dirLoss h (a t)) := by
    funext t
    rw [totalInfo_eq_defect_add_responseInfo hS ν (bdd_dirLoss hh (a t))]
    ring
  rw [e]
  refine ((hasDerivAt_totalInfo_coeff hS ν hh ha ha' t₀).sub
    (hasDerivAt_responseInfo_coeff hS ν hh ha ha' t₀)).congr_deriv ?_
  rw [lawCov_add_left_eq _ (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hS _) (bdd_dirLoss hh (a' t₀)),
    lawCov_dirLoss_left hS (ν.tilted (dirLoss h (a t₀))) _ _ (bdd_dirLoss hh (a' t₀))]
  simp only [forcing, dotJ]
  ring

end Derivatives

end Laplace.Multi
