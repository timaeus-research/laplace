/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFibreDeformation
import Laplace.Multi.ProjectionPythagoras
import Laplace.Multi.EntropyProjection
import Laplace.Multi.MixtureBridge
import Laplace.Multi.FiniteResponse

/-!
# The response as an information projection: the KL Pythagorean theorem

For a bounded tilt `g` with law `ρ_g = ν.tilted g` and a model law `P_θ = ν.tilted(−⟨θ,S⟩)`,

  `KL(ρ_g ‖ P_θ) = KL(ρ_g ‖ P_{Φ(g)}) + KL(P_{Φ(g)} ‖ P_θ)`   (`toReal_klDiv_pythagoras`),

because the log-ratio of two model densities is affine in `S` and the response `Φ(g)` matches the
moments of `ρ_g`. Hence the model law `P_{Φ(g)}` is the **unique** information projection of the
data law onto the family (`toReal_klDiv_model_ge`, `toReal_klDiv_model_eq_iff`), and the
**information defect** `KL(ρ_g ‖ P_{Φ(g)})` (`responseInformationDefect`) is the information
invisible to the response: it vanishes exactly when the data law is a model law
(`responseInformationDefect_eq_zero_iff`). Along the mixture deformation toward the model law the
defect decreases at least linearly (`responseInformationDefect_mix_le`), by convexity of the
divergence in its first argument.

The featureless case `θ = 0` is the global information decomposition

  `KL(ρ_g ‖ ν) = KL(ρ_g ‖ P_{Φ(g)}) + KL(P_{Φ(g)} ‖ ν)`
  (`toReal_klDiv_pythagoras_featureless`):

the total information of a data law relative to the featureless law splits exactly into the part
invisible to the response and the part retained by the structural coordinate.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Tilt

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The divergence of a bounded tilt to the reference law is finite. -/
theorem klDiv_tilted_ne_top {g : X → ℝ} (hg : Bdd g) : klDiv (ν.tilted g) ν ≠ ⊤ := by
  rw [klDiv_tilted_eq ν hg]
  exact ENNReal.ofReal_ne_top

/-- **The divergence between two bounded tilts**:
`KL(ρ_g ‖ ρ_h) = E_{ρ_g}(g − h) − log Z_g + log Z_h`. -/
theorem toReal_klDiv_tilted_tilted {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h) :
    (klDiv (ν.tilted g) (ν.tilted h)).toReal =
      ∫ x, (g x - h x) ∂ν.tilted g - Real.log (∫ x, Real.exp (g x) ∂ν) +
        Real.log (∫ x, Real.exp (h x) ∂ν) := by
  have hprob := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have h1 := toReal_klDiv_tilted_right ν (ν.tilted g) (tilted_absolutelyContinuous ν g)
    (klDiv_tilted_ne_top ν hg) hh
  have h0 := toReal_klDiv_tilted_right ν (ν.tilted g) (tilted_absolutelyContinuous ν g)
    (klDiv_tilted_ne_top ν hg) hg
  rw [klDiv_self, ENNReal.toReal_zero] at h0
  rw [h1, integral_sub (integrable_of_bdd_prob _ hg) (integrable_of_bdd_prob _ hh)]
  linarith

theorem klDiv_tilted_tilted_ne_top {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h) :
    klDiv (ν.tilted g) (ν.tilted h) ≠ ⊤ := by
  have hprob := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  rw [klDiv_tilted_right_eq ν (ν.tilted g) (tilted_absolutelyContinuous ν g)
    (klDiv_tilted_ne_top ν hg) hh]
  exact ENNReal.ofReal_ne_top

/-- **The law of the mixture tilt is the mixture of the laws.** -/
theorem tilted_mixTilt {g h : X → ℝ} (hg : Bdd g) (hh : Bdd h) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ν.tilted (mixTilt ν g h t) =
      (Real.toNNReal (1 - t)) • ν.tilted g + (Real.toNNReal t) • ν.tilted h := by
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, tilted_apply' ν _ hs,
    tilted_apply' ν _ hs, tilted_apply' ν _ hs]
  have e : ∀ x, ENNReal.ofReal (Real.exp (mixTilt ν g h t x) /
      ∫ y, Real.exp (mixTilt ν g h t y) ∂ν) =
      ENNReal.ofReal (1 - t) * ENNReal.ofReal (Real.exp (g x) / ∫ y, Real.exp (g y) ∂ν) +
        ENNReal.ofReal t * ENNReal.ofReal (Real.exp (h x) / ∫ y, Real.exp (h y) ∂ν) := by
    intro x
    have := congrFun (normDens_mixTilt ν hg hh ht0 ht1) x
    change normDens ν (mixTilt ν g h t) x = _ at this
    change ENNReal.ofReal (normDens ν (mixTilt ν g h t) x) = _
    rw [this, ENNReal.ofReal_add (mul_nonneg (by linarith) (normDens_pos ν hg x).le)
      (mul_nonneg ht0 (normDens_pos ν hh x).le), ENNReal.ofReal_mul (by linarith),
      ENNReal.ofReal_mul ht0]
    rfl
  simp only [e]
  have hmg : Measurable fun a ↦ ENNReal.ofReal (Real.exp (g a) / ∫ y, Real.exp (g y) ∂ν) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hg.1).div_const _)
  have hmh : Measurable fun a ↦ ENNReal.ofReal (Real.exp (h a) / ∫ y, Real.exp (h y) ∂ν) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hh.1).div_const _)
  have hmg' : Measurable fun a ↦
      ENNReal.ofReal (1 - t) * ENNReal.ofReal (Real.exp (g a) / ∫ y, Real.exp (g y) ∂ν) :=
    measurable_const.mul hmg
  rw [lintegral_add_left hmg', lintegral_const_mul _ hmg, lintegral_const_mul _ hmh]
  rfl

end Tilt

section Pythagoras

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The normaliser of the model tilt is the partition function. -/
theorem integral_exp_modelTilt (θ : J → ℝ) :
    ∫ x, Real.exp (modelTilt S θ x) ∂ν = famZ S ν θ := by
  simp only [modelTilt, famZ, famWeight, neg_one_mul]

omit [Nonempty X] [Nonempty J] in
/-- The expectation of the model tilt under a law is minus the pairing with its moments. -/
theorem integral_modelTilt (θ : J → ℝ) (ρ : Measure X) [IsProbabilityMeasure ρ] :
    ∫ x, modelTilt S θ x ∂ρ = -dotJ θ (fun i ↦ ∫ x, S i x ∂ρ) := by
  simp only [modelTilt, dirLoss, neg_one_mul, dotJ]
  rw [integral_neg, integral_finsetSum _ fun i _ ↦ (integrable_of_bdd_prob ρ (hS i)).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ integral_const_mul _ _

omit [Nonempty J] in
/-- **The divergence of a data law to a model law**:
`KL(ρ_g ‖ P_θ) = E_{ρ_g} g − log Z_g + ⟨θ, E_{ρ_g} S⟩ + log Z(θ)`. -/
theorem toReal_klDiv_tilted_model {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) :
    (klDiv (ν.tilted g) (Pfam θ)).toReal =
      ∫ x, g x ∂ν.tilted g - Real.log (∫ x, Real.exp (g x) ∂ν) + dotJ θ (tiltedMean S ν g) +
        Real.log (famZ S ν θ) := by
  have hprob := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  rw [← tilted_modelTilt hS ν θ, toReal_klDiv_tilted_tilted ν hg (bdd_modelTilt hS θ),
    integral_sub (integrable_of_bdd_prob _ hg) (integrable_of_bdd_prob _ (bdd_modelTilt hS θ)),
    integral_modelTilt hS θ, integral_exp_modelTilt]
  unfold tiltedMean
  ring

omit [Nonempty J] in
/-- The divergence of a model law to the reference law: `KL(P_θ ‖ ν) = −⟨θ, m(θ)⟩ − log Z(θ)`. -/
theorem toReal_klDiv_model_featureless (θ : J → ℝ) :
    (klDiv (Pfam θ) ν).toReal = -dotJ θ (mean θ) - Real.log (famZ S ν θ) := by
  have hprob := isProbabilityMeasure_family hS ν θ
  have e0 : ν.tilted (fun _ : X ↦ (0 : ℝ)) = ν := by simp
  have h := toReal_klDiv_tilted_tilted ν (bdd_modelTilt hS θ) (Bdd.const (0 : ℝ))
  rw [e0, tilted_modelTilt hS ν θ] at h
  rw [h, integral_sub (integrable_of_bdd_prob _ (bdd_modelTilt hS θ)) (integrable_const _),
    integral_modelTilt hS θ, mean_familyMeasure_one_zero hS ν θ, integral_exp_modelTilt]
  simp

omit [Nonempty J] in
/-- **The Bregman form of the divergence between two model laws**:
`KL(P_θ ‖ P_η) = ⟨η − θ, m(θ)⟩ + log Z(η) − log Z(θ)`. -/
theorem toReal_klDiv_model_model (θ η : J → ℝ) :
    (klDiv (Pfam θ) (Pfam η)).toReal =
      dotJ (η - θ) (mean θ) + Real.log (famZ S ν η) - Real.log (famZ S ν θ) := by
  have hprob := isProbabilityMeasure_family hS ν θ
  rw [← tilted_modelTilt hS ν θ, toReal_klDiv_tilted_model hS ν (bdd_modelTilt hS θ) η,
    tilted_modelTilt hS ν θ, integral_modelTilt hS θ, mean_familyMeasure_one_zero hS ν θ,
    integral_exp_modelTilt, tiltedMean_modelTilt hS ν θ, dotJ_sub_left]
  ring

/-- **The KL Pythagorean theorem of the response map**:
`KL(ρ_g ‖ P_θ) = KL(ρ_g ‖ P_{Φ(g)}) + KL(P_{Φ(g)} ‖ P_θ)`. -/
theorem toReal_klDiv_pythagoras {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) :
    (klDiv (ν.tilted g) (Pfam θ)).toReal =
      (klDiv (ν.tilted g) (Pfam (responseOf hS ν g : J → ℝ))).toReal +
        (klDiv (Pfam (responseOf hS ν g : J → ℝ)) (Pfam θ)).toReal := by
  have hmatch : tiltedMean S ν g = mean (responseOf hS ν g : J → ℝ) :=
    (responseOf_eq_iff_tiltedMean_eq_meanMap hS ν hg _).1 rfl
  rw [toReal_klDiv_tilted_model hS ν hg, toReal_klDiv_tilted_model hS ν hg,
    toReal_klDiv_model_model hS ν, hmatch, dotJ_sub_left]
  ring

/-- **The global information decomposition**: the information of a data law relative to the
featureless law splits into the part invisible to the response and the part it retains,
`KL(ρ_g ‖ ν) = KL(ρ_g ‖ P_{Φ(g)}) + KL(P_{Φ(g)} ‖ ν)`. -/
theorem toReal_klDiv_pythagoras_featureless {g : X → ℝ} (hg : Bdd g) :
    (klDiv (ν.tilted g) ν).toReal =
      (klDiv (ν.tilted g) (Pfam (responseOf hS ν g : J → ℝ))).toReal +
        (klDiv (Pfam (responseOf hS ν g : J → ℝ)) ν).toReal := by
  have h := toReal_klDiv_pythagoras hS ν hg 0
  rwa [familyMeasure_zero_eq hS ν] at h

/-- The model law with the matched moments is the closest model law. -/
theorem toReal_klDiv_model_ge {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) :
    (klDiv (ν.tilted g) (Pfam (responseOf hS ν g : J → ℝ))).toReal ≤
      (klDiv (ν.tilted g) (Pfam θ)).toReal := by
  rw [toReal_klDiv_pythagoras hS ν hg θ]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

/-- The family is injective in the natural coordinates of the direction space. -/
theorem familyMeasure_injective_dirSpan {θ η : 𝕍} (h : Pfam (θ : J → ℝ) = Pfam (η : J → ℝ)) :
    θ = η := by
  have hm : mean (θ : J → ℝ) = mean (η : J → ℝ) := by
    rw [← mean_familyMeasure_one_zero hS ν, ← mean_familyMeasure_one_zero hS ν, h]
  rw [← responseTheta_meanMap hS ν θ, ← responseTheta_meanMap hS ν η, hm]

theorem klDiv_model_model_eq_zero_iff (θ η : 𝕍) :
    klDiv (Pfam (θ : J → ℝ)) (Pfam (η : J → ℝ)) = 0 ↔ θ = η := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have := isProbabilityMeasure_family hS ν (η : J → ℝ)
  rw [klDiv_eq_zero_iff]
  exact ⟨familyMeasure_injective_dirSpan hS ν, fun h ↦ by rw [h]⟩

omit [Nonempty J] in
theorem klDiv_tilted_model_ne_top {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) :
    klDiv (ν.tilted g) (Pfam θ) ≠ ⊤ := by
  rw [← tilted_modelTilt hS ν θ]
  exact klDiv_tilted_tilted_ne_top ν hg (bdd_modelTilt hS θ)

omit [Nonempty J] in
theorem klDiv_model_model_ne_top (θ η : J → ℝ) : klDiv (Pfam θ) (Pfam η) ≠ ⊤ := by
  rw [← tilted_modelTilt hS ν θ, ← tilted_modelTilt hS ν η]
  exact klDiv_tilted_tilted_ne_top ν (bdd_modelTilt hS θ) (bdd_modelTilt hS η)

/-- **Uniqueness of the information projection**: a model law is closest to the data law exactly
when it is the response. -/
theorem toReal_klDiv_model_eq_iff {g : X → ℝ} (hg : Bdd g) (θ : 𝕍) :
    (klDiv (ν.tilted g) (Pfam (θ : J → ℝ))).toReal =
        (klDiv (ν.tilted g) (Pfam (responseOf hS ν g : J → ℝ))).toReal ↔
      θ = responseOf hS ν g := by
  rw [toReal_klDiv_pythagoras hS ν hg θ]
  constructor
  · intro h
    have h0 : (klDiv (Pfam (responseOf hS ν g : J → ℝ)) (Pfam (θ : J → ℝ))).toReal = 0 := by
      linarith
    rw [ENNReal.toReal_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact ((klDiv_model_model_eq_zero_iff hS ν _ _).1 h0).symm
    · exact absurd h0 (klDiv_model_model_ne_top hS ν _ _)
  · intro h
    have := isProbabilityMeasure_family hS ν (responseOf hS ν g : J → ℝ)
    rw [h, klDiv_self, ENNReal.toReal_zero, add_zero]

/-- **The information defect of a data law**: the divergence to its information projection,
`KL(ρ_g ‖ P_{Φ(g)})`, the information invisible to the response. -/
noncomputable def responseInformationDefect (g : X → ℝ) : ℝ :=
  (klDiv (ν.tilted g) (Pfam (responseOf hS ν g : J → ℝ))).toReal

theorem responseInformationDefect_nonneg (g : X → ℝ) : 0 ≤ responseInformationDefect hS ν g :=
  ENNReal.toReal_nonneg

/-- The defect vanishes exactly when the data law is a model law. -/
theorem responseInformationDefect_eq_zero_iff {g : X → ℝ} (hg : Bdd g) :
    responseInformationDefect hS ν g = 0 ↔
      ν.tilted g = Pfam (responseOf hS ν g : J → ℝ) := by
  unfold responseInformationDefect
  have hprob := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have hprob' := isProbabilityMeasure_family hS ν (responseOf hS ν g : J → ℝ)
  rw [ENNReal.toReal_eq_zero_iff, klDiv_eq_zero_iff]
  exact ⟨fun h ↦ h.resolve_right (klDiv_tilted_model_ne_top hS ν hg _), fun h ↦ Or.inl h⟩

/-- Model laws have no defect. -/
theorem responseInformationDefect_modelTilt (θ : 𝕍) :
    responseInformationDefect hS ν (modelTilt S (θ : J → ℝ)) = 0 := by
  unfold responseInformationDefect
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  rw [responseOf_modelTilt hS ν θ, tilted_modelTilt hS ν, klDiv_self, ENNReal.toReal_zero]

/-- **The mixture deformation dissipates the invisible information**: along the mixture segment
from a data law to its information projection the defect decreases at least linearly,
`KL(ρ_t ‖ P_{Φ}) ≤ (1 − t) KL(ρ_g ‖ P_{Φ})`. -/
theorem responseInformationDefect_mix_le {g : X → ℝ} (hg : Bdd g) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    responseInformationDefect hS ν (mixTilt ν g (modelTilt S (responseOf hS ν g : J → ℝ)) t) ≤
      (1 - t) * responseInformationDefect hS ν g := by
  unfold responseInformationDefect
  have hΦ := responseOf_mixTilt_of_eq hS ν hg (bdd_modelTilt hS _)
    (responseOf_modelTilt hS ν _).symm ht0 ht1
  rw [hΦ, tilted_mixTilt ν hg (bdd_modelTilt hS _) ht0 ht1, tilted_modelTilt hS ν]
  have hprobg := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have hprobΦ := isProbabilityMeasure_family hS ν (responseOf hS ν g : J → ℝ)
  have hab : Real.toNNReal (1 - t) + Real.toNNReal t = 1 := by
    rw [← Real.toNNReal_add (by linarith) ht0, sub_add_cancel, Real.toNNReal_one]
  have hac : ν.tilted g ≪ Pfam (responseOf hS ν g : J → ℝ) := by
    refine (tilted_absolutelyContinuous ν g).trans ?_
    rw [← tilted_modelTilt hS ν]
    exact absolutelyContinuous_tilted (integrable_exp_of_bdd ν (bdd_modelTilt hS _))
  have h := klDiv_mixture_le (ν := Pfam (responseOf hS ν g : J → ℝ)) (ν.tilted g) _ hac
    Measure.AbsolutelyContinuous.rfl hab
  rw [klDiv_self, mul_zero, add_zero] at h
  have hfin := klDiv_tilted_model_ne_top hS ν hg (responseOf hS ν g : J → ℝ)
  calc (klDiv ((Real.toNNReal (1 - t)) • ν.tilted g +
        (Real.toNNReal t) • Pfam (responseOf hS ν g : J → ℝ))
        (Pfam (responseOf hS ν g : J → ℝ))).toReal
      ≤ ((Real.toNNReal (1 - t) : ℝ≥0∞) *
          klDiv (ν.tilted g) (Pfam (responseOf hS ν g : J → ℝ))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) h
    _ = (1 - t) * (klDiv (ν.tilted g) (Pfam (responseOf hS ν g : J → ℝ))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal _ (by linarith)]

end Pythagoras

end Laplace.Multi
