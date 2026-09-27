/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiltVarianceComparison
import Laplace.Multi.RayFisherLengthClassification

/-!
# Accessibility is independent of the tangential lift

Two natural rays `v − r u` and `w − r u` with the same normal `u` differ, for every `r`, by the
fixed bounded tilt `−⟨v − w, S⟩`. By the variance comparison under bounded tilts their Fisher
speeds are comparable within constants independent of `r` (`raySpeedSq_tilt_comparable`), so one
ray has finite Fisher length iff the other does (`lintegral_sqrt_raySpeedSq_lt_top_iff_tilt`).
Consequently accessibility of a face by its normal rays is a property of the face, not of the
particular point of its relative interior: it is all-or-nothing on `ri F`.
-/

open MeasureTheory Set Real

namespace Laplace.Multi

section RayTilt

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family law of `v − r u` is the family law of `w − r u` tilted by `−⟨v − w, S⟩`. -/
theorem familyMeasure_sub_smul_eq_tilted (v w u : J → ℝ) (r : ℝ) :
    familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v - r • u) =
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (w - r • u)).tilted
        (fun x ↦ -(dirLoss S (v - w) x)) := by
  rw [familyMeasure_one_zero_eq_tilted hS ν, familyMeasure_one_zero_eq_tilted hS ν,
    tilted_tilted (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))]
  congr 1
  funext x
  simp only [Pi.add_apply, dirLoss_sub', dirLoss_smul]
  ring

/-- **Ray speeds of two rays with the same normal are comparable**, uniformly in `r`. -/
theorem raySpeedSq_tilt_comparable (v w u : J → ℝ) {c : ℝ}
    (hc : ∀ x, |dirLoss S (v - w) x| ≤ c) (r : ℝ) :
    exp (-(2 * c)) * raySpeedSq S ν w u r ≤ raySpeedSq S ν v u r ∧
      raySpeedSq S ν v u r ≤ exp (2 * c) * raySpeedSq S ν w u r := by
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (w - r • u)) := by
    rw [familyMeasure_one_zero_eq_tilted hS ν]
    exact isProbabilityMeasure_tilted (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))
  have hg : Bdd fun x ↦ -(dirLoss S (v - w) x) := bdd_neg (bdd_dirLoss hS _)
  have hc' : ∀ x, |(fun x ↦ -(dirLoss S (v - w) x)) x| ≤ c := fun x ↦ by
    rw [abs_neg]; exact hc x
  unfold raySpeedSq
  rw [familyMeasure_sub_smul_eq_tilted hS ν v w u r]
  exact ⟨le_lawCov_tilted _ hg hc' (bdd_dirLoss hS u), lawCov_tilted_le _ hg hc' (bdd_dirLoss hS u)⟩

/-- Ray speeds are dominated by the tilt-comparison constant. -/
theorem sqrt_raySpeedSq_le_tilt (v w u : J → ℝ) {c : ℝ} (hc : ∀ x, |dirLoss S (v - w) x| ≤ c)
    (r : ℝ) : √(raySpeedSq S ν v u r) ≤ exp c * √(raySpeedSq S ν w u r) := by
  have h := (raySpeedSq_tilt_comparable hS ν v w u hc r).2
  calc √(raySpeedSq S ν v u r) ≤ √(exp (2 * c) * raySpeedSq S ν w u r) := Real.sqrt_le_sqrt h
    _ = exp c * √(raySpeedSq S ν w u r) := by
      rw [Real.sqrt_mul (exp_pos _).le, show exp (2 * c) = exp c ^ 2 by rw [← exp_nat_mul]; ring_nf,
        Real.sqrt_sq (exp_pos _).le]

/-- **Finite Fisher length of a ray is independent of the tangential lift.** -/
theorem lintegral_sqrt_raySpeedSq_lt_top_of_tilt (v w u : J → ℝ) {c : ℝ}
    (hc : ∀ x, |dirLoss S (v - w) x| ≤ c)
    (hw : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν w u r))) < ⊤) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν v u r))) < ⊤ := by
  calc (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν v u r)))
      ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (exp c) * ENNReal.ofReal (√(raySpeedSq S ν w u r)) := by
        refine lintegral_mono fun r ↦ ?_
        rw [← ENNReal.ofReal_mul (exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (sqrt_raySpeedSq_le_tilt hS ν v w u hc r)
    _ = ENNReal.ofReal (exp c) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν w u r)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw

/-- **Accessibility is all-or-nothing**: for any two tangential lifts the rays have finite Fisher
length together. -/
theorem lintegral_sqrt_raySpeedSq_lt_top_iff_tilt (v w u : J → ℝ) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν v u r))) < ⊤ ↔
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν w u r))) < ⊤ := by
  obtain ⟨-, c, hc⟩ := bdd_dirLoss hS (v - w)
  have hc' : ∀ x, |dirLoss S (w - v) x| ≤ c := fun x ↦ by
    rw [show w - v = -(v - w) by abel, dirLoss_neg, abs_neg]
    exact hc x
  exact ⟨lintegral_sqrt_raySpeedSq_lt_top_of_tilt hS ν w v u hc',
    lintegral_sqrt_raySpeedSq_lt_top_of_tilt hS ν v w u hc⟩

end RayTilt

end Laplace.Multi
