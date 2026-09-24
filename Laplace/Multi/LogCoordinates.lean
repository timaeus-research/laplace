/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TwoScaledInner

/-!
# Logarithmic coordinates on the box

The substitution `x = ρ e^{-z}` from the positive orthant `z > 0` onto the open box `(0, ρ)^n`:
`∫_{(0,ρ)^n} F(x) dx = ∫_{z > 0} (∏ ρ e^{-z_i}) F(ρ e^{-z}) dz` (`integral_box_eq_orthant`) and
the corresponding integrability transfer (`integrableOn_box_iff_orthant`). This is the first step
of the transverse active-truth face theorem (`notes/active_truth_handoff.md`): in the coordinates
`z = −log(x/ρ)` the model integrand becomes `e^{-c·z}` times a Boltzmann factor in `e^{-κ·z}` and
the truth cut becomes a half-space.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The map `z ↦ ρ e^{-z}`, coordinatewise. -/
noncomputable def negExpMap (ρ : ℝ) (z : ι → ℝ) : ι → ℝ := fun i ↦ ρ * exp (-z i)

/-- Its derivative: the diagonal matrix `−ρ e^{-z_i}`. -/
noncomputable def negExpDeriv (ρ : ℝ) (z : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal fun i ↦ -(ρ * exp (-z i))))

theorem hasFDerivAt_negExpMap (ρ : ℝ) (z : ι → ℝ) :
    HasFDerivAt (negExpMap ρ) (negExpDeriv ρ z) z := by
  refine hasFDerivAt_pi'.mpr fun i ↦ ?_
  refine (((hasFDerivAt_apply (𝕜 := ℝ) i z).neg.exp).const_mul ρ).congr_fderiv ?_
  ext w
  simp [negExpDeriv, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  ring

theorem det_negExpDeriv (ρ : ℝ) (z : ι → ℝ) :
    (negExpDeriv ρ z).det = ∏ i, -(ρ * exp (-z i)) := by
  rw [ContinuousLinearMap.det, negExpDeriv, LinearMap.coe_toContinuousLinearMap,
    LinearMap.det_toLin', Matrix.det_diagonal]

theorem abs_det_negExpDeriv {ρ : ℝ} (hρ : 0 < ρ) (z : ι → ℝ) :
    |(negExpDeriv ρ z).det| = ∏ i, ρ * exp (-z i) := by
  rw [det_negExpDeriv, Finset.abs_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [abs_neg, abs_of_pos (by positivity)]

omit [Fintype ι] [DecidableEq ι] in
theorem negExpMap_injective {ρ : ℝ} (hρ : 0 < ρ) : Function.Injective (negExpMap (ι := ι) ρ) := by
  intro w w' h
  funext i
  have := congrFun h i
  simp only [negExpMap] at this
  have h2 := exp_injective (mul_left_cancel₀ hρ.ne' this)
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- The image of the open orthant is the open box `(0, ρ)^ι`. -/
theorem image_negExpMap_orthant {ρ : ℝ} (hρ : 0 < ρ) :
    negExpMap ρ '' (Set.pi univ fun _ : ι ↦ Ioi (0 : ℝ)) = Set.pi univ fun _ ↦ Ioo (0 : ℝ) ρ := by
  ext x
  simp only [Set.mem_image, Set.mem_univ_pi, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    simp only [negExpMap]
    refine ⟨by positivity, ?_⟩
    have : exp (-z i) < 1 := by
      have h := exp_lt_exp.mpr (show -z i < 0 by linarith [hz i])
      rwa [exp_zero] at h
    nlinarith
  · intro hx
    refine ⟨fun i ↦ -log (x i / ρ), fun i ↦ ?_, funext fun i ↦ ?_⟩
    · have : x i / ρ < 1 := (div_lt_one hρ).mpr (hx i).2
      have hpos : 0 < x i / ρ := div_pos (hx i).1 hρ
      linarith [Real.log_neg hpos this]
    · simp only [negExpMap, neg_neg]
      rw [exp_log (div_pos (hx i).1 hρ), mul_div_cancel₀ _ hρ.ne']

omit [DecidableEq ι] in
/-- **The logarithmic substitution on the box**:
`∫_{(0,ρ)^ι} F = ∫_{z > 0} (∏ ρ e^{-z_i}) F(ρ e^{-z})`. -/
theorem integral_box_eq_orthant {ρ : ℝ} (hρ : 0 < ρ) (F : (ι → ℝ) → ℝ) :
    ∫ x in Set.pi univ (fun _ : ι ↦ Ioo (0 : ℝ) ρ), F x =
      ∫ z in Set.pi univ (fun _ : ι ↦ Ioi (0 : ℝ)), (∏ i, ρ * exp (-z i)) * F (negExpMap ρ z) := by
  classical
  rw [← image_negExpMap_orthant hρ, integral_image_eq_integral_abs_det_fderiv_smul volume
    (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    (fun z _ ↦ (hasFDerivAt_negExpMap ρ z).hasFDerivWithinAt) (negExpMap_injective hρ).injOn F]
  refine setIntegral_congr_fun (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    fun z _ ↦ ?_
  rw [abs_det_negExpDeriv hρ, smul_eq_mul]

omit [DecidableEq ι] in
/-- Integrability transfers along the logarithmic substitution. -/
theorem integrableOn_box_iff_orthant {ρ : ℝ} (hρ : 0 < ρ) (F : (ι → ℝ) → ℝ) :
    IntegrableOn F (Set.pi univ (fun _ : ι ↦ Ioo (0 : ℝ) ρ)) ↔
      IntegrableOn (fun z ↦ (∏ i, ρ * exp (-z i)) * F (negExpMap ρ z))
        (Set.pi univ (fun _ : ι ↦ Ioi (0 : ℝ))) := by
  classical
  rw [← image_negExpMap_orthant hρ, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    (fun z _ ↦ (hasFDerivAt_negExpMap ρ z).hasFDerivWithinAt) (negExpMap_injective hρ).injOn F]
  refine integrableOn_congr_fun (fun z _ ↦ ?_)
    (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
  rw [abs_det_negExpDeriv hρ, smul_eq_mul]

end Laplace.Multi
