/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponsePullbackVariation
import Laplace.Multi.ResponseDefectEvolution
import Laplace.Multi.ResponseAtFeaturelessLaw

/-!
# The third derivative of the response defect

Along the exponential data journey `ρ_t = ν.tilted (t h)` the response defect `Δ(t) = D(ρ_t ‖
P_{Φ(ρ_t)})` (the KL distance from the data law to its own fitted response law) is `Δ(0) = Δ'(0) =
0` and `Δ''(0) = Var_ν(h − r)` with `r = ⟨−θ'_0, S⟩` the regressor (the part of `h` seen by the
statistics). This module computes the next term. With `v = θ'_0` the initial response velocity and
`L_v = ⟨v, S⟩`,

`Δ'''(0) = 2 κ_ν(h,h,h) + 3 κ_ν(h,h,L_v) − κ_ν(L_v,L_v,L_v)`

(`hasDerivAt_deriv_deriv_responseDefect_zero`, `deriv_deriv_deriv_responseDefect_zero`); in terms
of the residual `e = h − r = h + L_v` this is `2κ(e,e,e) + 3κ(e,e,r)`
(`deriv_deriv_deriv_responseDefect_zero_residual`). The factor two matters: the third defect
derivative is not simply the third cumulant of the residual.

The proof differentiates the every-`t` second-derivative formula of `ResponseDefectEvolution`,
`Δ''(t) = Var_{ρ_t}h − |θ'_t|²_F + Cov_{ρ_t}((h − E h)², t h + ⟨θ_t,S⟩)`, at `t = 0`: the variance
moves by the third cumulant (`hasDerivAt_var_tilted`); the response speed² is the pulled-back form
of the journey, whose variation is `ResponsePullbackVariation` (`hasDerivAt_responseSpeedSq`); and
the last covariance is `t κ_{ρ_t}(h,h,h) + ∑ θ_{t,i} κ_{ρ_t}(h,h,S_i)` (`defectBracket_eq`), a
product whose first factors vanish at `0`, so only the derivative of those factors survives
(`hasDerivAt_mul_of_eq_zero`, needing only continuity of the third cumulants along the path,
`continuous_thirdCentral_tilted`). No fourth cumulant enters.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Slope

/-- A product `u · w` with `u t₀ = 0`, `u` differentiable and `w` merely continuous at `t₀` is
differentiable at `t₀`, with derivative `u'(t₀) w(t₀)`. -/
theorem hasDerivAt_mul_of_eq_zero {u w : ℝ → ℝ} {u' t₀ : ℝ} (hu : HasDerivAt u u' t₀)
    (hu0 : u t₀ = 0) (hw : ContinuousAt w t₀) :
    HasDerivAt (fun t ↦ u t * w t) (u' * w t₀) t₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hu ⊢
  refine (hu.mul (hw.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  simp only [slope_def_field, hu0, sub_zero, zero_mul, div_mul_eq_mul_div]

end Slope

section ThirdContinuity

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- Expectations of bounded observables are continuous along an exponential tilt. -/
theorem continuous_integral_tilted_mul {f φ : X → ℝ} (hf : Bdd f) (hφ : Bdd φ) :
    Continuous fun t ↦ ∫ x, φ x ∂ν.tilted (fun x ↦ t * f x) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_integral_tilted ν hf hφ t).continuousAt

/-- **Third cumulants are continuous along an exponential tilt.** -/
theorem continuous_thirdCentral_tilted {f g k l : X → ℝ} (hf : Bdd f) (hg : Bdd g) (hk : Bdd k)
    (hl : Bdd l) : Continuous fun t ↦ thirdCentral (ν.tilted (fun x ↦ t * f x)) g k l := by
  have e : ∀ t, thirdCentral (ν.tilted (fun x ↦ t * f x)) g k l =
      (∫ x, g x * k x * l x ∂ν.tilted (fun x ↦ t * f x)) -
        (∫ x, g x * k x ∂ν.tilted (fun x ↦ t * f x)) * (∫ x, l x ∂ν.tilted (fun x ↦ t * f x)) -
        (∫ x, g x * l x ∂ν.tilted (fun x ↦ t * f x)) * (∫ x, k x ∂ν.tilted (fun x ↦ t * f x)) -
        (∫ x, k x * l x ∂ν.tilted (fun x ↦ t * f x)) * (∫ x, g x ∂ν.tilted (fun x ↦ t * f x)) +
        2 * ((∫ x, g x ∂ν.tilted (fun x ↦ t * f x)) * (∫ x, k x ∂ν.tilted (fun x ↦ t * f x)) *
          ∫ x, l x ∂ν.tilted (fun x ↦ t * f x)) := fun t ↦ by
    have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (Bdd.const_mul t hf))
    exact thirdCentral_eq _ hg hk hl
  refine (((((continuous_integral_tilted_mul ν hf ((hg.mul hk).mul hl)).sub
    ((continuous_integral_tilted_mul ν hf (hg.mul hk)).mul
      (continuous_integral_tilted_mul ν hf hl))).sub
    ((continuous_integral_tilted_mul ν hf (hg.mul hl)).mul
      (continuous_integral_tilted_mul ν hf hk))).sub
    ((continuous_integral_tilted_mul ν hf (hk.mul hl)).mul
      (continuous_integral_tilted_mul ν hf hg))).add
    (continuous_const.mul (((continuous_integral_tilted_mul ν hf hg).mul
      (continuous_integral_tilted_mul ν hf hk)).mul
        (continuous_integral_tilted_mul ν hf hl)))).congr fun t ↦ (e t).symm

omit [Nonempty X] in
/-- `Cov_ρ((h − E h)², b) = κ_ρ(h, h, b)`. -/
theorem lawCov_centredSq_eq_thirdCentral (ρ : Measure X) [IsProbabilityMeasure ρ] {h b : X → ℝ}
    (hh : Bdd h) (hb : Bdd b) :
    lawCov ρ (fun x ↦ (h x - ∫ y, h y ∂ρ) ^ 2) b = thirdCentral ρ h h b := by
  have hsq : Bdd (fun x ↦ (h x - ∫ y, h y ∂ρ) ^ 2) := by
    simpa [sq] using ((hh.sub (Bdd.const _)).mul (hh.sub (Bdd.const _)))
  rw [lawCov_eq_integral_centred ρ hsq hb]
  unfold thirdCentral
  have hb0 : ∫ x, (b x - ∫ y, b y ∂ρ) ∂ρ = 0 := by
    rw [integral_sub (integrable_of_bdd_prob ρ hb) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self]
  have hI1 : Integrable (fun x ↦ (h x - ∫ y, h y ∂ρ) ^ 2 * (b x - ∫ y, b y ∂ρ)) ρ :=
    integrable_of_bdd_prob ρ (hsq.mul (hb.sub (Bdd.const _)))
  have hI2 : Integrable (fun x ↦ (∫ y, (h y - ∫ z, h z ∂ρ) ^ 2 ∂ρ) * (b x - ∫ y, b y ∂ρ)) ρ :=
    (integrable_of_bdd_prob ρ (hb.sub (Bdd.const _))).const_mul _
  calc ∫ x, ((h x - ∫ y, h y ∂ρ) ^ 2 - ∫ y, (h y - ∫ z, h z ∂ρ) ^ 2 ∂ρ) * (b x - ∫ y, b y ∂ρ) ∂ρ
      = ∫ x, (h x - ∫ y, h y ∂ρ) ^ 2 * (b x - ∫ y, b y ∂ρ) ∂ρ -
          ∫ x, (∫ y, (h y - ∫ z, h z ∂ρ) ^ 2 ∂ρ) * (b x - ∫ y, b y ∂ρ) ∂ρ := by
        rw [← integral_sub hI1 hI2]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    _ = ∫ x, (h x - ∫ y, h y ∂ρ) * (h x - ∫ y, h y ∂ρ) * (b x - ∫ y, b y ∂ρ) ∂ρ := by
        rw [integral_const_mul, hb0, mul_zero, sub_zero]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

end ThirdContinuity

section Defect

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The data law along the path. -/
local notation "ρ" t => ν.tilted fun x ↦ t * h x

/-- The response of the exponential journey is the seabed's data path. -/
theorem responseOf_smul_eq_dataTheta (t : ℝ) :
    responseOf hS ν (fun x ↦ t * h x) = dataTheta hS ν hh t := by
  unfold responseOf responseTheta dataTheta
  congr 1
  apply Subtype.ext
  rw [toV]
  split_ifs with h'
  · rfl
  · exact absurd (pathV hS ν hh t).2 h'

/-- The response velocity of the exponential journey is the data-path velocity. -/
theorem responseVel_smul_eq_dataThetaVel (t : ℝ) :
    responseVel hS ν (Bdd.const_mul t hh) hh = dataThetaVel hS ν hh t := by
  rw [responseVel, responseOf_smul_eq_dataTheta hS ν hh t]
  rfl

/-- The response speed² of the data path is the pulled-back form of the journey. -/
theorem responseSpeedSq_eq_pullbackForm (t : ℝ) :
    responseSpeedSq hS ν hh t = pullbackForm hS ν (Bdd.const_mul t hh) hh := by
  rw [pullbackForm, fisherVar, responseOf_smul_eq_dataTheta hS ν hh t,
    responseVel_smul_eq_dataThetaVel hS ν hh t]
  rfl

/-- **The response speed² along the data path is differentiable**, with derivative
`κ_{P_{θ_t}}(L_{v_t},L_{v_t},L_{v_t}) − 2 κ_{ρ_t}(L_{v_t}, h, h)`. -/
theorem hasDerivAt_responseSpeedSq (t₀ : ℝ) :
    HasDerivAt (responseSpeedSq hS ν hh)
      (thirdCentral (Pfam (dataTheta hS ν hh t₀ : J → ℝ))
          (dirLoss S (dataThetaVel hS ν hh t₀ : J → ℝ))
          (dirLoss S (dataThetaVel hS ν hh t₀ : J → ℝ))
          (dirLoss S (dataThetaVel hS ν hh t₀ : J → ℝ)) -
        2 * thirdCentral (ρ t₀) (dirLoss S (dataThetaVel hS ν hh t₀ : J → ℝ)) h h) t₀ := by
  have h0 := hasDerivAt_pullbackForm_add hS ν (Bdd.const (0 : ℝ)) hh t₀
  have e : ∀ t : ℝ, (fun x ↦ (0 : ℝ) + t * h x) = fun x ↦ t * h x := fun t ↦ by
    funext x
    simp
  have e1 : ∀ t, responseVel hS ν ((Bdd.const 0).add (Bdd.const_mul t hh)) hh =
      dataThetaVel hS ν hh t := fun t ↦ by
    rw [responseVel_congr hS ν _ _ (Bdd.const_mul t hh) hh (e t) rfl,
      responseVel_smul_eq_dataThetaVel]
  rw [e1 t₀, e t₀, responseOf_smul_eq_dataTheta hS ν hh t₀] at h0
  refine h0.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
  rw [responseSpeedSq_eq_pullbackForm hS ν hh t]
  exact (pullbackForm_congr hS ν ((Bdd.const 0).add (Bdd.const_mul t hh)) hh
    (Bdd.const_mul t hh) hh (e t) rfl).symm

/-- The bracket term of `Δ''(t)` as a combination of third cumulants:
`Cov_{ρ_t}((h − E h)², t h + ⟨θ_t,S⟩) = t κ_{ρ_t}(h,h,h) + ∑ θ_{t,i} κ_{ρ_t}(h,h,S_i)`. -/
theorem defectBracket_eq (t : ℝ) :
    lawCov (ρ t) (fun x ↦ (h x - ∫ y, h y ∂(ρ t)) ^ 2)
        (fun x ↦ t * h x + dirLoss S (dataTheta hS ν hh t : J → ℝ) x) =
      t * thirdCentral (ρ t) h h h +
        ∑ i, (dataTheta hS ν hh t : J → ℝ) i * thirdCentral (ρ t) h h (S i) := by
  have hP := isProbabilityMeasure_dataPath ν hh t
  have hsq : Bdd (fun x ↦ (h x - ∫ y, h y ∂(ρ t)) ^ 2) := by
    simpa [sq] using ((hh.sub (Bdd.const _)).mul (hh.sub (Bdd.const _)))
  rw [lawCov_add_right_eq _ (Bdd.const_mul t hh) (bdd_dirLoss hS _) hsq, lawCov_comm,
    lawCov_const_mul_left_eq, lawCov_comm, lawCov_centredSq_eq_thirdCentral _ hh hh, lawCov_comm,
    lawCov_dirLoss_left hS _ _ _ hsq]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [lawCov_comm, lawCov_centredSq_eq_thirdCentral _ hh (hS i)]

/-- **The bracket term is differentiable at `0`**, with derivative `κ_ν(h,h,h) + κ_ν(h,h,L_v)`. -/
theorem hasDerivAt_defectBracket_zero :
    HasDerivAt (fun t ↦ lawCov (ρ t) (fun x ↦ (h x - ∫ y, h y ∂(ρ t)) ^ 2)
        (fun x ↦ t * h x + dirLoss S (dataTheta hS ν hh t : J → ℝ) x))
      (thirdCentral ν h h h +
        thirdCentral ν h h (dirLoss S (basepointVelocity hS ν hh : J → ℝ))) 0 := by
  have h1 : HasDerivAt (fun t ↦ t * thirdCentral (ρ t) h h h) (1 * thirdCentral (ρ 0) h h h) 0 :=
    hasDerivAt_mul_of_eq_zero (hasDerivAt_id 0) rfl
      (continuous_thirdCentral_tilted ν hh hh hh hh).continuousAt
  have h2 : ∀ i, HasDerivAt
      (fun t ↦ (dataTheta hS ν hh t : J → ℝ) i * thirdCentral (ρ t) h h (S i))
      ((dataThetaVel hS ν hh 0 : J → ℝ) i * thirdCentral (ρ 0) h h (S i)) 0 := fun i ↦
    hasDerivAt_mul_of_eq_zero (hasDerivAt_pi.1 (hasDerivAt_coe_dataTheta hS ν hh 0) i)
      (by simp [dataTheta_zero]) (continuous_thirdCentral_tilted ν hh hh hh (hS i)).continuousAt
  have h := h1.add (HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ h2 i)
  refine (h.congr_of_eventuallyEq
    (Eventually.of_forall fun t ↦ defectBracket_eq hS ν hh t)).congr_deriv ?_
  rw [tilted_zero_mul, dataThetaVel_zero, one_mul]
  congr 1
  rw [thirdCentral_comm₂₃, thirdCentral_comm₁₂, thirdCentral_dirLoss_left _ hS _ hh hh]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [thirdCentral_comm₂₃, thirdCentral_comm₁₂]

/-- **THE THIRD DEFECT DERIVATIVE**: with `v = θ'_0` the initial response velocity and
`L_v = ⟨v,S⟩`, `Δ'''(0) = 2 κ_ν(h,h,h) + 3 κ_ν(h,h,L_v) − κ_ν(L_v,L_v,L_v)`. -/
theorem hasDerivAt_deriv_deriv_responseDefect_zero :
    HasDerivAt (deriv (deriv (responseDefect S ν h)))
      (2 * thirdCentral ν h h h +
        3 * thirdCentral ν h h (dirLoss S (basepointVelocity hS ν hh : J → ℝ)) -
        thirdCentral ν (dirLoss S (basepointVelocity hS ν hh : J → ℝ))
          (dirLoss S (basepointVelocity hS ν hh : J → ℝ))
          (dirLoss S (basepointVelocity hS ν hh : J → ℝ))) 0 := by
  have e2 : deriv (deriv (responseDefect S ν h)) = fun t ↦
      lawCov (ρ t) h h - responseSpeedSq hS ν hh t +
        lawCov (ρ t) (fun x ↦ (h x - ∫ y, h y ∂(ρ t)) ^ 2)
          (fun x ↦ t * h x + dirLoss S (dataTheta hS ν hh t : J → ℝ) x) :=
    funext fun t ↦ deriv_deriv_responseDefect hS ν hh t
  rw [e2]
  have h1 := hasDerivAt_var_tilted ν hh 0
  have h2 := hasDerivAt_responseSpeedSq hS ν hh 0
  have h3 := hasDerivAt_defectBracket_zero hS ν hh
  refine ((h1.sub h2).add h3).congr_deriv ?_
  rw [tilted_zero_mul, familyMeasure_dataTheta_zero hS ν hh, dataThetaVel_zero]
  have hcube : ∫ x, (h x - ∫ y, h y ∂ν) ^ 3 ∂ν = thirdCentral ν h h h := by
    unfold thirdCentral
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have hsym : thirdCentral ν (dirLoss S (basepointVelocity hS ν hh : J → ℝ)) h h =
      thirdCentral ν h h (dirLoss S (basepointVelocity hS ν hh : J → ℝ)) := by
    rw [thirdCentral_comm₁₂, thirdCentral_comm₂₃]
  rw [hcube, hsym]
  ring

/-- The third defect derivative as a value. -/
theorem deriv_deriv_deriv_responseDefect_zero :
    deriv (deriv (deriv (responseDefect S ν h))) 0 =
      2 * thirdCentral ν h h h +
        3 * thirdCentral ν h h (dirLoss S (basepointVelocity hS ν hh : J → ℝ)) -
        thirdCentral ν (dirLoss S (basepointVelocity hS ν hh : J → ℝ))
          (dirLoss S (basepointVelocity hS ν hh : J → ℝ))
          (dirLoss S (basepointVelocity hS ν hh : J → ℝ)) :=
  (hasDerivAt_deriv_deriv_responseDefect_zero hS ν hh).deriv

end Defect

end Laplace.Multi
