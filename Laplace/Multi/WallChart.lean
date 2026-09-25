/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WallWindowLength

/-!
# The singular response chart: two couplings, one profile

For the two-coupling family `L_{a,b}(w) = w^p + a w^q + b w^r` on `(0,∞)` (`0 < q < r < p`) the
wall `a = b = 0` is approached in the window `a = c t^{-σ_q}`, `b = d t^{-σ_r}` (`σ_e = 1 − e/p`),
and the finite-`t` posterior of the scaled coordinate `y = t^{1/p} w` there is exactly the
**two-parameter profile law** `ρ_{c,d} ∝ e^{-(y^p + c y^q + d y^r)} dy`
(`chart_posterior_eq_profile`).
The response form of the family at a window point, **pulled back by the chart Jacobian**
`∂_c = t^{-σ_q} ∂_a`, `∂_d = t^{-σ_r} ∂_b`, is the profile's own Fisher covariance matrix:

  `t^{-σ_{e₁}} t^{-σ_{e₂}} · t² Cov_{t,(a,b)}(w^{e₁}, w^{e₂}) = Cov_{c,d}(y^{e₁}, y^{e₂})`
  (`chart_cov`, `responseForm_chart`),

exactly, for every `t > 0` and all exponents `e₁, e₂` (in particular `q, r`). This is the
homogeneous, flat-prior instance of the *singular response-chart theorem* (Astra, round 24): the
profile is a chart through the singularity, its covariance is the metric in that chart, and the
response geometry of the physical family is the chart geometry transported by the anisotropic
scaling. Two features of the same variable have a nonzero cross term in general: the chamber
geometry is an atlas, not a product.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The two-parameter profile numerator `∫₀^∞ ψ e^{-(y^p + c y^q + d y^r)}`. -/
noncomputable def chartNum (p q r : ℝ) (ψ : ℝ → ℝ) (c d : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), ψ y * Real.exp (-(y ^ p + c * y ^ q + d * y ^ r))

/-- The two-parameter profile law `⟨ψ⟩_{c,d}`. -/
noncomputable def chartPosterior (p q r : ℝ) (ψ : ℝ → ℝ) (c d : ℝ) : ℝ :=
  chartNum p q r ψ c d / chartNum p q r (fun _ ↦ 1) c d

/-- The two-coupling data family `L_{a,b}(w) = w^p + a w^q + b w^r`. -/
noncomputable def chartPath (p q r a b : ℝ) : ℝ → ℝ := fun w ↦ w ^ p + a * w ^ q + b * w ^ r

/-- The scaled numerator in the two-coupling window is `t^{-1/p}` times the profile numerator. -/
theorem chart_numerator_scaled {p q r : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (ψ : ℝ → ℝ)
    (c d : ℝ) :
    ∫ w in Ioi (0 : ℝ), ψ (t ^ (1 / p) * w) *
        Real.exp (-(t * chartPath p q r (c * t ^ (-(1 - q / p))) (d * t ^ (-(1 - r / p))) w)) =
      t ^ (-(1 / p)) * chartNum p q r ψ c d := by
  unfold chartNum chartPath
  have ha : 0 < t ^ (1 / p) := Real.rpow_pos_of_pos ht _
  have key := integral_comp_mul_left_Ioi
    (fun y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q + d * y ^ r))) (0 : ℝ) ha
  rw [mul_zero, smul_eq_mul, ← Real.rpow_neg ht.le] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
  have hw0 : (0 : ℝ) < w := hw
  have hp' : (t ^ (1 / p) * w) ^ p = t * w ^ p := by
    rw [Real.mul_rpow ha.le hw0.le, ← Real.rpow_mul ht.le, one_div_mul_cancel hp.ne',
      Real.rpow_one]
  have hh : ∀ e : ℝ, t * t ^ (-(1 - e / p)) = t ^ (e / p) := fun e ↦ by
    calc t * t ^ (-(1 - e / p)) = t ^ (1 : ℝ) * t ^ (-(1 - e / p)) := by rw [Real.rpow_one]
      _ = t ^ (1 + -(1 - e / p)) := (Real.rpow_add ht _ _).symm
      _ = t ^ (e / p) := by congr 1; ring
  congr 1
  rw [hp', scaled_rpow ht hw0, scaled_rpow ht hw0]
  congr 1
  linear_combination (-(c * w ^ q)) * hh q + (-(d * w ^ r)) * hh r

/-- **The finite-`t` posterior in the two-coupling window is the two-parameter profile law.** -/
theorem chart_posterior_eq_profile {p q r : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (ψ : ℝ → ℝ)
    (c d : ℝ) :
    priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
        (chartPath p q r (c * t ^ (-(1 - q / p))) (d * t ^ (-(1 - r / p))))
        (fun w ↦ ψ (t ^ (1 / p) * w)) t = chartPosterior p q r ψ c d := by
  unfold priorExp priorZ chartPosterior
  have h1 := chart_numerator_scaled (q := q) (r := r) hp ht ψ c d
  have h2 := chart_numerator_scaled (q := q) (r := r) hp ht (fun _ ↦ (1 : ℝ)) c d
  simp only [one_mul] at h2
  simp only [mul_one]
  rw [h1, h2, mul_div_mul_left _ _ (Real.rpow_pos_of_pos ht _).ne']

/-- Monomial moments in the window: `⟨w^e⟩_t = t^{-e/p} ⟨y^e⟩_{c,d}`. -/
theorem priorExp_chart_rpow {p q r : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (c d e : ℝ) :
    priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
        (chartPath p q r (c * t ^ (-(1 - q / p))) (d * t ^ (-(1 - r / p)))) (fun w ↦ w ^ e) t =
      (t ^ (e / p))⁻¹ * chartPosterior p q r (fun y ↦ y ^ e) c d := by
  have h := chart_posterior_eq_profile (q := q) (r := r) hp ht (fun y ↦ y ^ e) c d
  have e' : priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
      (chartPath p q r (c * t ^ (-(1 - q / p))) (d * t ^ (-(1 - r / p))))
      (fun w ↦ (t ^ (1 / p) * w) ^ e) t =
      t ^ (e / p) * priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
        (chartPath p q r (c * t ^ (-(1 - q / p))) (d * t ^ (-(1 - r / p)))) (fun w ↦ w ^ e) t := by
    rw [← priorExp_const_mul]
    refine priorExp_congr_ae _ _ ?_ t
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun w hw ↦ ?_)
    exact scaled_rpow ht hw
  rw [e'] at h
  have hT : t ^ (e / p) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hT, one_mul]

/-- Products of monomials in the window. -/
theorem priorExp_chart_rpow_mul {p q r : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (c d e₁ e₂ : ℝ) :
    priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
        (chartPath p q r (c * t ^ (-(1 - q / p))) (d * t ^ (-(1 - r / p))))
        (fun w ↦ w ^ e₁ * w ^ e₂) t =
      (t ^ (e₁ / p))⁻¹ * (t ^ (e₂ / p))⁻¹ * chartPosterior p q r (fun y ↦ y ^ e₁ * y ^ e₂) c d := by
  have h := chart_posterior_eq_profile (q := q) (r := r) hp ht (fun y ↦ y ^ e₁ * y ^ e₂) c d
  have e' : priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
      (chartPath p q r (c * t ^ (-(1 - q / p))) (d * t ^ (-(1 - r / p))))
      (fun w ↦ (t ^ (1 / p) * w) ^ e₁ * (t ^ (1 / p) * w) ^ e₂) t =
      (t ^ (e₁ / p) * t ^ (e₂ / p)) * priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
        (chartPath p q r (c * t ^ (-(1 - q / p))) (d * t ^ (-(1 - r / p))))
        (fun w ↦ w ^ e₁ * w ^ e₂) t := by
    rw [← priorExp_const_mul]
    refine priorExp_congr_ae _ _ ?_ t
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun w hw ↦ ?_)
    rw [scaled_rpow ht hw, scaled_rpow ht hw]
    ring
  rw [e'] at h
  have hT₁ : t ^ (e₁ / p) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hT₂ : t ^ (e₂ / p) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  rw [← h]
  field_simp

/-- **The singular response chart**: the covariance of two monomials in the window, pulled back by
the chart Jacobian `t^{-σ_{e₁}} t^{-σ_{e₂}}`, is exactly the two-parameter profile covariance. -/
theorem chart_cov {p q r : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (c d e₁ e₂ : ℝ) :
    (t ^ (1 - e₁ / p))⁻¹ * (t ^ (1 - e₂ / p))⁻¹ * (t ^ 2 * priorCov (volume.restrict (Ioi 0))
        (fun _ ↦ 1) (chartPath p q r (c * t ^ (-(1 - q / p))) (d * t ^ (-(1 - r / p))))
        (fun w ↦ w ^ e₁) (fun w ↦ w ^ e₂) t) =
      chartPosterior p q r (fun y ↦ y ^ e₁ * y ^ e₂) c d -
        chartPosterior p q r (fun y ↦ y ^ e₁) c d * chartPosterior p q r (fun y ↦ y ^ e₂) c d := by
  unfold priorCov
  rw [priorExp_chart_rpow_mul hp ht, priorExp_chart_rpow hp ht, priorExp_chart_rpow hp ht,
    Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_one]
  have hT₁ : t ^ (e₁ / p) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hT₂ : t ^ (e₂ / p) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  field_simp

/-- The two-coupling family as an affine family over the base `w^p` with contrasts `w^q, w^r`. -/
theorem affLoss_chart (p q r a b : ℝ) :
    affLoss (fun w : ℝ ↦ w ^ p) ![fun w ↦ w ^ q, fun w ↦ w ^ r] ![a, b] = chartPath p q r a b := by
  funext w
  simp [affLoss, chartPath, Fin.sum_univ_two]
  ring

/-- A coordinate direction loss is the corresponding contrast. -/
theorem dirLoss_single {ι X : Type*} [Fintype ι] [DecidableEq ι] (R : ι → X → ℝ) (i : ι) :
    dirLoss R (Pi.single i 1) = R i := by
  funext x
  simp [dirLoss, Pi.single_apply]

/-- **The response form of the two-coupling family in the window is the profile Fisher matrix**
after pulling back by the chart Jacobian: with `E = ![q, r]`,
`t^{-σ_{E i}} t^{-σ_{E j}} g_{(a,b)}(eᵢ, eⱼ) = Cov_{c,d}(y^{E i}, y^{E j})`. -/
theorem responseForm_chart {p q r : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (c d : ℝ) (i j : Fin 2) :
    (t ^ (1 - ![q, r] i / p))⁻¹ * (t ^ (1 - ![q, r] j / p))⁻¹ *
      responseForm (volume.restrict (Ioi 0)) (fun _ ↦ 1) (fun w : ℝ ↦ w ^ p)
        ![fun w ↦ w ^ q, fun w ↦ w ^ r] ![c * t ^ (-(1 - q / p)), d * t ^ (-(1 - r / p))] t
        (Pi.single i 1) (Pi.single j 1) =
      chartPosterior p q r (fun y ↦ y ^ (![q, r] i) * y ^ (![q, r] j)) c d -
        chartPosterior p q r (fun y ↦ y ^ (![q, r] i)) c d *
          chartPosterior p q r (fun y ↦ y ^ (![q, r] j)) c d := by
  have hR : ∀ k : Fin 2, (![fun w : ℝ ↦ w ^ q, fun w ↦ w ^ r] : Fin 2 → ℝ → ℝ) k =
      fun w ↦ w ^ (![q, r] k) := fun k ↦ by
    fin_cases k <;> rfl
  unfold responseForm
  rw [affLoss_chart, dirLoss_single, dirLoss_single, hR i, hR j]
  exact chart_cov hp ht c d _ _

end Laplace.Multi
