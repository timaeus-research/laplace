/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.FourGonSusceptibility
import Laplace.Patterning.RadialVirial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The radial rows of the 4-gon susceptibility matrix

The rows of the susceptibility matrix for the dead unit's norm `‖W₄‖` and for the restricted
excess loss `K = r⁴/15` depend on the radial law through its moments `Eₖ = E_t[rᵏ]`, which for
the quartic Gibbs law are `(t/15)^{-k/4} Γ((k+2)/4)/Γ(1/2)`. With `χ(φ; hᵢ) = −(t/5) Cov_t(φ, ℓᵢ)`:

* `χ(‖W₄‖; hⱼ) = −(t/60)(E₃ − E₁E₂) < 0` for the alive features (`deadChi_normObs_alive`,
  `deadChi_normObs_alive_neg`; the sign is `Cov(r, r²) > 0`, proved from the log-convexity of `Γ`
  and Legendre's duplication formula), and `χ(‖W₄‖; h₄) = −(t/15)[(E₅ − E₃) − E₁(E₄ − E₂)]`;
* `χ(K; hⱼ) = −(t/900)(E₆ − E₄E₂)` and `χ(K; h₄) = −(t/225)[(E₈ − E₆) − E₄(E₄ − E₂)]`;
* the excess-loss row sums to `−t Var_t(K) = −1/(2t)` exactly (`deadChi_deadQuartic_sum`), using
  `E₄ = 15/(2t)` and `E₈ = 675/(4t²)`: the note's "sums to zero within noise" is `−1/(2t)`.

At `t = 1000` these give `−0.087`, `+0.287`, `−0.00058`, `+0.0018`, `−0.0005`, matching the
sampled matrix of the note.
-/

namespace Laplace.Patterning

open Real MeasureTheory Set Laplace.TwoD intervalIntegral

noncomputable section

/-! ### General rotationally symmetric laws -/

theorem integral_relu_cos_sub_sq (β : ℝ) : ∫ θ in (-π)..π, relu (cos (θ - β)) ^ 2 = π / 2 := by
  have hper : Function.Periodic (fun θ => relu (cos θ) ^ 2) (2 * π) := fun θ => by
    simp only
    rw [cos_periodic θ]
  exact (integral_periodic_shift (fun θ => relu (cos θ) ^ 2) hper β).trans integral_relu_cos_sq

theorem deadQuartic_polar (r θ : ℝ) : deadQuartic (r * cos θ, r * sin θ) = r ^ 4 / 15 := by
  simp only [deadQuartic, polar_sq]
  ring

/-- `Cov(r, ℓ_β) = (1/12)(E₃ − E₁E₂)` for every rotationally symmetric law. -/
theorem radialCov_normObs_plusLoss (G : ℝ → ℝ) (β : ℝ) :
    radialCov G normObs (plusLoss β)
      = 1 / 12 * (polarMoment G 3 / polarMoment G 0
          - polarMoment G 1 / polarMoment G 0 * (polarMoment G 2 / polarMoment G 0)) := by
  unfold radialCov radialExpectation
  beta_reduce
  rw [integral_radial_weight,
    integral_polar_sep (fun z => normObs z * plusLoss β z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 3 * (r ^ 4 * G (r ^ 2))) (fun θ => relu (cos (θ - β)) ^ 2)
      (fun r hr θ _ => by rw [normObs_polar hr.le, plusLoss_polar β hr.le, polar_sq]; ring),
    integral_polar_sep (fun z => normObs z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => r ^ 2 * G (r ^ 2)) (fun _ => 1)
      (fun r hr θ _ => by rw [normObs_polar hr.le, polar_sq]; ring),
    integral_polar_sep (fun z => plusLoss β z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 3 * (r ^ 3 * G (r ^ 2))) (fun θ => relu (cos (θ - β)) ^ 2)
      (fun r hr θ _ => by rw [plusLoss_polar β hr.le, polar_sq]; ring),
    integral_relu_cos_sub_sq, intervalIntegral.integral_const, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  have h3 : ∫ r in Ioi (0 : ℝ), r ^ 4 * G (r ^ 2) = polarMoment G 3 := rfl
  have h1 : ∫ r in Ioi (0 : ℝ), r ^ 2 * G (r ^ 2) = polarMoment G 1 := rfl
  have h2 : ∫ r in Ioi (0 : ℝ), r ^ 3 * G (r ^ 2) = polarMoment G 2 := rfl
  rw [h3, h1, h2]
  simp only [sub_neg_eq_add, smul_eq_mul, mul_one]
  by_cases hm : polarMoment G 0 = 0
  · simp [hm]
  · field_simp
    ring

/-- `Cov(K, ℓ_β) = (1/180)(E₆ − E₄E₂)` for every rotationally symmetric law. -/
theorem radialCov_deadQuartic_plusLoss (G : ℝ → ℝ) (β : ℝ) :
    radialCov G deadQuartic (plusLoss β)
      = 1 / 180 * (polarMoment G 6 / polarMoment G 0
          - polarMoment G 4 / polarMoment G 0 * (polarMoment G 2 / polarMoment G 0)) := by
  unfold radialCov radialExpectation
  beta_reduce
  rw [integral_radial_weight,
    integral_polar_sep (fun z => deadQuartic z * plusLoss β z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 45 * (r ^ 7 * G (r ^ 2))) (fun θ => relu (cos (θ - β)) ^ 2)
      (fun r hr θ _ => by rw [deadQuartic_polar, plusLoss_polar β hr.le, polar_sq]; ring),
    integral_polar_sep (fun z => deadQuartic z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 15 * (r ^ 5 * G (r ^ 2))) (fun _ => 1)
      (fun r _ θ _ => by rw [deadQuartic_polar, polar_sq]; ring),
    integral_polar_sep (fun z => plusLoss β z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 3 * (r ^ 3 * G (r ^ 2))) (fun θ => relu (cos (θ - β)) ^ 2)
      (fun r hr θ _ => by rw [plusLoss_polar β hr.le, polar_sq]; ring),
    integral_relu_cos_sub_sq, intervalIntegral.integral_const, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have h6 : ∫ r in Ioi (0 : ℝ), r ^ 7 * G (r ^ 2) = polarMoment G 6 := rfl
  have h4 : ∫ r in Ioi (0 : ℝ), r ^ 5 * G (r ^ 2) = polarMoment G 4 := rfl
  have h2 : ∫ r in Ioi (0 : ℝ), r ^ 3 * G (r ^ 2) = polarMoment G 2 := rfl
  rw [h6, h4, h2]
  simp only [sub_neg_eq_add, smul_eq_mul, mul_one]
  by_cases hm : polarMoment G 0 = 0
  · simp [hm]
  · field_simp
    ring

/-! ### The quartic Gibbs law: moments and the dead-feature rows -/

theorem integrableOn_pow_mul_quarticWeight (t : ℝ) (ht : 0 < t) (n : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ n * quarticWeight t (r ^ 2)) (Ioi 0) := by
  have h := integrableOn_pow_mul_exp_neg_quartic (t / 15) (by positivity) n
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [quarticWeight, ← pow_mul]
  ring_nf

/-- `E_t[rᵏ]`, the radial moments of the dead component under the restricted Gibbs law. -/
def gibbsMoment (t : ℝ) (k : ℕ) : ℝ :=
  Laplace.TwoD.gibbsExpectation deadQuartic t (fun z => normObs z ^ k)

theorem gibbsMoment_eq_ratio (t : ℝ) (k : ℕ) :
    gibbsMoment t k = polarMoment (quarticWeight t) k / polarMoment (quarticWeight t) 0 := by
  rw [gibbsMoment, gibbsExpectation_eq_radial, radialExpectation_normObs_pow]

/-- **Closed form**: `E_t[rᵏ] = (t/15)^{-k/4} Γ((k+2)/4) / Γ(1/2)`. -/
theorem gibbsMoment_closed (t : ℝ) (ht : 0 < t) (k : ℕ) :
    gibbsMoment t k = (t / 15) ^ (-(k : ℝ) / 4) * Gamma (((k : ℝ) + 2) / 4) / Gamma (1 / 2) := by
  have ha : (0 : ℝ) < t / 15 := by positivity
  have h0 := polarMoment_quartic t ht 0
  simp only [Nat.cast_zero, zero_add] at h0
  rw [gibbsMoment_eq_ratio, polarMoment_quartic t ht k, h0]
  have hsplit : (t / 15) ^ (-((k : ℝ) + 2) / 4)
      = (t / 15) ^ (-(k : ℝ) / 4) * (t / 15) ^ (-(2 : ℝ) / 4) := by
    rw [← rpow_add ha]
    ring_nf
  have hpos : (0 : ℝ) < (t / 15) ^ (-(2 : ℝ) / 4) := rpow_pos_of_pos ha _
  have hG : (0 : ℝ) < Gamma (2 / 4) := Gamma_pos_of_pos (by norm_num)
  rw [hsplit, show (2 : ℝ) / 4 = 1 / 2 by norm_num] at *
  field_simp
  try ring

theorem gibbsMoment_four (t : ℝ) (ht : 0 < t) : gibbsMoment t 4 = 15 / (2 * t) := by
  rw [gibbsMoment_closed t ht 4]
  have hG : Gamma ((((4 : ℕ) : ℝ) + 2) / 4) = (1 / 2) * Gamma (1 / 2) := by
    rw [show (((4 : ℕ) : ℝ) + 2) / 4 = 1 / 2 + 1 by norm_num, Gamma_add_one (by norm_num)]
  rw [hG, show -((4 : ℕ) : ℝ) / 4 = -1 by norm_num, rpow_neg_one]
  have := Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  field_simp
  try ring

theorem gibbsMoment_eight (t : ℝ) (ht : 0 < t) : gibbsMoment t 8 = 675 / (4 * t ^ 2) := by
  rw [gibbsMoment_closed t ht 8]
  have hG : Gamma ((((8 : ℕ) : ℝ) + 2) / 4) = (3 / 4) * Gamma (1 / 2) := by
    rw [show (((8 : ℕ) : ℝ) + 2) / 4 = (1 / 2 + 1) + 1 by norm_num, Gamma_add_one (by norm_num),
      Gamma_add_one (by norm_num)]
    ring
  rw [hG, show -((8 : ℕ) : ℝ) / 4 = ((-2 : ℤ) : ℝ) by norm_num, rpow_intCast, zpow_neg, zpow_two]
  have := Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  field_simp
  try ring

/-- `Cov_t(r, ℓ₄) = ⅓[(E₅ − E₃) − E₁(E₄ − E₂)]`. -/
theorem gibbsCov_normObs_deadLoss (t : ℝ) (ht : 0 < t) :
    Laplace.TwoD.gibbsCov deadQuartic t normObs deadLoss
      = 1 / 3 * ((gibbsMoment t 5 - gibbsMoment t 3)
          - gibbsMoment t 1 * (gibbsMoment t 4 - gibbsMoment t 2)) := by
  simp only [gibbsMoment_eq_ratio]
  rw [gibbsCov_eq_radial]
  unfold radialCov radialExpectation
  beta_reduce
  set G := quarticWeight t with hG
  rw [integral_radial_weight,
    integral_polar_sep (fun z => normObs z * deadLoss z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 3 * (r ^ 6 * G (r ^ 2) - r ^ 4 * G (r ^ 2))) (fun _ => 1)
      (fun r hr θ _ => by rw [normObs_polar hr.le, deadLoss_polar, polar_sq]; ring),
    integral_polar_sep (fun z => normObs z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => r ^ 2 * G (r ^ 2)) (fun _ => 1)
      (fun r hr θ _ => by rw [normObs_polar hr.le, polar_sq]; ring),
    integral_polar_sep (fun z => deadLoss z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 3 * (r ^ 5 * G (r ^ 2) - r ^ 3 * G (r ^ 2))) (fun _ => 1)
      (fun r _ θ _ => by rw [deadLoss_polar, polar_sq]; ring),
    intervalIntegral.integral_const, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul,
    integral_sub (integrableOn_pow_mul_quarticWeight t ht 6)
      (integrableOn_pow_mul_quarticWeight t ht 4),
    integral_sub (integrableOn_pow_mul_quarticWeight t ht 5)
      (integrableOn_pow_mul_quarticWeight t ht 3)]
  have h5 : ∫ r in Ioi (0 : ℝ), r ^ 6 * G (r ^ 2) = polarMoment G 5 := rfl
  have h3 : ∫ r in Ioi (0 : ℝ), r ^ 4 * G (r ^ 2) = polarMoment G 3 := rfl
  have h1 : ∫ r in Ioi (0 : ℝ), r ^ 2 * G (r ^ 2) = polarMoment G 1 := rfl
  have h4 : ∫ r in Ioi (0 : ℝ), r ^ 5 * G (r ^ 2) = polarMoment G 4 := rfl
  have h2 : ∫ r in Ioi (0 : ℝ), r ^ 3 * G (r ^ 2) = polarMoment G 2 := rfl
  rw [h5, h3, h1, h4, h2]
  simp only [sub_neg_eq_add, smul_eq_mul, mul_one]
  have hm0 := (polarMoment_quartic_pos t ht 0).ne'
  field_simp
  ring

/-- `Cov_t(K, ℓ₄) = (1/45)[(E₈ − E₆) − E₄(E₄ − E₂)]`. -/
theorem gibbsCov_deadQuartic_deadLoss (t : ℝ) (ht : 0 < t) :
    Laplace.TwoD.gibbsCov deadQuartic t deadQuartic deadLoss
      = 1 / 45 * ((gibbsMoment t 8 - gibbsMoment t 6)
          - gibbsMoment t 4 * (gibbsMoment t 4 - gibbsMoment t 2)) := by
  simp only [gibbsMoment_eq_ratio]
  rw [gibbsCov_eq_radial]
  unfold radialCov radialExpectation
  beta_reduce
  set G := quarticWeight t with hG
  rw [integral_radial_weight,
    integral_polar_sep (fun z => deadQuartic z * deadLoss z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 45 * (r ^ 9 * G (r ^ 2) - r ^ 7 * G (r ^ 2))) (fun _ => 1)
      (fun r _ θ _ => by rw [deadQuartic_polar, deadLoss_polar, polar_sq]; ring),
    integral_polar_sep (fun z => deadQuartic z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 15 * (r ^ 5 * G (r ^ 2))) (fun _ => 1)
      (fun r _ θ _ => by rw [deadQuartic_polar, polar_sq]; ring),
    integral_polar_sep (fun z => deadLoss z * G (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 3 * (r ^ 5 * G (r ^ 2) - r ^ 3 * G (r ^ 2))) (fun _ => 1)
      (fun r _ θ _ => by rw [deadLoss_polar, polar_sq]; ring),
    intervalIntegral.integral_const, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_sub (integrableOn_pow_mul_quarticWeight t ht 9)
      (integrableOn_pow_mul_quarticWeight t ht 7),
    integral_sub (integrableOn_pow_mul_quarticWeight t ht 5)
      (integrableOn_pow_mul_quarticWeight t ht 3)]
  have h8 : ∫ r in Ioi (0 : ℝ), r ^ 9 * G (r ^ 2) = polarMoment G 8 := rfl
  have h6 : ∫ r in Ioi (0 : ℝ), r ^ 7 * G (r ^ 2) = polarMoment G 6 := rfl
  have h4 : ∫ r in Ioi (0 : ℝ), r ^ 5 * G (r ^ 2) = polarMoment G 4 := rfl
  have h2 : ∫ r in Ioi (0 : ℝ), r ^ 3 * G (r ^ 2) = polarMoment G 2 := rfl
  rw [h8, h6, h4, h2]
  simp only [sub_neg_eq_add, smul_eq_mul, mul_one]
  have hm0 := (polarMoment_quartic_pos t ht 0).ne'
  field_simp
  ring

/-! ### The norm and excess-loss rows of the susceptibility matrix -/

/-- `χ(‖W₄‖; hⱼ) = −(t/60)(E₃ − E₁E₂)` for the alive features. -/
theorem deadChi_normObs_alive (t : ℝ) (j : Fin 4) :
    deadChi t normObs (Fin.castSucc j)
      = -(t / 60) * (gibbsMoment t 3 - gibbsMoment t 1 * gibbsMoment t 2) := by
  unfold deadChi
  rw [show featureExcess (Fin.castSucc j) = plusLoss (featureAngle j) from
    funext (featureExcess_alive j), gibbsCov_eq_radial, radialCov_normObs_plusLoss]
  simp only [gibbsMoment_eq_ratio]
  ring

/-- `χ(‖W₄‖; h₄) = −(t/15)[(E₅ − E₃) − E₁(E₄ − E₂)]`. -/
theorem deadChi_normObs_dead (t : ℝ) (ht : 0 < t) :
    deadChi t normObs 4
      = -(t / 15) * ((gibbsMoment t 5 - gibbsMoment t 3)
          - gibbsMoment t 1 * (gibbsMoment t 4 - gibbsMoment t 2)) := by
  unfold deadChi
  rw [show featureExcess 4 = deadLoss from funext featureExcess_dead,
    gibbsCov_normObs_deadLoss t ht]
  ring

/-- `χ(K; hⱼ) = −(t/900)(E₆ − E₄E₂)` for the alive features. -/
theorem deadChi_deadQuartic_alive (t : ℝ) (j : Fin 4) :
    deadChi t deadQuartic (Fin.castSucc j)
      = -(t / 900) * (gibbsMoment t 6 - gibbsMoment t 4 * gibbsMoment t 2) := by
  unfold deadChi
  rw [show featureExcess (Fin.castSucc j) = plusLoss (featureAngle j) from
    funext (featureExcess_alive j), gibbsCov_eq_radial, radialCov_deadQuartic_plusLoss]
  simp only [gibbsMoment_eq_ratio]
  ring

/-- `χ(K; h₄) = −(t/225)[(E₈ − E₆) − E₄(E₄ − E₂)]`. -/
theorem deadChi_deadQuartic_dead (t : ℝ) (ht : 0 < t) :
    deadChi t deadQuartic 4
      = -(t / 225) * ((gibbsMoment t 8 - gibbsMoment t 6)
          - gibbsMoment t 4 * (gibbsMoment t 4 - gibbsMoment t 2)) := by
  unfold deadChi
  rw [show featureExcess 4 = deadLoss from funext featureExcess_dead,
    gibbsCov_deadQuartic_deadLoss t ht]
  ring

/-- **The excess-loss row sums to `−t Var_t(K) = −1/(2t)`**, not to zero. -/
theorem deadChi_deadQuartic_sum (t : ℝ) (ht : 0 < t) :
    ∑ i, deadChi t deadQuartic i = -1 / (2 * t) := by
  rw [Fin.sum_univ_five]
  have h0 : deadChi t deadQuartic 0
      = -(t / 900) * (gibbsMoment t 6 - gibbsMoment t 4 * gibbsMoment t 2) :=
    deadChi_deadQuartic_alive t 0
  have h1 : deadChi t deadQuartic 1
      = -(t / 900) * (gibbsMoment t 6 - gibbsMoment t 4 * gibbsMoment t 2) :=
    deadChi_deadQuartic_alive t 1
  have h2 : deadChi t deadQuartic 2
      = -(t / 900) * (gibbsMoment t 6 - gibbsMoment t 4 * gibbsMoment t 2) :=
    deadChi_deadQuartic_alive t 2
  have h3 : deadChi t deadQuartic 3
      = -(t / 900) * (gibbsMoment t 6 - gibbsMoment t 4 * gibbsMoment t 2) :=
    deadChi_deadQuartic_alive t 3
  rw [h0, h1, h2, h3, deadChi_deadQuartic_dead t ht, gibbsMoment_four t ht, gibbsMoment_eight t ht]
  field_simp
  ring

/-- The mean and the second moment of the excess loss: `E_t[K] = E₄/15`, `E_t[K²] = E₈/225`. -/
theorem gibbsExpectation_deadQuartic_sq (t : ℝ) (ht : 0 < t) :
    Laplace.TwoD.gibbsExpectation deadQuartic t (fun z => deadQuartic z * deadQuartic z)
      = gibbsMoment t 8 / 225 := by
  rw [gibbsExpectation_eq_radial, gibbsMoment_eq_ratio]
  unfold radialExpectation
  rw [integral_radial_weight,
    integral_polar_sep (fun z => deadQuartic z * deadQuartic z * quarticWeight t (z.1 ^ 2 + z.2 ^ 2))
      (fun r => 1 / 225 * (r ^ 9 * quarticWeight t (r ^ 2))) (fun _ => 1)
      (fun r _ θ _ => by rw [deadQuartic_polar, polar_sq]; ring),
    intervalIntegral.integral_const, MeasureTheory.integral_const_mul]
  have h8 : ∫ r in Ioi (0 : ℝ), r ^ 9 * quarticWeight t (r ^ 2) = polarMoment (quarticWeight t) 8 :=
    rfl
  rw [h8]
  simp only [sub_neg_eq_add, smul_eq_mul, mul_one]
  have hm0 := (polarMoment_quartic_pos t ht 0).ne'
  field_simp
  ring

/-- **The fluctuation of the excess loss**: `t² Var_t(K) = ½`. The learning coefficient of the
dead component is both the mean and the variance of `tK`: `tK` is `Gamma(½, 1)`. -/
theorem deadQuartic_gibbs_variance (t : ℝ) (ht : 0 < t) :
    t ^ 2 * Laplace.TwoD.gibbsCov deadQuartic t deadQuartic deadQuartic = 1 / 2 := by
  have hK : Laplace.TwoD.gibbsExpectation deadQuartic t deadQuartic = 1 / (2 * t) := by
    have h := deadQuartic_gibbs_excess t ht
    field_simp
    linarith
  unfold Laplace.TwoD.gibbsCov
  rw [gibbsExpectation_deadQuartic_sq t ht, hK, gibbsMoment_eight t ht]
  field_simp
  ring

/-! ### The sign of the norm row: `Cov_t(r, r²) > 0` -/

/-- Log-convexity of `Γ` at the midpoint of `[1/2, 1]`: `Γ(3/4)² ≤ Γ(1/2) Γ(1) = √π`. -/
theorem Gamma_three_quarters_sq_le : Gamma (3 / 4) ^ 2 ≤ √π := by
  have h := convexOn_log_Gamma.2 (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num)
    (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [Function.comp, smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * (1 / 2) + 1 / 2 * 1 = 3 / 4 by norm_num, Gamma_one, Gamma_one_half_eq,
    log_one] at h
  have h34 : 0 < Gamma (3 / 4 : ℝ) := Gamma_pos_of_pos (by norm_num)
  have hpi : 0 < √π := sqrt_pos.mpr pi_pos
  rw [← log_le_log_iff (by positivity) hpi, log_pow]
  push_cast
  linarith

/-- Legendre duplication at `3/4`: `Γ(3/4) Γ(5/4) = π / (2√2)`. -/
theorem Gamma_three_quarters_mul_five_quarters : Gamma (3 / 4) * Gamma (5 / 4) = π / (2 * √2) := by
  have h := Gamma_mul_Gamma_add_half (3 / 4 : ℝ)
  rw [show (3 / 4 : ℝ) + 1 / 2 = 5 / 4 by norm_num,
    show (1 : ℝ) - 2 * (3 / 4) = -(1 / 2) by norm_num,
    show (2 : ℝ) * (3 / 4) = 1 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), Gamma_one_half_eq,
    rpow_neg (by norm_num), ← sqrt_eq_rpow] at h
  rw [h]
  have h2 : (0 : ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  have hsq : √π * √π = π := mul_self_sqrt pi_pos.le
  field_simp
  nlinarith [hsq]

/-- `Γ(3/4) < Γ(5/4) √π`, the inequality behind `Cov_t(r, r²) > 0`. -/
theorem Gamma_three_quarters_lt : Gamma (3 / 4) < Gamma (5 / 4) * √π := by
  have h34 : 0 < Gamma (3 / 4 : ℝ) := Gamma_pos_of_pos (by norm_num)
  have hdup := Gamma_three_quarters_mul_five_quarters
  have hsq := Gamma_three_quarters_sq_le
  have h2 : (0 : ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  have hs2 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  have hpi : 0 < √π := sqrt_pos.mpr pi_pos
  have hpi2 : √π * √π = π := mul_self_sqrt pi_pos.le
  -- Γ(3/4)² ≤ √π < π√π/(2√2), and Γ(5/4)√π = π√π/(2√2 Γ(3/4))
  have hlt : √π * (2 * √2) < π * √π := by
    have h8 : 2 * √2 < π := by nlinarith [hs2, pi_gt_three, h2]
    nlinarith [h8, hpi]
  have key : Gamma (3 / 4) * Gamma (3 / 4) < Gamma (5 / 4) * √π * Gamma (3 / 4) := by
    rw [show Gamma (5 / 4) * √π * Gamma (3 / 4) = (Gamma (3 / 4) * Gamma (5 / 4)) * √π by ring,
      hdup]
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith [hsq, hlt]
  exact lt_of_mul_lt_mul_right key h34.le

theorem gibbsMoment_three_sub_pos (t : ℝ) (ht : 0 < t) :
    0 < gibbsMoment t 3 - gibbsMoment t 1 * gibbsMoment t 2 := by
  rw [gibbsMoment_closed t ht 3, gibbsMoment_closed t ht 1, gibbsMoment_closed t ht 2]
  have ha : (0 : ℝ) < t / 15 := by positivity
  have hsplit : (t / 15) ^ (-((3 : ℕ) : ℝ) / 4)
      = (t / 15) ^ (-((1 : ℕ) : ℝ) / 4) * (t / 15) ^ (-((2 : ℕ) : ℝ) / 4) := by
    rw [← rpow_add ha]
    norm_num
  rw [hsplit, show (((2 : ℕ) : ℝ) + 2) / 4 = 1 by norm_num, Gamma_one,
    show (((3 : ℕ) : ℝ) + 2) / 4 = 5 / 4 by norm_num,
    show (((1 : ℕ) : ℝ) + 2) / 4 = 3 / 4 by norm_num,
    Gamma_one_half_eq]
  have hp1 : (0 : ℝ) < (t / 15) ^ (-((1 : ℕ) : ℝ) / 4) := rpow_pos_of_pos ha _
  have hp2 : (0 : ℝ) < (t / 15) ^ (-((2 : ℕ) : ℝ) / 4) := rpow_pos_of_pos ha _
  have hpi : 0 < √π := sqrt_pos.mpr pi_pos
  have hlt := Gamma_three_quarters_lt
  have : (t / 15) ^ (-((1 : ℕ) : ℝ) / 4) * (t / 15) ^ (-((2 : ℕ) : ℝ) / 4) * Gamma (5 / 4) / √π
      - (t / 15) ^ (-((1 : ℕ) : ℝ) / 4) * Gamma (3 / 4) / √π
        * ((t / 15) ^ (-((2 : ℕ) : ℝ) / 4) * 1 / √π)
      = (t / 15) ^ (-((1 : ℕ) : ℝ) / 4) * (t / 15) ^ (-((2 : ℕ) : ℝ) / 4) / (√π * √π)
        * (Gamma (5 / 4) * √π - Gamma (3 / 4)) := by
    field_simp
    try ring
  rw [this]
  exact mul_pos (by positivity) (by linarith)

/-- **`χ(‖W₄‖; hⱼ) < 0`**: upweighting any alive feature shrinks the dead unit. -/
theorem deadChi_normObs_alive_neg (t : ℝ) (ht : 0 < t) (j : Fin 4) :
    deadChi t normObs (Fin.castSucc j) < 0 := by
  rw [deadChi_normObs_alive]
  have := gibbsMoment_three_sub_pos t ht
  nlinarith

end

end Laplace.Patterning
