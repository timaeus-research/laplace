/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WallRecedes

/-!
# A spectator mode: the receding-wall coefficient is not the RLCT of the dominant side

For the two-dimensional family `L_a(x, y) = x² + y⁴ + a y²` (Lebesgue prior on `ℝ²`) the wall
`a = 0` has `σ* = 1 − 2/4 = 1/2`, and for fixed `a > 0` the model is regular with RLCT `1`. But
the `x`-mode is a **spectator** for the response to `a`: the posterior factorises, `y²` is even,
and the response geometry of the family is exactly that of the half-line two-monomial family
`w⁴ + a w²` (`spectator_fisherSpeed`). Hence the wall recedes at rate

  `σ* √κ_resp = (1/2) · √(1/2) = 1/(2√2)`   (`spectator_wall_recedes`),

not `σ* √λ = 1/2`: the right exponent is the *response-active* one,
`κ_resp = lim c² Var_c(y²) = 1/2`, the RLCT of the modes actually activated by the coupling that
vanishes at the wall (Astra, round 23).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The spectator family `L_a(x, y) = x² + y⁴ + a y²`. -/
noncomputable def spectatorPath : ℝ → ℝ × ℝ → ℝ := fun a p ↦ p.1 ^ 2 + p.2 ^ 4 + a * p.2 ^ 2

/-- Its velocity `y²`. -/
noncomputable def spectatorVel : ℝ → ℝ × ℝ → ℝ := fun _ p ↦ p.2 ^ 2

/-- The `x`-mode factors out of every numerator. -/
theorem spectator_num (t a : ℝ) (φ : ℝ → ℝ) :
    ∫ p : ℝ × ℝ, φ p.2 * Real.exp (-(t * spectatorPath a p)) * 1 =
      (∫ x : ℝ, Real.exp (-(t * x ^ 2))) *
        ∫ y : ℝ, φ y * Real.exp (-(t * (y ^ 4 + a * y ^ 2))) := by
  rw [Measure.volume_eq_prod, ← integral_prod_mul (fun x ↦ Real.exp (-(t * x ^ 2)))
    (fun y ↦ φ y * Real.exp (-(t * (y ^ 4 + a * y ^ 2))))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
  simp only [mul_one, spectatorPath]
  rw [show -(t * (p.1 ^ 2 + p.2 ^ 4 + a * p.2 ^ 2)) =
    -(t * p.1 ^ 2) + -(t * (p.2 ^ 4 + a * p.2 ^ 2)) by ring, Real.exp_add]
  ring

/-- An even integrand on the line is twice its half-line integral. -/
theorem integral_even_eq_two_Ioi {F : ℝ → ℝ} (hF : ∀ y, F |y| = F y) :
    ∫ y : ℝ, F y = 2 * ∫ y in Ioi (0 : ℝ), F y := by
  rw [← integral_comp_abs (f := F)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ (hF y).symm)

/-- The weight is even. -/
theorem spectator_weight_even (t a : ℝ) (y : ℝ) :
    Real.exp (-(t * (|y| ^ 4 + a * |y| ^ 2))) = Real.exp (-(t * (y ^ 4 + a * y ^ 2))) := by
  rw [show |y| ^ 4 = y ^ 4 by rw [← abs_pow, abs_of_nonneg (by positivity)], sq_abs]

/-- The even numerator integrand is even. -/
theorem spectator_even (t a : ℝ) {φ : ℝ → ℝ} (hφ : ∀ y, φ |y| = φ y) (y : ℝ) :
    φ |y| * Real.exp (-(t * (|y| ^ 4 + a * |y| ^ 2))) =
      φ y * Real.exp (-(t * (y ^ 4 + a * y ^ 2))) := by
  rw [hφ, spectator_weight_even]

/-- The half-line two-monomial numerator with real exponents equals the natural-power one. -/
theorem twoMono_num_eq (t a : ℝ) {φ ψ : ℝ → ℝ} (hφψ : ∀ w, 0 < w → φ w = ψ w) :
    ∫ w in Ioi (0 : ℝ), ψ w * Real.exp (-(t * twoMonoPath 4 2 a w)) * 1 =
      ∫ w in Ioi (0 : ℝ), φ w * Real.exp (-(t * (w ^ 4 + a * w ^ 2))) := by
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
  have hw0 : (0 : ℝ) < w := hw
  simp only [mul_one, twoMonoPath]
  rw [← hφψ w hw0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]

/-- The half-line two-monomial partition function with real exponents. -/
theorem twoMono_den_eq (t a : ℝ) :
    ∫ w in Ioi (0 : ℝ), Real.exp (-(t * twoMonoPath 4 2 a w)) * 1 =
      ∫ w in Ioi (0 : ℝ), Real.exp (-(t * (w ^ 4 + a * w ^ 2))) := by
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
  simp only [mul_one, twoMonoPath]
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]

/-- **The spectator reduction**: posterior expectations of even functions of `y` in the
two-dimensional family are those of the half-line two-monomial family. -/
theorem spectator_priorExp {t : ℝ} (ht : 0 < t) (a : ℝ) {φ ψ : ℝ → ℝ} (hφ : ∀ y, φ |y| = φ y)
    (hφψ : ∀ w, 0 < w → φ w = ψ w) :
    priorExp volume (fun _ ↦ (1 : ℝ)) (spectatorPath a) (fun p ↦ φ p.2) t =
      priorExp (volume.restrict (Ioi 0)) (fun _ ↦ (1 : ℝ)) (twoMonoPath 4 2 a) ψ t := by
  have hG : (∫ x : ℝ, Real.exp (-(t * x ^ 2))) ≠ 0 := by
    have := integral_gaussian t
    simp only [neg_mul] at this
    rw [this]
    exact (Real.sqrt_pos.mpr (div_pos Real.pi_pos ht)).ne'
  unfold priorExp priorZ
  have h0 := spectator_num t a (fun _ ↦ 1)
  simp only [one_mul] at h0
  rw [spectator_num t a φ, h0,
    integral_even_eq_two_Ioi (F := fun y ↦ φ y * Real.exp (-(t * (y ^ 4 + a * y ^ 2))))
      (spectator_even t a hφ),
    integral_even_eq_two_Ioi (F := fun y ↦ Real.exp (-(t * (y ^ 4 + a * y ^ 2))))
      (spectator_weight_even t a),
    twoMono_num_eq t a hφψ, twoMono_den_eq t a, mul_div_mul_left _ _ hG,
    mul_div_mul_left _ _ two_ne_zero]

/-- **The spectator mode does not respond**: the Fisher speed of the two-dimensional family is
that of the half-line two-monomial family `w⁴ + a w²`. -/
theorem spectator_fisherSpeed {t : ℝ} (ht : 0 < t) (a : ℝ) :
    fisherSpeed volume (fun _ ↦ (1 : ℝ)) spectatorPath spectatorVel t a =
      fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ (1 : ℝ)) (twoMonoPath 4 2) (twoMonoVel 2)
        t a := by
  simp only [fisherSpeed, priorCov]
  have e1 : spectatorVel a = fun p ↦ (fun y ↦ y ^ 2) p.2 := rfl
  have e2 : (fun x ↦ spectatorVel a x * spectatorVel a x) =
      fun p ↦ (fun y ↦ y ^ 2 * y ^ 2) p.2 := rfl
  have f1 : twoMonoVel 2 a = fun w ↦ w ^ (2 : ℝ) := rfl
  have f2 : (fun x ↦ twoMonoVel 2 a x * twoMonoVel 2 a x) = fun w ↦ w ^ (2 : ℝ) * w ^ (2 : ℝ) := rfl
  rw [e2, e1, f2, f1,
    spectator_priorExp ht a (φ := fun y ↦ y ^ 2 * y ^ 2) (ψ := fun w ↦ w ^ (2 : ℝ) * w ^ (2 : ℝ))
      (fun y ↦ by simp [sq_abs]) (fun w _ ↦ by rw [Real.rpow_two]),
    spectator_priorExp ht a (φ := fun y ↦ y ^ 2) (ψ := fun w ↦ w ^ (2 : ℝ))
      (fun y ↦ by simp [sq_abs]) (fun w _ ↦ by rw [Real.rpow_two])]

/-- **The receding wall with a spectator**: `ℓ_t / log t → (1/2) √(1/2) = 1/(2√2)`, not `1/2`. -/
theorem spectator_wall_recedes {a₁ : ℝ} (ha₁ : 0 < a₁) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    Tendsto (fun t ↦ (∫ a in (c₀ * t ^ (-(1 - (2 : ℝ) / 4)))..a₁, Real.sqrt (fisherSpeed volume
      (fun _ ↦ (1 : ℝ)) spectatorPath spectatorVel t a)) / Real.log t) atTop
      (𝓝 ((1 - (2 : ℝ) / 4) * Real.sqrt (1 / 2))) := by
  have key := wall_recedes (p := 4) (q := 2) (by norm_num) (by norm_num) (by norm_num) ha₁ hc₀
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  congr 1
  refine intervalIntegral.integral_congr fun a _ ↦ ?_
  rw [spectator_fisherSpeed ht a]

end Laplace.Multi
