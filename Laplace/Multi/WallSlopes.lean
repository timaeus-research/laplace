/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ToyCrossoverResponse
import Laplace.Multi.MergingZeros

/-!
# The initial slope of a crossover distinguishes the two kinds of wall

Both one-dimensional walls of type `1/4 → 1/2` have their crossover functions in a squared
variable: the degenerating-unit wall `x²(x² + u²)` in `s = u²√t` (`crossover`, S8) and the
merging-zeros wall `x²(x − s)²` in `a = σ²/4 = s²√t/4` (`doubleWell`). Both start at `1/4` and
end at `1/2`, but with opposite initial slopes:

* `G'(0) = Γ(3/4)/(2Γ(1/4)) > 0` for the degenerating unit (`deriv_crossover_zero`);
* `doubleWell'(0) = −Γ(3/4)/Γ(1/4) < 0` for merging zeros (`deriv_doubleWell_zero`),

so the merging-zeros energy statistic UNDERSHOOTS the wall value before rising (the dip seen in the
S10 zoo), and the ratio of the slopes is exactly `−2` (`deriv_doubleWell_zero_eq_neg_two_mul`).
The sign of the initial response at a wall is therefore a finite-temperature diagnostic of the
mechanism: a unit losing its lower bound versus two zeros merging.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### Moments of `e^{-w⁴}` -/

theorem agmom_two (j : ℕ) : agmom 2 j = Real.Gamma (((j : ℝ) + 1) / 4) / 2 := by
  rw [agmom_eq_Gamma 2 (by norm_num) j]
  norm_num

theorem Gamma_quarter_pos : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
theorem Gamma_three_quarter_pos : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)

theorem Gamma_five_quarter : Real.Gamma (5 / 4) = 1 / 4 * Real.Gamma (1 / 4) := by
  rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]

theorem Gamma_seven_quarter : Real.Gamma (7 / 4) = 3 / 4 * Real.Gamma (3 / 4) := by
  rw [show (7 / 4 : ℝ) = 3 / 4 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]

/-- `∫ w^{2j} e^{-w⁴} = agmom 2 (2j)`. -/
theorem integral_pow_exp_neg_quartic (j : ℕ) :
    (∫ w : ℝ, w ^ (2 * j) * Real.exp (-w ^ 4)) = agmom 2 (2 * j) := by
  unfold agmom
  refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only
  rw [abs_pow_even]

theorem integrable_pow_mul_exp_neg_quartic' (j : ℕ) :
    Integrable fun w : ℝ ↦ w ^ j * Real.exp (-w ^ 4) := by
  have := integrable_pow_mul_exp_neg_mul_pow one_pos 2 (by norm_num) j
  simpa using this

/-! ### The degenerating-unit wall: `G'(0) = Γ(3/4)/(2Γ(1/4))` -/

theorem cw_zero (y : ℝ) : cw 0 y = Real.exp (-y ^ 4) := by
  simp [cw]

theorem crossExp_zero_pow (j : ℕ) :
    crossExp 0 (fun y ↦ y ^ (2 * j)) = agmom 2 (2 * j) / agmom 2 0 := by
  unfold crossExp
  simp only [cw_zero]
  rw [integral_pow_exp_neg_quartic]
  congr 1
  have := integral_pow_exp_neg_quartic 0
  simpa using this

/-- **The degenerating-unit crossover starts upward.** -/
theorem deriv_crossover_zero :
    deriv crossover 0 = Real.Gamma (3 / 4) / (2 * Real.Gamma (1 / 4)) := by
  rw [(hasDerivAt_crossover 0).deriv]
  unfold crossCov
  have h2 := crossExp_zero_pow 1
  have h4 := crossExp_zero_pow 2
  have hf6 : (fun y : ℝ ↦ cE 0 y * y ^ 2) = fun y ↦ y ^ (2 * 3) := by
    funext y
    simp only [cE, zero_mul, add_zero]
    ring
  have hf4 : cE 0 = fun y : ℝ ↦ y ^ (2 * 2) := by
    funext y
    simp only [cE, zero_mul, add_zero]
  have h6 := crossExp_zero_pow 3
  simp only [mul_one] at h2
  rw [hf6, hf4, h2, h6, h4]
  rw [agmom_two, agmom_two, agmom_two, agmom_two]
  norm_num
  rw [Gamma_five_quarter, Gamma_seven_quarter]
  have hg := Gamma_quarter_pos
  field_simp
  ring

/-! ### The merging-zeros wall: `doubleWell'(0) = −Γ(3/4)/Γ(1/4)` -/

/-- The well `V_a(w) = (w² − a)²` is bounded below by `w⁴/2 − 2a²`. -/
theorem doubleWell_pot_ge (a w : ℝ) : w ^ 4 / 2 - 2 * a ^ 2 ≤ (w ^ 2 - a) ^ 2 := by
  nlinarith [sq_nonneg (w ^ 2 - 2 * a), sq_nonneg a]

theorem abs_sq_sub_le {a w : ℝ} (ha : |a| ≤ 1) : |w ^ 2 - a| ≤ w ^ 2 + 1 := by
  rw [abs_le] at ha
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg w]

/-- Dominating function for the derivative of the double-well integrals near `a = 0`. -/
theorem integrable_dw_dom :
    Integrable fun w : ℝ ↦ Real.exp (1 / 2) *
      (2 * (w ^ 2 + 1) * ((w ^ 2 + 1) ^ 2 + 1)) * Real.exp (-(1 / 2 * w ^ (2 * 2))) := by
  have hG : ∀ j : ℕ, Integrable fun w : ℝ ↦ |w| ^ j * Real.exp (-(1 / 2 * w ^ (2 * 2))) :=
    fun j ↦ integrable_abs_pow_mul_exp_neg_mul_pow (by norm_num) 2 (by norm_num) j
  have := ((((hG 6).const_mul 2).add ((hG 4).const_mul 6)).add
    (((hG 2).const_mul 8).add ((hG 0).const_mul 4))).const_mul (Real.exp (1 / 2))
  refine this.congr (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only [Pi.add_apply, pow_zero]
  have h2 : |w| ^ 2 = w ^ 2 := sq_abs w
  have h4 : |w| ^ 4 = w ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
  have h6 : |w| ^ 6 = w ^ 6 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, pow_mul, sq_abs]
  rw [h2, h4, h6]
  ring

theorem hasDerivAt_dw_den (a w : ℝ) :
    HasDerivAt (fun a ↦ Real.exp (-(w ^ 2 - a) ^ 2)) (2 * (w ^ 2 - a) * Real.exp (-(w ^ 2 - a) ^ 2))
      a := by
  have hV : HasDerivAt (fun a ↦ (w ^ 2 - a) ^ 2) (-(2 * (w ^ 2 - a))) a := by
    have := ((hasDerivAt_id a).const_sub (w ^ 2)).pow 2
    refine this.congr_deriv ?_
    simp
  have hV' : HasDerivAt (fun a ↦ -(w ^ 2 - a) ^ 2) (2 * (w ^ 2 - a)) a := by
    refine hV.neg.congr_deriv ?_
    ring
  have := hV'.exp
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_dw_num (a w : ℝ) :
    HasDerivAt (fun a ↦ (w ^ 2 - a) ^ 2 * Real.exp (-(w ^ 2 - a) ^ 2))
      (2 * (w ^ 2 - a) * ((w ^ 2 - a) ^ 2 - 1) * Real.exp (-(w ^ 2 - a) ^ 2)) a := by
  have hV : HasDerivAt (fun a ↦ (w ^ 2 - a) ^ 2) (-(2 * (w ^ 2 - a))) a := by
    have := ((hasDerivAt_id a).const_sub (w ^ 2)).pow 2
    refine this.congr_deriv ?_
    simp
  have := hV.mul (hasDerivAt_dw_den a w)
  refine this.congr_deriv ?_
  ring

/-- Bound on the exponential factor for `|a| ≤ 1/2`. -/
theorem exp_neg_dw_le {a w : ℝ} (ha : |a| ≤ 1 / 2) :
    Real.exp (-(w ^ 2 - a) ^ 2) ≤ Real.exp (1 / 2) * Real.exp (-(1 / 2 * w ^ (2 * 2))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := doubleWell_pot_ge a w
  have h2 : a ^ 2 ≤ 1 / 4 := by
    rw [abs_le] at ha
    nlinarith
  have : (1 / 2 : ℝ) * w ^ (2 * 2) = w ^ 4 / 2 := by ring
  rw [this]
  linarith

theorem hasDerivAt_doubleWell_zero :
    HasDerivAt doubleWell (-(Real.Gamma (3 / 4) / Real.Gamma (1 / 4))) 0 := by
  have hball : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 (by norm_num)
  have hin : ∀ a ∈ Metric.ball (0 : ℝ) (1 / 2), |a| ≤ 1 / 2 := fun a ha ↦ by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ha
    exact ha.le
  have hdom := integrable_dw_dom
  -- integrability at `a = 0`
  have hsq : ∀ w : ℝ, (w ^ 2) ^ 2 = w ^ 4 := fun w ↦ by ring
  have hi0 : Integrable fun w : ℝ ↦ Real.exp (-(w ^ 2 - 0) ^ 2) := by
    have := integrable_pow_mul_exp_neg_quartic' 0
    refine this.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [pow_zero, one_mul, sub_zero, hsq]
  have hiN : Integrable fun w : ℝ ↦ (w ^ 2 - 0) ^ 2 * Real.exp (-(w ^ 2 - 0) ^ 2) := by
    have := integrable_pow_mul_exp_neg_quartic' 4
    refine this.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [sub_zero, hsq]
  -- the denominator
  have hD : HasDerivAt (fun a ↦ ∫ w, Real.exp (-(w ^ 2 - a) ^ 2))
      (∫ w, 2 * (w ^ 2 - 0) * Real.exp (-(w ^ 2 - 0) ^ 2)) 0 := by
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
      (F := fun a w ↦ Real.exp (-(w ^ 2 - a) ^ 2))
      (F' := fun a w ↦ 2 * (w ^ 2 - a) * Real.exp (-(w ^ 2 - a) ^ 2)) (x₀ := 0)
      (bound := fun w ↦ Real.exp (1 / 2) * (2 * (w ^ 2 + 1) * ((w ^ 2 + 1) ^ 2 + 1)) *
        Real.exp (-(1 / 2 * w ^ (2 * 2))))
      hball (Filter.Eventually.of_forall fun a ↦ by fun_prop) hi0 (by fun_prop)
      (Filter.Eventually.of_forall fun w a ha ↦ by
        have ha' := hin a ha
        rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_mul, abs_two]
        have h1 : |w ^ 2 - a| ≤ w ^ 2 + 1 := abs_sq_sub_le (ha'.trans (by norm_num))
        have h2 := exp_neg_dw_le (w := w) ha'
        have hP : 2 * |w ^ 2 - a| ≤ 2 * (w ^ 2 + 1) * ((w ^ 2 + 1) ^ 2 + 1) := by
          have : (1 : ℝ) ≤ (w ^ 2 + 1) ^ 2 + 1 := by nlinarith [sq_nonneg (w ^ 2 + 1)]
          nlinarith [abs_nonneg (w ^ 2 - a)]
        calc 2 * |w ^ 2 - a| * Real.exp (-(w ^ 2 - a) ^ 2)
            ≤ (2 * (w ^ 2 + 1) * ((w ^ 2 + 1) ^ 2 + 1)) *
              (Real.exp (1 / 2) * Real.exp (-(1 / 2 * w ^ (2 * 2)))) :=
              mul_le_mul hP h2 (Real.exp_pos _).le (by positivity)
          _ = _ := by ring)
      hdom (Filter.Eventually.of_forall fun w a _ ↦ hasDerivAt_dw_den a w)
    exact key.2
  -- the numerator
  have hN : HasDerivAt (fun a ↦ ∫ w, (w ^ 2 - a) ^ 2 * Real.exp (-(w ^ 2 - a) ^ 2))
      (∫ w, 2 * (w ^ 2 - 0) * ((w ^ 2 - 0) ^ 2 - 1) * Real.exp (-(w ^ 2 - 0) ^ 2)) 0 := by
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
      (F := fun a w ↦ (w ^ 2 - a) ^ 2 * Real.exp (-(w ^ 2 - a) ^ 2))
      (F' := fun a w ↦ 2 * (w ^ 2 - a) * ((w ^ 2 - a) ^ 2 - 1) * Real.exp (-(w ^ 2 - a) ^ 2))
      (x₀ := 0)
      (bound := fun w ↦ Real.exp (1 / 2) * (2 * (w ^ 2 + 1) * ((w ^ 2 + 1) ^ 2 + 1)) *
        Real.exp (-(1 / 2 * w ^ (2 * 2))))
      hball (Filter.Eventually.of_forall fun a ↦ by fun_prop) hiN (by fun_prop)
      (Filter.Eventually.of_forall fun w a ha ↦ by
        have ha' := hin a ha
        rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_mul, abs_mul, abs_two]
        have h1 : |w ^ 2 - a| ≤ w ^ 2 + 1 := abs_sq_sub_le (ha'.trans (by norm_num))
        have h2 := exp_neg_dw_le (w := w) ha'
        have hV : (w ^ 2 - a) ^ 2 ≤ (w ^ 2 + 1) ^ 2 := by
          rw [← sq_abs (w ^ 2 - a)]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        have hV1 : |(w ^ 2 - a) ^ 2 - 1| ≤ (w ^ 2 + 1) ^ 2 + 1 := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg (w ^ 2 - a)]
        have hP : 2 * |w ^ 2 - a| * |(w ^ 2 - a) ^ 2 - 1| ≤
            2 * (w ^ 2 + 1) * ((w ^ 2 + 1) ^ 2 + 1) := by
          have := mul_le_mul h1 hV1 (abs_nonneg _) (by positivity)
          nlinarith [abs_nonneg (w ^ 2 - a), abs_nonneg ((w ^ 2 - a) ^ 2 - 1)]
        calc 2 * |w ^ 2 - a| * |(w ^ 2 - a) ^ 2 - 1| * Real.exp (-(w ^ 2 - a) ^ 2)
            ≤ (2 * (w ^ 2 + 1) * ((w ^ 2 + 1) ^ 2 + 1)) *
              (Real.exp (1 / 2) * Real.exp (-(1 / 2 * w ^ (2 * 2)))) :=
              mul_le_mul hP h2 (Real.exp_pos _).le (by positivity)
          _ = _ := by ring)
      hdom (Filter.Eventually.of_forall fun w a _ ↦ hasDerivAt_dw_num a w)
    exact key.2
  -- the quotient, and the values at `0` in Gamma form
  have e0 : (∫ w : ℝ, Real.exp (-(w ^ 2 - 0) ^ 2)) = agmom 2 0 := by
    unfold agmom
    refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [sub_zero, pow_zero, one_mul]
    congr 1
    ring
  have hD0 : (∫ w : ℝ, Real.exp (-(w ^ 2 - 0) ^ 2)) ≠ 0 := by
    rw [e0]
    exact (agmom_pos 2 (by norm_num) 0).ne'
  have hq : HasDerivAt (fun a ↦ (∫ w, (w ^ 2 - a) ^ 2 * Real.exp (-(w ^ 2 - a) ^ 2)) /
      ∫ w, Real.exp (-(w ^ 2 - a) ^ 2)) _ 0 := hN.div hD hD0
  have hfun : (fun a ↦ (∫ w, (w ^ 2 - a) ^ 2 * Real.exp (-(w ^ 2 - a) ^ 2)) /
      ∫ w, Real.exp (-(w ^ 2 - a) ^ 2)) = doubleWell := by
    funext a
    rfl
  rw [hfun] at hq
  refine hq.congr_deriv ?_
  -- evaluate the remaining three integrals
  have habs4 : ∀ w : ℝ, |w| ^ 4 = (w ^ 2) ^ 2 := fun w ↦ by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs]
  have habs6 : ∀ w : ℝ, |w| ^ 6 = (w ^ 2) ^ 3 := fun w ↦ by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sq_abs]
  have e4 : (∫ w : ℝ, (w ^ 2 - 0) ^ 2 * Real.exp (-(w ^ 2 - 0) ^ 2)) = agmom 2 4 := by
    unfold agmom
    refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [sub_zero, habs4]
    congr 2
    ring
  have eD : (∫ w : ℝ, 2 * (w ^ 2 - 0) * Real.exp (-(w ^ 2 - 0) ^ 2)) = 2 * agmom 2 2 := by
    unfold agmom
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [sub_zero, sq_abs]
    ring_nf
  have eN : (∫ w : ℝ, 2 * (w ^ 2 - 0) * ((w ^ 2 - 0) ^ 2 - 1) * Real.exp (-(w ^ 2 - 0) ^ 2)) =
      2 * agmom 2 6 - 2 * agmom 2 2 := by
    unfold agmom
    have hi6 := (integrable_abs_pow_mul_exp_neg_mul_pow one_pos 2 (by norm_num) 6).const_mul 2
    have hi2 := (integrable_abs_pow_mul_exp_neg_mul_pow one_pos 2 (by norm_num) 2).const_mul 2
    simp only [one_mul] at hi6 hi2
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub hi6 hi2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [sub_zero, sq_abs, habs6]
    ring_nf
  rw [eN, eD, e4, e0, agmom_two, agmom_two, agmom_two, agmom_two]
  norm_num
  rw [Gamma_five_quarter, Gamma_seven_quarter]
  have hg := Gamma_quarter_pos
  field_simp
  ring

/-- **The merging-zeros crossover starts downward.** -/
theorem deriv_doubleWell_zero : deriv doubleWell 0 = -(Real.Gamma (3 / 4) / Real.Gamma (1 / 4)) :=
  hasDerivAt_doubleWell_zero.deriv

theorem deriv_doubleWell_zero_neg : deriv doubleWell 0 < 0 := by
  rw [deriv_doubleWell_zero]
  have := div_pos Gamma_three_quarter_pos Gamma_quarter_pos
  linarith

theorem deriv_crossover_zero_pos : 0 < deriv crossover 0 := by
  rw [deriv_crossover_zero]
  exact div_pos Gamma_three_quarter_pos (by linarith [Gamma_quarter_pos])

/-- **The two initial slopes are in the ratio `−2`.** -/
theorem deriv_doubleWell_zero_eq_neg_two_mul :
    deriv doubleWell 0 = -2 * deriv crossover 0 := by
  rw [deriv_doubleWell_zero, deriv_crossover_zero]
  have hg := Gamma_quarter_pos
  field_simp

end Laplace.Multi
