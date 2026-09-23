/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The logarithmic substitution on a coordinate

The change of variables `x = e^{−y/A}` on `(0, 1)`: for measurable `G ≥ 0`,
`∫⁻_{(0,1)} x^h G(x^A) dx = ∫⁻_{(0,∞)} (1/A) e^{−(h+1) y/A} G(e^{−y}) dy`
(`lintegral_Ioo_rpow_mul_comp_rpow`). This is the coordinatewise step of the single-monomial
power–log theorem: in the tied block `(h_i + 1)/A_i = λ` the density becomes `(1/A_i) e^{−λ y_i}`
and the monomial becomes `e^{−∑ y_i}`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

/-- The image of `(0, ∞)` under `y ↦ e^{−y/A}` is `(0, 1)`. -/
theorem image_exp_neg_div_Ioi {A : ℝ} (hA : 0 < A) :
    (fun y : ℝ ↦ exp (-(y / A))) '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy : 0 < y := hy
    refine ⟨exp_pos _, ?_⟩
    calc exp (-(y / A)) < exp 0 := Real.exp_lt_exp.mpr (by have := div_pos hy hA; linarith)
      _ = 1 := Real.exp_zero
  · rintro ⟨hx0, hx1⟩
    refine ⟨-(A * log x), ?_, ?_⟩
    · have : log x < 0 := log_neg hx0 hx1
      change 0 < -(A * log x)
      nlinarith
    · simp only
      rw [neg_div, neg_neg, mul_div_cancel_left₀ _ hA.ne', exp_log hx0]

/-- **The logarithmic substitution.** -/
theorem lintegral_Ioo_rpow_mul_comp_rpow {A : ℝ} (hA : 0 < A) (h : ℝ) (G : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ h) * G (x ^ A) =
      ∫⁻ y in Ioi 0, ENNReal.ofReal (exp (-((h + 1) / A * y)) / A) * G (exp (-y)) := by
  have hder : ∀ y ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun y ↦ exp (-(y / A)))
      (-(1 / A) * exp (-(y / A))) (Ioi 0) y := fun y _ ↦ by
    have := ((hasDerivAt_id y).div_const A).neg.exp
    simpa [neg_div, mul_comm] using this.hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ ↦ exp (-(y / A))) (Ioi 0) := by
    intro y₁ _ y₂ _ hy
    have h1 := exp_injective hy
    have h2 : y₁ / A = y₂ / A := neg_injective h1
    exact (div_left_inj' hA.ne').mp h2
  rw [← image_exp_neg_div_Ioi hA, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    hder hinj]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  have e1 : exp (-(y / A)) ^ A = exp (-y) := by
    rw [← Real.exp_mul]; congr 1; field_simp
  have e2 : exp (-(y / A)) ^ h = exp (-(y / A) * h) := by rw [← Real.exp_mul]
  rw [e1, e2, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hA), abs_of_pos (exp_pos _),
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have e3 : -(y / A) + -(y / A) * h = -((h + 1) / A * y) := by ring
  rw [mul_assoc, ← Real.exp_add, e3]
  ring

end Laplace.Multi
