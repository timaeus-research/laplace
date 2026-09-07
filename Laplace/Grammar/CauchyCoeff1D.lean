/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TaylorTreeWrapper

/-!
# The one-variable Cauchy-estimate bridge (pilot, Stage 6a)

Unit 257 (Astra #30 candidate C₁, scouting gate). For `f : ℂ → ℂ` with `DifferentiableOn ℂ f
(closedBall 0 r)` ("holomorphic on the closed disc" below is shorthand for this hypothesis, which
the
paper's holomorphy on the larger open disc `|z| < R` supplies for every `r < R`), Mathlib's Cauchy
power series `cauchyPowerSeries f 0 r` represents `f` on the open disc. The estimate and the
weighted
summability are stated for arbitrary `f` (Lean's totalised contour integrals); they are used only
under the differentiability hypothesis.
Its scalar coefficients `discCoeff f r n` satisfy
```
∑_n discCoeff f r n · z^n = f z            (|z| < r; `hasSum_discCoeff`),
‖discCoeff f r n‖ ≤ M_r · r^{-n}            (`norm_discCoeff_le`, Cauchy estimate with the circle
                                             average `M_r` of `‖f‖`),
∑_n ‖discCoeff f r n‖ b^n < ∞               (`summable_norm_discCoeff_mul_pow`, every `0 ≤ b < r`),
discCoeff f r n = iteratedDeriv n f 0 / n!  (`discCoeff_eq_iteratedDeriv_div`, uniqueness of power
                                             series at `0`).
```
This is the gate of the analytic bridge: from the paper's hypothesis (holomorphy on a disc of radius
`R > b`) to weighted absolute summability of the normalised Taylor coefficients at radius `b`, in
    one
variable. Reality of the coefficients for real-valued `f` and the transfer to the coefficient-family
Taylor tree are the next units. No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

/-- The `n`-th scalar coefficient of the Cauchy power series of `f` on the disc of radius `r`. -/
noncomputable def discCoeff (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : ℂ := (cauchyPowerSeries f 0 r).coeff n

/-- The circle average of `‖f‖` on `|z| = r`: the Cauchy-estimate constant `M_r`. -/
noncomputable def circleAvgNorm (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 r θ)‖

/-- **Cauchy estimate**: `‖discCoeff f r n‖ ≤ M_r r^{-n}`. -/
theorem norm_discCoeff_le (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ‖discCoeff f r n‖ ≤ circleAvgNorm f r * r⁻¹ ^ n := by
  unfold discCoeff circleAvgNorm
  rw [← FormalMultilinearSeries.norm_apply_eq_norm_coef]
  have := norm_cauchyPowerSeries_le f 0 r n
  rwa [abs_of_pos hr] at this

/-- **Representation on the open disc**: `∑_n discCoeff f r n · z^n = f z` for `‖z‖ < r`. -/
theorem hasSum_discCoeff {f : ℂ → ℂ} {r : NNReal} (hf : DifferentiableOn ℂ f (Metric.closedBall 0
    r))
    (hr : 0 < r) {z : ℂ} (hz : ‖z‖ < r) :
    HasSum (fun n => discCoeff f r n * z ^ n) (f z) := by
  have hps := hf.hasFPowerSeriesOnBall hr
  have hz' : z ∈ Metric.eball (0 : ℂ) (r : ENNReal) := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.coe_nnreal_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hr)).2 hz
  have := hps.hasSum hz'
  rw [zero_add] at this
  refine this.congr_fun fun n => ?_
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
  unfold discCoeff
  ring

/-- **Weighted absolute summability** at every radius `0 ≤ b < r`. -/
theorem summable_norm_discCoeff_mul_pow (f : ℂ → ℂ) {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (hbr : b
    < r) :
    Summable fun n => ‖discCoeff f r n‖ * b ^ n := by
  have hgeo : Summable fun n : ℕ => circleAvgNorm f r * (b / r) ^ n :=
    (summable_geometric_of_lt_one (div_nonneg hb hr.le) ((div_lt_one hr).2 hbr)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  calc ‖discCoeff f r n‖ * b ^ n ≤ circleAvgNorm f r * r⁻¹ ^ n * b ^ n :=
        mul_le_mul_of_nonneg_right (norm_discCoeff_le f hr n) (pow_nonneg hb _)
    _ = circleAvgNorm f r * (b / r) ^ n := by rw [div_eq_mul_inv, mul_pow]; ring

/-- The Cauchy coefficients are the normalised Taylor coefficients `f^{(n)}(0)/n!`. -/
theorem discCoeff_eq_iteratedDeriv_div {f : ℂ → ℂ} {r : NNReal}
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 r)) (hr : 0 < r) (n : ℕ) :
    discCoeff f r n = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  have hps := (hf.hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  have han : AnalyticAt ℂ f 0 := hps.analyticAt
  have huniq := hps.eq_formalMultilinearSeries han.hasFPowerSeriesAt
  unfold discCoeff
  rw [huniq]
  simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]

end Laplace.Grammar
