/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Laplace.Grammar.HeadlinePosterior

/-!
# The constant-Gaussian fluctuation model: expected leading moment (grammar §4.3, rem:pop_vs_emp)

The leading coefficient is `A_p = y₀₀/(k₁k₂) J_p(x₀₀)` with the positive Gaussian moment
`J_p(x) = ∫₀^∞ s^{p−1} e^{−βs²} e^{βsx} ds` (units 124, 154). If the constant fluctuation `x₀₀ = X`
is Gaussian `N(0, v)`, Tonelli and the Gaussian moment generating function give the identity
(in the extended nonnegative reals, so that `+∞` is a legitimate value)

`E₊[J_p(X)] = ∫₀^∞ s^{p−1} e^{−βs²} e^{v(βs)²/2} ds` (`lintegral_gaussMoment_eq`).

The right-hand side is finite iff `βv < 2` (next unit): the expected leading coefficient can be
infinite although every sample coefficient is finite, which is the content of the paper's remark
that "E[C(ξ_n)] ≠ C(0)" and of the temperature threshold. Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace Laplace.Grammar

/-- The Gaussian moment `J_p(x) = ∫₀^∞ s^{p−1} e^{−βs²} e^{βsx} ds` as a function of `x`. -/
noncomputable def gaussMomentJ (β p x : ℝ) : ℝ :=
  logMoment β p 0 (fun s => Real.exp (β * s * x))

theorem gaussMomentJ_pos (β p x : ℝ) (hβ : 0 < β) (hp : 0 < p) : 0 < gaussMomentJ β p x :=
  logMoment_exp_pos β p x hβ hp

/-- The integrand of `J_p`, jointly measurable in `(ω, s)`. -/
theorem measurable_gaussMoment_integrand {Ω : Type*} [MeasurableSpace Ω] (β p : ℝ) (X : Ω → ℝ)
    (hX : Measurable X) :
    Measurable fun q : Ω × ℝ => ENNReal.ofReal (q.2 ^ (p - 1) * Real.log q.2 ^ 0
      * (Real.exp (-β * q.2 ^ 2) * Real.exp (β * q.2 * X q.1))) := by
  refine Measurable.ennreal_ofReal ?_
  refine ((measurable_snd.pow_const (p - 1)).mul
      ((Real.measurable_log.comp measurable_snd).pow_const 0)).mul
    (Measurable.mul (Real.measurable_exp.comp (measurable_const.mul (measurable_snd.pow_const 2)))
      (Real.measurable_exp.comp ((measurable_const.mul measurable_snd).mul
        (hX.comp measurable_fst))))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The exponential moment of a Gaussian variable as a Lebesgue integral. -/
theorem lintegral_exp_gaussian (X : Ω → ℝ) (hX : Measurable X) (v : NNReal)
    (hXg : μ.map X = gaussianReal 0 v) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂μ = ENNReal.ofReal (Real.exp (v * t ^ 2 / 2)) := by
  have hint : Integrable (fun ω => Real.exp (t * X ω)) μ := by
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hXg] at h
    have hg : AEStronglyMeasurable (fun x : ℝ => Real.exp (t * x)) (μ.map X) :=
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
    exact (integrable_map_measure hg hX.aemeasurable).1 h
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω =>
    (Real.exp_pos _).le)]
  congr 1
  have := mgf_gaussianReal hXg t
  unfold mgf at this
  rw [this, zero_mul, zero_add]

/-- **Tonelli identity for the expected Gaussian moment.** -/
theorem lintegral_gaussMomentJ_eq (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (X : Ω → ℝ)
    (hX : Measurable X) (v : NNReal) (hXg : μ.map X = gaussianReal 0 v) :
    ∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (p - 1) * Real.exp (-β * s ^ 2)
          * Real.exp (v * (β * s) ^ 2 / 2)) := by
  -- express each `J_p(X ω)` as a Lebesgue integral
  have h1 : ∀ ω, ENNReal.ofReal (gaussMomentJ β p (X ω))
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (p - 1) * Real.log s ^ 0
          * (Real.exp (-β * s ^ 2) * Real.exp (β * s * X ω))) := by
    intro ω
    unfold gaussMomentJ logMoment
    refine ofReal_integral_eq_lintegral_ofReal (gaussMoment_exp_integrableOn β p (X ω) hβ hp) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    have : 0 < s ^ (p - 1) := Real.rpow_pos_of_pos hs _
    change (0 : ℝ) ≤ s ^ (p - 1) * Real.log s ^ 0 * (Real.exp (-β * s ^ 2) * Real.exp (β * s * X ω))
    positivity
  simp_rw [h1]
  -- swap the order of integration
  rw [lintegral_lintegral_swap (measurable_gaussMoment_integrand β p X hX).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  have hnn : 0 ≤ s ^ (p - 1) * Real.log s ^ 0 * Real.exp (-β * s ^ 2) := by
    have : 0 < s ^ (p - 1) := Real.rpow_pos_of_pos hs0 _
    positivity
  calc ∫⁻ ω, ENNReal.ofReal (s ^ (p - 1) * Real.log s ^ 0
          * (Real.exp (-β * s ^ 2) * Real.exp (β * s * X ω))) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (s ^ (p - 1) * Real.log s ^ 0 * Real.exp (-β * s ^ 2))
          * ENNReal.ofReal (Real.exp ((β * s) * X ω)) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [← ENNReal.ofReal_mul hnn]
        congr 1; ring
    _ = ENNReal.ofReal (s ^ (p - 1) * Real.log s ^ 0 * Real.exp (-β * s ^ 2))
          * ∫⁻ ω, ENNReal.ofReal (Real.exp ((β * s) * X ω)) ∂μ := lintegral_const_mul _ (by
            exact Measurable.ennreal_ofReal
              (Real.measurable_exp.comp (measurable_const.mul hX)))
    _ = ENNReal.ofReal (s ^ (p - 1) * Real.exp (-β * s ^ 2) * Real.exp (v * (β * s) ^ 2 / 2)) := by
        rw [lintegral_exp_gaussian X hX v hXg (β * s), ← ENNReal.ofReal_mul hnn]
        congr 1
        rw [pow_zero, mul_one]

end Laplace.Grammar
