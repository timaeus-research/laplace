/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WallLogMultiplicity

/-!
# The second crossover of the wall example: `s = c/t`

Astra (round 20) pointed out that the additive profile `t Z = log (1 + e^τ) + o(1)` of
`WallLogMultiplicity` is valid only while `t s → ∞`; at the scale `s = c/t` there is a second
crossover, where the logarithmic coefficient saturates:

  `t Z(t, c/t) − log t → −log c − E₁(c)`,   `E₁(c) = ∫_c^∞ e^{-u}/u du`
  (`tendsto_wallZ_second`).

So along `s = t^{-σ}` the leading order is `σ t^{-1} log t` for `0 < σ < 1` and `t^{-1} log t`
(with a `c`-dependent constant and an additive shift) for `σ ≥ 1`: the coupled-limit exponent of
the log multiplicity is `min(σ, 1)`, itself a piecewise affine function with a wall at `σ = 1`.
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

/-- The exponential integral `E₁(c) = ∫_c^∞ e^{-u}/u du`. -/
noncomputable def expIntE1 (c : ℝ) : ℝ := ∫ u in Ioi c, Real.exp (-u) / u

theorem integrableOn_exp_neg_div_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-u) / u) (Ioi c) := by
  have h := (exp_neg_integrableOn_Ioi c one_pos).const_mul (1 / c)
  refine h.mono' ((Real.continuous_exp.comp continuous_neg).measurable.div
    measurable_id).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu ↦ ?_)
  have hu0 : 0 < u := hc.trans hu
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) hu0), neg_one_mul,
    div_le_iff₀ hu0]
  have h1 : 1 ≤ u / c := (one_le_div hc).mpr (le_of_lt hu)
  calc Real.exp (-u) = Real.exp (-u) * 1 := by ring
    _ ≤ Real.exp (-u) * (u / c) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = 1 / c * Real.exp (-u) * u := by ring

/-- **The second crossover**: `t Z(t, c/t) − log t → −log c − E₁(c)`. -/
theorem tendsto_wallZ_second {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t ↦ t * wallZ t (c / t) - Real.log t) atTop (𝓝 (-Real.log c - expIntE1 c)) := by
  have hrem : Tendsto (fun t ↦ wallRem t (c / t)) atTop (𝓝 (expIntE1 c)) := by
    have := intervalIntegral_tendsto_integral_Ioi c (integrableOn_exp_neg_div_Ioi hc)
      (tendsto_atTop_add_const_right atTop c tendsto_id)
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    unfold wallRem
    rw [mul_div_cancel₀ _ ht.ne', show t * (1 + c / t) = t + c by field_simp]
    rfl
  have hlog : Tendsto (fun t ↦ Real.log (1 + c / t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ ↦ 1 + c / t) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at h1
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at this
    exact this
  have key : Tendsto (fun t ↦ Real.log (1 + c / t) - Real.log c - wallRem t (c / t)) atTop
      (𝓝 (0 - Real.log c - expIntE1 c)) := (hlog.sub tendsto_const_nhds).sub hrem
  rw [zero_sub] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hs : 0 < c / t := div_pos hc ht
  rw [wallZ_eq ht hs]
  have hl : Real.log ((1 + c / t) / (c / t)) = Real.log (1 + c / t) + Real.log t - Real.log c := by
    rw [Real.log_div (by positivity) hs.ne', Real.log_div hc.ne' ht.ne']
    ring
  rw [hl]
  ring

end Laplace.Multi
