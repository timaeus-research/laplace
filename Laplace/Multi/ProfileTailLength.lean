/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ThermoLengthAsymptotic

/-!
# The profile-tail wall theorem (weak form)

Suppose the thermodynamic length from the wall window `c₀ t^{-σ}` to a fixed data point `a₁` is
given, after the wall rescaling, by `∫_{c₀}^{a₁ t^σ} h(c) dc` for a profile speed `h` — as is
exactly the case for the two-monomial family (`wall_window_length`). If the profile speed has the
tail `c h(c) → √κ` (the *response-active exponent* `κ = lim c² Var_c(R)`), then

  `ℓ_t / log t → σ √κ`   (`tendsto_integral_div_log_scaled`):

**the wall recedes logarithmically**, at the rate "logarithmic scale range `σ` × limiting dilation
speed `√κ`" (Astra, round 23). It is the Cesàro lemma `tendsto_intervalIntegral_div_log` of
`ThermoLengthAsymptotic` read along the moving endpoint `T(t) = a₁ t^σ`, whose logarithm is
`σ log t + log a₁`. The strong form (a convergent renormalised remainder) needs the integrable tail
`h(c) − √κ/c ∈ L¹([1,∞))`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- **The profile-tail wall theorem (weak form)**: if `c h(c) → √κ` then
`(∫_{c₀}^{a₁ t^σ} h) / log t → σ √κ`. -/
theorem tendsto_integral_div_log_scaled {h : ℝ → ℝ} {L : ℝ}
    (hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable h volume a b)
    (hlim : Tendsto (fun c ↦ c * h c) atTop (𝓝 L)) {σ a₁ : ℝ} (hσ : 0 < σ) (ha₁ : 0 < a₁)
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    Tendsto (fun t ↦ (∫ c in c₀..(a₁ * t ^ σ), h c) / Real.log t) atTop (𝓝 (σ * L)) := by
  -- the moving endpoint tends to infinity
  have hT : Tendsto (fun t : ℝ ↦ a₁ * t ^ σ) atTop atTop :=
    (tendsto_rpow_atTop hσ).const_mul_atTop ha₁
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  -- Cesàro along the moving endpoint
  have h1 : Tendsto (fun t ↦ (∫ c in (0 : ℝ)..(a₁ * t ^ σ), h c) / Real.log (a₁ * t ^ σ)) atTop
      (𝓝 L) := (tendsto_intervalIntegral_div_log hint hlim).comp hT
  -- `log (a₁ t^σ) / log t → σ`
  have h2 : Tendsto (fun t ↦ Real.log (a₁ * t ^ σ) / Real.log t) atTop (𝓝 σ) := by
    have h3 : Tendsto (fun t ↦ Real.log a₁ / Real.log t + σ) atTop (𝓝 (0 + σ)) :=
      (tendsto_const_nhds.div_atTop hlog).add tendsto_const_nhds
    rw [zero_add] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have hlt : 0 < Real.log t := Real.log_pos ht
    rw [Real.log_mul ha₁.ne' (Real.rpow_pos_of_pos (by linarith) σ).ne',
      Real.log_rpow (by linarith), add_div, mul_div_assoc, div_self hlt.ne', mul_one]
  -- the fixed lower piece is negligible
  have h4 : Tendsto (fun t ↦ (∫ c in (0 : ℝ)..c₀, h c) / Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have key : Tendsto (fun t ↦ (∫ c in (0 : ℝ)..(a₁ * t ^ σ), h c) / Real.log (a₁ * t ^ σ) *
      (Real.log (a₁ * t ^ σ) / Real.log t) - (∫ c in (0 : ℝ)..c₀, h c) / Real.log t) atTop
      (𝓝 (L * σ - 0)) := (h1.mul h2).sub h4
  rw [sub_zero, mul_comm] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), (hlog.comp hT).eventually_gt_atTop 0] with t ht hlT
  have hlT' : 0 < Real.log (a₁ * t ^ σ) := hlT
  have hTpos : 0 ≤ a₁ * t ^ σ := (mul_pos ha₁ (Real.rpow_pos_of_pos (by linarith) σ)).le
  rw [div_mul_div_comm, mul_comm _ (Real.log (a₁ * t ^ σ)), mul_div_mul_left _ _ hlT'.ne',
    ← sub_div, intervalIntegral.integral_interval_sub_left (hint 0 _ le_rfl hTpos)
      (hint 0 c₀ le_rfl hc₀)]

end Laplace.Multi
