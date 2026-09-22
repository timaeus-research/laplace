/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RelativeChartFamily

/-!
# The second failure mode: two charts competing when a leading amplitude vanishes

At a wall of the second kind the exponent data of the charts do not change; the amplitude of the
chart with the smaller exponent `e₁` goes to zero. With the amplitude scaled by `c`, the two chart
integrals `c · I₁(t) + I₂(t)` compete, and along `c = σ t^{-(e₂ - e₁)}` the leading order of
`t^{e₂}(c I₁ + I₂)` is `σ C₁ + C₂` (`two_chart_competition`): the combined variable is
`c · t^{e₂ - e₁}`, the general form of the S8/S10 collapse for this mechanism. The normalised
expectation of a test crosses from `C₂^g/C₂^1` (the chamber where chart 2 leads, `σ = 0`) to
`C₁^g/C₁^1` (`σ → ∞`) along the Möbius function `(σ C₁^g + C₂^g)/(σ C₁^1 + C₂^1)`
(`two_chart_competition_ratio`), and an observable whose two chamber values agree is constant
across the whole crossover (`ratio_const_of_chamber_values_eq`): the wall is invisible to it.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {n : ℕ}

/-- **Two-chart competition.** -/
theorem two_chart_competition {k₁ h₁ k₂ h₂ : ℕ} {a₁ b₁ χ₁ a₂ b₂ χ₂ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc₁ : ChartData k₁ h₁ a₁ b₁ χ₁ a₀) (hc₂ : ChartData k₂ h₂ a₂ b₂ χ₂ a₀) {g : EuclidD n → ℝ}
    (hg : Continuous g) (σ : ℝ) :
    Tendsto (fun t ↦ t ^ chartExp k₂ h₂ *
      (σ * t ^ (-(chartExp k₂ h₂ - chartExp k₁ h₁)) * chartIntegral k₁ h₁ a₁ b₁ χ₁ g t +
        chartIntegral k₂ h₂ a₂ b₂ χ₂ g t)) atTop
      (𝓝 (σ * chartCoeff k₁ h₁ a₁ b₁ χ₁ g + chartCoeff k₂ h₂ a₂ b₂ χ₂ g)) := by
  have h1 := hc₁.tendsto_rpow_mul_chartIntegral hg
  have h2 := hc₂.tendsto_rpow_mul_chartIntegral hg
  have := (h1.const_mul σ).add h2
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hexp : t ^ chartExp k₂ h₂ * t ^ (-(chartExp k₂ h₂ - chartExp k₁ h₁)) =
      t ^ chartExp k₁ h₁ := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  unfold chartExp at hexp ⊢
  calc σ * (t ^ (((h₁ : ℝ) + 1) / (2 * k₁)) * chartIntegral k₁ h₁ a₁ b₁ χ₁ g t) +
        t ^ (((h₂ : ℝ) + 1) / (2 * k₂)) * chartIntegral k₂ h₂ a₂ b₂ χ₂ g t
      = σ * ((t ^ (((h₂ : ℝ) + 1) / (2 * k₂)) *
          t ^ (-(((h₂ : ℝ) + 1) / (2 * k₂) - ((h₁ : ℝ) + 1) / (2 * k₁)))) *
          chartIntegral k₁ h₁ a₁ b₁ χ₁ g t) +
        t ^ (((h₂ : ℝ) + 1) / (2 * k₂)) * chartIntegral k₂ h₂ a₂ b₂ χ₂ g t := by rw [hexp]
    _ = _ := by ring

/-- The normalised expectation of `g` along the competition, as a ratio. -/
theorem two_chart_competition_ratio {k₁ h₁ k₂ h₂ : ℕ} {a₁ b₁ χ₁ a₂ b₂ χ₂ : ℝ × EuclidD n → ℝ}
    {a₀ : ℝ} (hc₁ : ChartData k₁ h₁ a₁ b₁ χ₁ a₀) (hc₂ : ChartData k₂ h₂ a₂ b₂ χ₂ a₀)
    {g : EuclidD n → ℝ} (hg : Continuous g) (σ : ℝ)
    (hZ : σ * chartCoeff k₁ h₁ a₁ b₁ χ₁ (fun _ ↦ 1) + chartCoeff k₂ h₂ a₂ b₂ χ₂ (fun _ ↦ 1) ≠ 0) :
    Tendsto (fun t ↦
      (σ * t ^ (-(chartExp k₂ h₂ - chartExp k₁ h₁)) * chartIntegral k₁ h₁ a₁ b₁ χ₁ g t +
          chartIntegral k₂ h₂ a₂ b₂ χ₂ g t) /
        (σ * t ^ (-(chartExp k₂ h₂ - chartExp k₁ h₁)) * chartIntegral k₁ h₁ a₁ b₁ χ₁ (fun _ ↦ 1) t +
          chartIntegral k₂ h₂ a₂ b₂ χ₂ (fun _ ↦ 1) t)) atTop
      (𝓝 ((σ * chartCoeff k₁ h₁ a₁ b₁ χ₁ g + chartCoeff k₂ h₂ a₂ b₂ χ₂ g) /
        (σ * chartCoeff k₁ h₁ a₁ b₁ χ₁ (fun _ ↦ 1) + chartCoeff k₂ h₂ a₂ b₂ χ₂ (fun _ ↦ 1)))) := by
  have hN := two_chart_competition hc₁ hc₂ hg σ
  have hD := two_chart_competition hc₁ hc₂ (g := fun _ ↦ (1 : ℝ)) continuous_const σ
  have := hN.div hD hZ
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Pi.div_apply]
  rw [mul_div_mul_left _ _ (Real.rpow_pos_of_pos ht _).ne']

/-- **A wall is invisible to an observable whose chamber values agree**: the crossover ratio is
then constant in `σ`. -/
theorem ratio_const_of_chamber_values_eq {A B C D ℓ : ℝ} (hA : A = ℓ * C) (hB : B = ℓ * D)
    (σ : ℝ) (hne : σ * C + D ≠ 0) : (σ * A + B) / (σ * C + D) = ℓ := by
  rw [hA, hB, show σ * (ℓ * C) + ℓ * D = ℓ * (σ * C + D) by ring, mul_div_assoc,
    div_self hne, mul_one]

end Laplace.Multi
