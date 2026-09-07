/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FixedAmplitudeJointLimit

/-!
# The chart posterior limit (grammar §4.3, cor:empirical_expectation at chart level)

For a common random phase converging in distribution and deterministic amplitudes `y_φ`, `y_1` with
`y_{1,00} > 0`, the chart posterior ratio `Z_{N_n}[φ] / Z_{N_n}[1]` converges in distribution to the
deterministic corner-value ratio `y_{φ,00} / y_{1,00}` (`tendstoInDistribution_chart_posterior`).
Proof: the normalised pair converges jointly (unit 158), the limiting denominator
`A_p(Z; y_1) = y_{1,00}/(k₁k₂) ∫ s^{p−1} e^{−βs²+βs x₀₀}` is positive (unit 154), so the quotient of
the normalised integrals converges (unit 157); the common positive factor cancels in the limit
(`coeffA_withY_div`), and the normalisation `s_n` cancels in the quotient for `N_n > 1`. Lean's
totalised division is used; no finite-`n` nonvanishing hypothesis is needed. Astra #13 unit u159.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real

namespace Laplace.Grammar

/-- **Cancellation of the common phase factor** in the ratio of leading coefficients. -/
theorem coeffA_withY_div (β ρ : ℝ) (hρ : 0 < ρ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (yφ y₁ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hy₁0 : 0 < y₁ (0, 0))
    (a : CoeffPair) :
    coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ yφ hyφ a) / coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ y₁ hy₁ a)
      = yφ (0, 0) / y₁ (0, 0) := by
  unfold coeffA
  simp only [toX_withY, toY_withY]
  rw [leading_log_coeff β h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂, leading_log_coeff β h₁ h₂ k₁ k₂ hk₁ hk₂ p
    hp₁ hp₂]
  have hk : (0 : ℝ) < (k₁ : ℝ) * k₂ := by exact_mod_cast Nat.mul_pos hk₁ hk₂
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hp : 0 < p := by rw [← hp₁]; positivity
  set M := logMoment β p 0 (fun s => Real.exp (β * s * toX ρ a (0, 0))) with hMdef
  have hM : 0 < M := logMoment_exp_pos β p (toX ρ a (0, 0)) hβ hp
  field_simp

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- The quotient of the normalised chart integrals converges to the corner-value ratio. -/
theorem tendstoInDistribution_normA_div (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (yφ y₁ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hy₁0 : 0 < y₁ (0, 0))
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (Z : Ω' → CoeffPair)
    (hZm : Measurable Z) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun n ω =>
        normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) yφ hyφ (X n ω))
          / normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) y₁ hy₁ (X n ω))) l
      (fun _ => yφ (0, 0) / y₁ (0, 0)) (fun _ => μ) μ' := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  have hp0 : 0 < p := by
    rw [← hp₁]; have : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
    positivity
  have hpair := tendstoInDistribution_normA_pair β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂
    hp₁ hp₂ hpT yφ y₁ hyφ hy₁ X hXm Z hX Nseq hN
  have hmeasA : ∀ (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) n,
      Measurable fun ω => normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ hρ y hy (X n ω)) :=
    fun y hy n => measurable_normA_comp β b ρ r p p T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ p
      (Nseq n) _ ((measurable_withY ρ hρ y hy).comp (hXm n))
  have hmeasC : ∀ (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y),
      Measurable fun ω => coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ y hy (Z ω)) :=
    fun y hy => (measurable_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ p hp0).comp
      ((measurable_withY ρ hρ y hy).comp hZm)
  have hpos : ∀ᵐ ω ∂μ', 0 < coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ y₁ hy₁ (Z ω)) :=
    Filter.Eventually.of_forall fun ω =>
      coeffA_leading_pos β ρ h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂ _ (by rw [toY_withY]; exact hy₁0)
  have hdiv := tendstoInDistribution_div_of_pos _ _ _ _ (hmeasA yφ hyφ) (hmeasA y₁ hy₁)
    (hmeasC yφ hyφ) (hmeasC y₁ hy₁) hpair hpos
  refine hdiv.congr (fun n => Filter.Eventually.of_forall fun ω => rfl)
    (Filter.Eventually.of_forall fun ω => ?_)
  exact coeffA_withY_div β ρ hρ h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂ yφ y₁ hyφ hy₁ hy₁0 (Z ω)

/-- For `N > 1` the quotient of normalised chart integrals is the quotient of chart integrals. -/
theorem normA_div_eq_chartZ_div (β b p ρ T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (N : ℝ) (hN : 1 < N)
    (a a' : CoeffPair) :
    normA β b ρ p p T h₁ h₂ k₁ k₂ p N a / normA β b ρ p p T h₁ h₂ k₁ k₂ p N a'
      = chartZ β b ρ h₁ h₂ k₁ k₂ N a / chartZ β b ρ h₁ h₂ k₁ k₂ N a' := by
  unfold normA
  rw [lowerPart_leading_eq_zero h₁ h₂ k₁ k₂ hk₁ hk₂ p T hp₁ hp₂,
    lowerPart_leading_eq_zero h₁ h₂ k₁ k₂ hk₁ hk₂ p T hp₁ hp₂, sub_zero, sub_zero]
  have hs : N ^ (-p) * Real.log N ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' (Real.log_pos hN).ne'
  exact div_div_div_cancel_right₀ hs _ _

/-- **The chart posterior limit**: `Z_{N_n}[φ] / Z_{N_n}[1] ⇒ y_{φ,00} / y_{1,00}`. -/
theorem tendstoInDistribution_chart_posterior (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (yφ y₁ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hy₁0 : 0 < y₁ (0, 0))
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (Z : Ω' → CoeffPair)
    (hZm : Measurable Z) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun n ω =>
        chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ (lt_trans hb hbρ) yφ hyφ (X n ω))
          / chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ (lt_trans hb hbρ) y₁ hy₁ (X n ω))) l
      (fun _ => yφ (0, 0) / y₁ (0, 0)) (fun _ => μ) μ' := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hdiv := tendstoInDistribution_normA_div β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂
    hp₁ hp₂ hpT yφ y₁ hyφ hy₁ hy₁0 X hXm Z hZm hX Nseq hN
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hdiv ?_ fun n =>
    ((measurable_chartZ_comp β b ρ h₁ h₂ k₁ k₂ hb hbρ (Nseq n) _
        ((measurable_withY ρ hρ yφ hyφ).comp (hXm n))).div
      (measurable_chartZ_comp β b ρ h₁ h₂ k₁ k₂ hb hbρ (Nseq n) _
        ((measurable_withY ρ hρ y₁ hy₁).comp (hXm n)))).aemeasurable
  have h := tendstoInMeasure_of_eventually_abs_le (l := l) μ
    (fun n ω =>
      chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ hρ yφ hyφ (X n ω))
          / chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ hρ y₁ hy₁ (X n ω))
        - normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ hρ yφ hyφ (X n ω))
          / normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ hρ y₁ hy₁ (X n ω)))
    (fun _ => (0 : ℝ)) tendsto_const_nhds ?_
  · exact h
  · filter_upwards [hN.eventually_gt_atTop 1] with n hn ω
    rw [normA_div_eq_chartZ_div β b p ρ T h₁ h₂ k₁ k₂ hk₁ hk₂ hp₁ hp₂ (Nseq n) hn, sub_self,
      abs_zero]

end Laplace.Grammar
