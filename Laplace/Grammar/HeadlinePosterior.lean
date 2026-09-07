/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ChartPosteriorLimit

/-!
# Headline statements, part II: the chart posterior ratio (§4.3, cor:empirical_expectation)

Paper-facing wrappers for units 156–159, complementing `Laplace/Grammar/Headline.lean` (which the
probabilistic files import, hence this separate file). Same scope as there: `d = 2`, one chart,
Taylor data in the weighted coefficient space; in addition the amplitudes are DETERMINISTIC arrays
(the paper's `η = φ·prior·Jacobian`) and only the phase is random, with equal starting exponents.

NOT claimed: the multi-chart posterior; the full division expansion (only the leading ratio);
the functional CLT supplying the convergence of the phase data; finite-sample positivity of the
normaliser (Lean's totalised division makes it unnecessary for the limit statement).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology

namespace Laplace.Grammar

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- **Stability of convergence in distribution under small-probability modifications**
(generic tool). -/
theorem headline_approx_in_distribution {E : Type*} [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableEq E] [Nonempty E] (X : ι → Ω → E) (Z : Ω' → E)
    (hX : ∀ n, Measurable (X n)) (hZ : Measurable Z)
    (happrox : ∀ η : ℝ, 0 < η → ∃ (Y : ι → Ω → E) (W : Ω' → E),
      (∀ n, Measurable (Y n)) ∧ Measurable W ∧
      TendstoInDistribution Y l W (fun _ => μ) μ' ∧
      (∀ᶠ n in l, μ {ω | X n ω ≠ Y n ω} ≤ ENNReal.ofReal η) ∧
      μ' {ω | Z ω ≠ W ω} ≤ ENNReal.ofReal η) :
    TendstoInDistribution X l Z (fun _ => μ) μ' :=
  tendstoInDistribution_of_approx X Z hX hZ happrox

/-- **Quotients with a.s. positive limiting denominator converge in distribution**
(the division lemma of cor:empirical_expectation, probabilistic form). -/
theorem headline_quotient_in_distribution (U V : ι → Ω → ℝ) (U₀ V₀ : Ω' → ℝ)
    (hU : ∀ n, Measurable (U n)) (hV : ∀ n, Measurable (V n)) (hU₀ : Measurable U₀)
    (hV₀ : Measurable V₀)
    (hUV : TendstoInDistribution (fun n ω => (U n ω, V n ω)) l (fun ω => (U₀ ω, V₀ ω))
      (fun _ => μ) μ')
    (hpos : ∀ᵐ ω ∂μ', 0 < V₀ ω) :
    TendstoInDistribution (fun n ω => U n ω / V n ω) l (fun ω => U₀ ω / V₀ ω) (fun _ => μ) μ' :=
  tendstoInDistribution_div_of_pos U V U₀ V₀ hU hV hU₀ hV₀ hUV hpos

/-- **Joint convergence of numerator and denominator**: for deterministic amplitudes `y_φ, y_1`
and a common random phase `X n ⇒ Z`, `(Z_{N_n}[φ]/s_n, Z_{N_n}[1]/s_n) ⇒ (A_p(Z; y_φ), A_p(Z; y_1))`
with `s_n = N_n^{−p} log N_n` (equal starting exponents `p`). -/
theorem headline_joint_normalised_pair (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (yφ y₁ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun n ω =>
        (normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) yφ hyφ (X n ω)),
          normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) y₁ hy₁ (X n ω)))) l
      (fun ω => (coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) yφ hyφ (Z ω)),
        coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) y₁ hy₁ (Z ω)))) (fun _ => μ) μ' :=
  tendstoInDistribution_normA_pair β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ hp₁ hp₂ hpT
    yφ y₁ hyφ hy₁ X hXm Z hX Nseq hN

/-- **The chart posterior limit** (cor:empirical_expectation, leading term, chart level): for a
common random phase `X n ⇒ Z` and deterministic amplitudes with `y_{1,00} > 0`,
`Z_{N_n}[φ] / Z_{N_n}[1] ⇒ y_{φ,00} / y_{1,00}`. The random fluctuation factor cancels: the leading
posterior expectation converges to the deterministic corner-value ratio (`= φ(0,0)` when
`η_φ = φ η_1`). -/
theorem headline_chart_posterior_limit (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (yφ y₁ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hy₁0 : 0 < y₁ (0, 0))
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (Z : Ω' → CoeffPair)
    (hZm : Measurable Z) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun n ω =>
        chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ (lt_trans hb hbρ) yφ hyφ (X n ω))
          / chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ (lt_trans hb hbρ) y₁ hy₁ (X n ω))) l
      (fun _ => yφ (0, 0) / y₁ (0, 0)) (fun _ => μ) μ' :=
  tendstoInDistribution_chart_posterior β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ hp₁ hp₂
    hpT yφ y₁ hyφ hy₁ hy₁0 X hXm Z hZm hX Nseq hN

end Laplace.Grammar
