/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StochasticLogRegime

/-!
# Headline statements, part X: the stochastic `1/log N` regime

Paper-facing wrapper for unit 194. At chart level (`d = 2`, equal starting exponents `p`), for a
deterministic corner-vanishing observable amplitude `y_φ` (`y_{φ,00} = 0`), a deterministic
normaliser amplitude `y_1` with positive corner value (`y_{1,00} > 0`; positivity throughout the
chart is not assumed), and a common random phase whose Taylor data
`X_n` converge in distribution to `Z`,

  `log N_n · Z_{N_n}[φ](X_n) / Z_{N_n}[1](X_n) ⇒ B^φ_p(Z) / A^1_p(Z)`

(`headline_posterior_log_decay_stochastic`), a scaled convergence in distribution (not a pathwise
asymptotic equivalence): the empirical posterior expectation of a corner-vanishing observable is
of order `1/log N` with the **random** coefficient
`B^φ_p(Z)/A^1_p(Z)`, the stochastic form of `headline_posterior_log_decay`. The denominator
coefficient is strictly positive; when `B^φ_p(Z) = 0` the limit is `0` and no faster rate is
claimed. NOT claimed: random amplitudes, rates beyond `1/log N`, or unequal starting exponents.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real

namespace Laplace.Grammar

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- **Stochastic `1/log N` decay** of the chart posterior expectation of a corner-vanishing
observable: `log N · Z[φ]/Z[1] ⇒ B^φ_p(Z)/A^1_p(Z)`. -/
theorem headline_posterior_log_decay_stochastic (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (yφ y₁ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hyφ0 : yφ (0, 0) = 0)
    (hy₁0 : 0 < y₁ (0, 0)) (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n))
    (Z : Ω' → CoeffPair) (hZm : Measurable Z) (hX : TendstoInDistribution X l Z (fun _ => μ) μ')
    (Nseq : ι → ℝ) (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun n ω =>
        twoDAmp β b (Nseq n) h₁ h₂ k₁ k₂
            (anaAmp (ampCoeff β (toX ρ (withY ρ (lt_trans hb hbρ) yφ hyφ (X n ω)))
              (toY ρ (withY ρ (lt_trans hb hbρ) yφ hyφ (X n ω)))) b)
          / twoDAmp β b (Nseq n) h₁ h₂ k₁ k₂
            (anaAmp (ampCoeff β (toX ρ (withY ρ (lt_trans hb hbρ) y₁ hy₁ (X n ω)))
              (toY ρ (withY ρ (lt_trans hb hbρ) y₁ hy₁ (X n ω)))) b)
          * Real.log (Nseq n)) l
      (fun ω => coeffB β b ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) yφ hyφ (Z ω))
        / coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) y₁ hy₁ (Z ω))) (fun _ => μ) μ' :=
  tendstoInDistribution_log_posterior β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ hp₁ hp₂
    hpT yφ y₁ hyφ hy₁ hyφ0 hy₁0 X hXm Z hZm hX Nseq hN

end Laplace.Grammar
