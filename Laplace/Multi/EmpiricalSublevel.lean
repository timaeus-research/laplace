/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AbelianTransfer

/-!
# Empirical sublevel volumes carry the population exponent above the fluctuation scale

If `|K - L| ≤ δ` then `{L ≤ ε - δ} ⊆ {K ≤ ε} ⊆ {L ≤ ε + δ}`, so the sublevel masses are
sandwiched (`sublevelMass_sandwich_of_uniform_close`). With the population bounds
`c₁ ε^λ ≤ μ{L ≤ ε} ≤ c₂ ε^λ` on `(0, ε₀]`, the empirical sublevel mass satisfies

  `c₁ 2^{-λ} ε^λ ≤ μ{K ≤ ε} ≤ c₂ 2^{λ} ε^λ`   for `2δ ≤ ε ≤ ε₀ - δ`

(`sublevelMass_power_bounds_of_uniform_close`): the real log canonical threshold of the
population loss is legible in the empirical sublevel volumes exactly on the scales `ε ≫ δ_n`,
the volume-side counterpart of the partition-function sandwich of `EmpiricalTransfer`.
-/

open MeasureTheory Set

namespace Laplace

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- **Sublevel sandwich under uniform closeness.** -/
theorem sublevelMass_sandwich_of_uniform_close {K L : X → ℝ} {δ : ℝ}
    (hclose : ∀ x, |K x - L x| ≤ δ) (ε : ℝ) :
    sublevelMass μ L (ε - δ) ≤ sublevelMass μ K ε ∧
      sublevelMass μ K ε ≤ sublevelMass μ L (ε + δ) := by
  constructor
  · refine measureReal_mono fun x hx ↦ ?_
    have h := abs_le.mp (hclose x)
    change L x ≤ ε - δ at hx
    change K x ≤ ε
    linarith
  · refine measureReal_mono fun x hx ↦ ?_
    have h := abs_le.mp (hclose x)
    change K x ≤ ε at hx
    change L x ≤ ε + δ
    linarith

/-- **The population exponent on empirical sublevel volumes.** Two-sided power bounds for
`μ{L ≤ ε}` on `(0, ε₀]` transfer to `μ{K ≤ ε}` on `2δ ≤ ε ≤ ε₀ - δ` with constants
`c₁ 2^{-λ}` and `c₂ 2^{λ}`. -/
theorem sublevelMass_power_bounds_of_uniform_close {K L : X → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ x, |K x - L x| ≤ δ) {lam ε₀ c₁ c₂ : ℝ} (hlam : 0 ≤ lam) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂)
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → c₁ * ε ^ lam ≤ sublevelMass μ L ε)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → sublevelMass μ L ε ≤ c₂ * ε ^ lam)
    {ε : ℝ} (hε : 0 < ε) (hεδ : 2 * δ ≤ ε) (hε₀ : ε ≤ ε₀ - δ) :
    c₁ * (2 : ℝ) ^ (-lam) * ε ^ lam ≤ sublevelMass μ K ε ∧
      sublevelMass μ K ε ≤ c₂ * (2 : ℝ) ^ lam * ε ^ lam := by
  obtain ⟨h1, h2⟩ := sublevelMass_sandwich_of_uniform_close μ hclose ε
  have hεm : 0 < ε - δ := by linarith
  have hεp : 0 < ε + δ := by linarith
  constructor
  · -- `(ε - δ) ≥ ε / 2`
    have hhalf : ε / 2 ≤ ε - δ := by linarith
    have hpow : (ε / 2) ^ lam ≤ (ε - δ) ^ lam := Real.rpow_le_rpow (by positivity) hhalf hlam
    have heq : (ε / 2) ^ lam = (2 : ℝ) ^ (-lam) * ε ^ lam := by
      rw [div_eq_mul_inv, Real.mul_rpow hε.le (by positivity), Real.inv_rpow (by norm_num),
        ← Real.rpow_neg (by norm_num), mul_comm]
    calc c₁ * (2 : ℝ) ^ (-lam) * ε ^ lam = c₁ * (ε / 2) ^ lam := by rw [heq]; ring
      _ ≤ c₁ * (ε - δ) ^ lam := mul_le_mul_of_nonneg_left hpow hc₁
      _ ≤ sublevelMass μ L (ε - δ) := hlower _ hεm (by linarith)
      _ ≤ sublevelMass μ K ε := h1
  · -- `(ε + δ) ≤ 2 ε`
    have hdouble : ε + δ ≤ 2 * ε := by linarith
    have hpow : (ε + δ) ^ lam ≤ (2 * ε) ^ lam := Real.rpow_le_rpow hεp.le hdouble hlam
    have heq : (2 * ε) ^ lam = (2 : ℝ) ^ lam * ε ^ lam := Real.mul_rpow (by norm_num) hε.le
    calc sublevelMass μ K ε ≤ sublevelMass μ L (ε + δ) := h2
      _ ≤ c₂ * (ε + δ) ^ lam := hupper _ hεp (by linarith)
      _ ≤ c₂ * (2 * ε) ^ lam := mul_le_mul_of_nonneg_left hpow hc₂
      _ = c₂ * (2 : ℝ) ^ lam * ε ^ lam := by rw [heq]; ring

end Laplace
