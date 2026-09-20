/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AbelianTransferLog

/-!
# Empirical partition functions and the population exponent

If two nonnegative losses are uniformly `δ`-close then their Boltzmann masses
are sandwiched, `e^{-tδ} Z_L(t) ≤ Z_K(t) ≤ e^{tδ} Z_L(t)`
(`boltzmannMass_sandwich_of_uniform_close`), because the weights are
pointwise within the factor `e^{±tδ}`. Combined with the Abelian transfer for
the population loss this gives, for the empirical loss `K = K_n` with
`δ = δ_n = sup |K_n - L|`,

  `e^{-tδ_n} C₁ t^{-λ} (log t)^k ≤ Z_n(t) ≤ e^{tδ_n} C₂ t^{-λ} (log t)^k`

(`boltzmannMass_log_transfer_of_uniform_close`): the empirical free energy
`-log Z_n(t)` equals `λ log t - (m-1) log log t + O(1)` up to an error `t δ_n`,
so the population exponent and multiplicity are visible in the empirical
partition function exactly on the temperature range `t ≪ 1/δ_n`. This is the
partition-function counterpart of the moment stability of
`EmpiricalStability` and of the schedules of `EmpiricalSchedule`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Laplace

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Integrability of the Boltzmann weight of a nonnegative measurable loss. -/
theorem integrable_exp_neg_mul (K : X → ℝ) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {t : ℝ}
    (ht : 0 ≤ t) : Integrable (fun x ↦ Real.exp (-(t * K x))) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg ht (hK0 x))

/-- **Sandwich under uniform closeness**: `|K - L| ≤ δ` gives
`e^{-tδ} Z_L(t) ≤ Z_K(t) ≤ e^{tδ} Z_L(t)` for `t ≥ 0`. -/
theorem boltzmannMass_sandwich_of_uniform_close {K L : X → ℝ} (hK : Measurable K)
    (hL : Measurable L) (hK0 : ∀ x, 0 ≤ K x) (hL0 : ∀ x, 0 ≤ L x) {δ : ℝ}
    (hclose : ∀ x, |K x - L x| ≤ δ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(t * δ)) * boltzmannMass μ L t ≤ boltzmannMass μ K t ∧
      boltzmannMass μ K t ≤ Real.exp (t * δ) * boltzmannMass μ L t := by
  have hIK := integrable_exp_neg_mul μ K hK hK0 ht
  have hIL := integrable_exp_neg_mul μ L hL hL0 ht
  have hpt : ∀ x, Real.exp (-(t * δ)) * Real.exp (-(t * L x)) ≤ Real.exp (-(t * K x)) ∧
      Real.exp (-(t * K x)) ≤ Real.exp (t * δ) * Real.exp (-(t * L x)) := by
    intro x
    have h := abs_le.mp (hclose x)
    have h1 : t * (K x - L x) ≤ t * δ := mul_le_mul_of_nonneg_left h.2 ht
    have h2 : -(t * δ) ≤ t * (K x - L x) := by
      have := mul_le_mul_of_nonneg_left h.1 ht
      linarith
    constructor
    · rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
  unfold boltzmannMass
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hIL.const_mul _) hIK fun x ↦ (hpt x).1
  · rw [← integral_const_mul]
    exact integral_mono hIK (hIL.const_mul _) fun x ↦ (hpt x).2

/-- **Empirical partition function with the population exponent**: sublevel
log-power bounds for the population loss `L` and uniform closeness `|K - L| ≤ δ`
give `e^{-tδ} C₁ t^{-λ} (log t)^k ≤ Z_K(t) ≤ e^{tδ} C₂ t^{-λ} (log t)^k` for
large `t`. -/
theorem boltzmannMass_log_transfer_of_uniform_close {K L : X → ℝ} (hK : Measurable K)
    (hL : Measurable L) (hK0 : ∀ x, 0 ≤ K x) (hL0 : ∀ x, 0 ≤ L x) {δ : ℝ}
    (hclose : ∀ x, |K x - L x| ≤ δ) {lam ε₀ c₁ c₂ : ℝ} (k : ℕ)
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      c₁ * ε ^ lam * (Real.log ε⁻¹) ^ k ≤ sublevelMass μ L ε)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      sublevelMass μ L ε ≤ c₂ * ε ^ lam * (Real.log ε⁻¹) ^ k) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ t : ℝ in atTop,
      Real.exp (-(t * δ)) * (C₁ * t ^ (-lam) * (Real.log t) ^ k) ≤ boltzmannMass μ K t ∧
      boltzmannMass μ K t ≤ Real.exp (t * δ) * (C₂ * t ^ (-lam) * (Real.log t) ^ k) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ :=
    boltzmannMass_log_transfer μ L hL hL0 k hlam hε₀ hε₀1 hc₁ hc₂ hlower hupper
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  obtain ⟨hs1, hs2⟩ := boltzmannMass_sandwich_of_uniform_close μ hK hL hK0 hL0 hclose ht0
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left ht.1 (Real.exp_pos _).le) hs1
  · exact le_trans hs2 (mul_le_mul_of_nonneg_left ht.2 (Real.exp_pos _).le)

end Laplace
