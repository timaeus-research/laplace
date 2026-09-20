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

/-- **Empirical free energy along a schedule.** With `t_n → ∞` and `t_n δ_n ≤ B`, the empirical
free energy `-log Z_{K_n}(t_n)` equals `λ log t_n - k log log t_n` up to a bounded error, where
`(λ, k+1)` are the population sublevel data. -/
theorem eventually_abs_neg_log_boltzmannMass_sub_le_of_uniform_close {K : ℕ → X → ℝ}
    {L : X → ℝ} (hK : ∀ n, Measurable (K n)) (hL : Measurable L)
    (hK0 : ∀ n x, 0 ≤ K n x) (hL0 : ∀ x, 0 ≤ L x) {δ t : ℕ → ℝ}
    (hclose : ∀ n x, |K n x - L x| ≤ δ n) (hδ : ∀ n, 0 ≤ δ n) {B : ℝ} (htδ : ∀ n, t n * δ n ≤ B)
    (ht : Tendsto t atTop atTop) {lam ε₀ c₁ c₂ : ℝ} (k : ℕ)
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      c₁ * ε ^ lam * (Real.log ε⁻¹) ^ k ≤ sublevelMass μ L ε)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      sublevelMass μ L ε ≤ c₂ * ε ^ lam * (Real.log ε⁻¹) ^ k) :
    ∃ D : ℝ, ∀ᶠ n in atTop,
      |(-Real.log (boltzmannMass μ (K n) (t n))) -
        (lam * Real.log (t n) - k * Real.log (Real.log (t n)))| ≤ D := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ :=
    boltzmannMass_log_transfer μ L hL hL0 k hlam hε₀ hε₀1 hc₁ hc₂ hlower hupper
  refine ⟨max |B + Real.log C₂| |B - Real.log C₁|, ?_⟩
  have hev : ∀ᶠ n in atTop, (C₁ * t n ^ (-lam) * (Real.log (t n)) ^ k ≤ boltzmannMass μ L (t n) ∧
      boltzmannMass μ L (t n) ≤ C₂ * t n ^ (-lam) * (Real.log (t n)) ^ k) ∧ Real.exp 1 < t n :=
    (ht.eventually h).and (ht.eventually (eventually_gt_atTop (Real.exp 1)))
  filter_upwards [hev] with n hn
  obtain ⟨⟨hlo, hhi⟩, hte⟩ := hn
  have htpos : 0 < t n := lt_trans (Real.exp_pos 1) hte
  have hlog1 : 1 < Real.log (t n) := by
    have := Real.log_lt_log (Real.exp_pos 1) hte
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log (t n) := zero_lt_one.trans hlog1
  set S : ℝ := t n ^ (-lam) * (Real.log (t n)) ^ k with hS_def
  have hSpos : 0 < S := mul_pos (Real.rpow_pos_of_pos htpos _) (pow_pos hlogpos _)
  have hlogS : Real.log S = -lam * Real.log (t n) + k * Real.log (Real.log (t n)) := by
    rw [hS_def, Real.log_mul (Real.rpow_pos_of_pos htpos _).ne' (pow_pos hlogpos _).ne',
      Real.log_rpow htpos, Real.log_pow]
  have htδ0 : 0 ≤ t n * δ n := mul_nonneg htpos.le (hδ n)
  obtain ⟨hs1, hs2⟩ := boltzmannMass_sandwich_of_uniform_close μ (hK n) hL (hK0 n) hL0 (hclose n)
    htpos.le
  -- two-sided bounds on `Z_K` by `e^{±B} C S`
  have hZlo : Real.exp (-B) * (C₁ * S) ≤ boltzmannMass μ (K n) (t n) := by
    calc Real.exp (-B) * (C₁ * S) ≤ Real.exp (-(t n * δ n)) * (C₁ * S) := by
          gcongr
          linarith [htδ n]
      _ ≤ Real.exp (-(t n * δ n)) * boltzmannMass μ L (t n) := by
          gcongr
          simpa [hS_def, mul_assoc] using hlo
      _ ≤ boltzmannMass μ (K n) (t n) := hs1
  have hZhi : boltzmannMass μ (K n) (t n) ≤ Real.exp B * (C₂ * S) := by
    calc boltzmannMass μ (K n) (t n) ≤ Real.exp (t n * δ n) * boltzmannMass μ L (t n) := hs2
      _ ≤ Real.exp (t n * δ n) * (C₂ * S) := by
          gcongr
          simpa [hS_def, mul_assoc] using hhi
      _ ≤ Real.exp B * (C₂ * S) := by
          gcongr
          exact htδ n
  have hZpos : 0 < boltzmannMass μ (K n) (t n) :=
    lt_of_lt_of_le (by positivity) hZlo
  -- take logarithms
  have hlo' : -B + (Real.log C₁ + Real.log S) ≤ Real.log (boltzmannMass μ (K n) (t n)) := by
    have := Real.log_le_log (by positivity) hZlo
    rwa [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
      Real.log_mul hC₁.ne' hSpos.ne'] at this
  have hhi' : Real.log (boltzmannMass μ (K n) (t n)) ≤ B + (Real.log C₂ + Real.log S) := by
    have := Real.log_le_log hZpos hZhi
    rwa [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
      Real.log_mul hC₂.ne' hSpos.ne'] at this
  rw [hlogS] at hlo' hhi'
  rw [abs_le]
  constructor
  · have : -(max |B + Real.log C₂| |B - Real.log C₁|) ≤ -(B + Real.log C₂) := by
      have := le_abs_self (B + Real.log C₂)
      have := le_max_left |B + Real.log C₂| |B - Real.log C₁|
      linarith
    linarith
  · have : B - Real.log C₁ ≤ max |B + Real.log C₂| |B - Real.log C₁| :=
      (le_abs_self _).trans (le_max_right _ _)
    linarith

end Laplace
