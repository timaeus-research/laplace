/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.NormBoundedInProbability

/-!
# Positivity of the leading log coefficient (grammar §4.2–§4.3, Astra #12 rank 3)

For equal starting exponents the leading log coefficient is
`A_p = y₀₀/(k₁k₂) · ∫₀^∞ s^{p−1} e^{−βs²} e^{βs x₀₀} ds` (unit 124). The Gaussian moment is
strictly positive (`logMoment_exp_pos`) and monotone in `x₀₀` (`logMoment_exp_mono`), so
`y₀₀ > 0 ⇒ A_p > 0` (`leading_log_coeff_pos`), with the quantitative lower bound
`A_p ≥ c/(k₁k₂) · ∫₀^∞ s^{p−1} e^{−βs²} e^{−βsM} ds` when `y₀₀ ≥ c ≥ 0` and `‖x‖_ρ ≤ M`
(`leading_log_coeff_ge`). Restated on the coefficient-pair space (`coeffA_leading_pos`,
`coeffA_leading_ge`), this is the nonvanishing of the denominator in the posterior ratio
`Z_n[φ]/Z_n` (cor:empirical_expectation): the prior/Jacobian amplitude has `y₀₀ > 0` at the corner.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- The Gaussian moment integrand is integrable. -/
theorem gaussMoment_exp_integrableOn (β α x : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IntegrableOn (fun s => s ^ (α - 1) * Real.log s ^ 0
      * (Real.exp (-β * s ^ 2) * Real.exp (β * s * x))) (Ioi 0) := by
  have h := gaussMoment_integrableOn β α x hβ hα 0 0
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp

/-- **Strict positivity** of `∫₀^∞ s^{α−1} e^{−βs²} e^{βsx} ds`. -/
theorem logMoment_exp_pos (β α x : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    0 < logMoment β α 0 (fun s => Real.exp (β * s * x)) := by
  unfold logMoment
  have hint := gaussMoment_exp_integrableOn β α x hβ hα
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi 0)] fun s => s ^ (α - 1) * Real.log s ^ 0
      * (Real.exp (-β * s ^ 2) * Real.exp (β * s * x)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    have : 0 < s ^ (α - 1) := Real.rpow_pos_of_pos hs _
    change (0 : ℝ) ≤ s ^ (α - 1) * Real.log s ^ 0 * (Real.exp (-β * s ^ 2) * Real.exp (β * s * x))
    positivity
  refine (setIntegral_pos_iff_support_of_nonneg_ae hnn hint).2 ?_
  have hsupp : Function.support (fun s : ℝ => s ^ (α - 1) * Real.log s ^ 0
      * (Real.exp (-β * s ^ 2) * Real.exp (β * s * x))) ∩ Ioi 0 = Ioi 0 := by
    ext s
    simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro hs
      refine ⟨?_, hs⟩
      have : 0 < s ^ (α - 1) := Real.rpow_pos_of_pos hs _
      positivity
  rw [hsupp, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- Monotonicity of the Gaussian moment in the linear coefficient. -/
theorem logMoment_exp_mono (β α x x' : ℝ) (hβ : 0 < β) (hα : 0 < α) (hxx' : x ≤ x') :
    logMoment β α 0 (fun s => Real.exp (β * s * x))
      ≤ logMoment β α 0 (fun s => Real.exp (β * s * x')) := by
  unfold logMoment
  refine setIntegral_mono_on (gaussMoment_exp_integrableOn β α x hβ hα)
    (gaussMoment_exp_integrableOn β α x' hβ hα) measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  have h1 : 0 ≤ s ^ (α - 1) * Real.log s ^ 0 := by positivity
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) h1
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxx' (by positivity))

/-- **Positivity of the leading log coefficient** for `y₀₀ > 0` (equal starting exponents). -/
theorem leading_log_coeff_pos (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x y : ℕ × ℕ → ℝ)
    (hy : 0 < y (0, 0)) :
    0 < canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p := by
  rw [leading_log_coeff β h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂ x y]
  have hk : (0 : ℝ) < (k₁ : ℝ) * k₂ := by exact_mod_cast Nat.mul_pos hk₁ hk₂
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hp : 0 < p := by rw [← hp₁]; positivity
  exact mul_pos (div_pos hy hk) (logMoment_exp_pos β p (x (0, 0)) hβ hp)

/-- **Quantitative lower bound** on the ball `‖x‖_ρ ≤ M` with `y₀₀ ≥ c ≥ 0`. -/
theorem leading_log_coeff_ge (β ρ M c : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hρ : 0 < ρ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hM : wnorm ρ x ≤ M) (hc : 0 ≤ c) (hy : c ≤ y (0, 0)) :
    c / ((k₁ : ℝ) * k₂) * logMoment β p 0 (fun s => Real.exp (β * s * (-M)))
      ≤ canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p := by
  rw [leading_log_coeff β h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂ x y]
  have hk : (0 : ℝ) < (k₁ : ℝ) * k₂ := by exact_mod_cast Nat.mul_pos hk₁ hk₂
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hp : 0 < p := by rw [← hp₁]; positivity
  have hx00 : -M ≤ x (0, 0) := by
    have := abs_apply_zero_le_wnorm ρ hρ.le x hx
    have := (abs_le.1 (this.trans hM)).1
    linarith
  exact mul_le_mul (div_le_div_of_nonneg_right hy hk.le)
    (logMoment_exp_mono β p (-M) (x (0, 0)) hβ hp hx00)
    (logMoment_exp_pos β p (-M) hβ hp).le (div_nonneg (hc.trans hy) hk.le)

/-- Positivity of the leading coefficient on the coefficient-pair space. -/
theorem coeffA_leading_pos (β ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (a : CoeffPair)
    (hy : 0 < toY ρ a (0, 0)) : 0 < coeffA β ρ h₁ h₂ k₁ k₂ p a :=
  leading_log_coeff_pos β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂ (toX ρ a) (toY ρ a) hy

/-- Quantitative lower bound on the coefficient-pair ball. -/
theorem coeffA_leading_ge (β ρ M c : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hρ : 0 < ρ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (a : CoeffPair) (ha : ‖a‖ ≤ M) (hc : 0 ≤ c)
    (hy : c ≤ toY ρ a (0, 0)) :
    c / ((k₁ : ℝ) * k₂) * logMoment β p 0 (fun s => Real.exp (β * s * (-M)))
      ≤ coeffA β ρ h₁ h₂ k₁ k₂ p a :=
  leading_log_coeff_ge β ρ M c h₁ h₂ k₁ k₂ hβ hρ hk₁ hk₂ p hp₁ hp₂ (toX ρ a) (toY ρ a)
    (wsummable_toX ρ hρ a) ((wnorm_toX_le_norm ρ hρ a).trans ha) hc hy

end Laplace.Grammar
