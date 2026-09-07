/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LeadingTermExtraction

/-!
# The deterministic chart posterior ratio, including the corner-vanishing regime

For a fixed phase `x` and amplitudes `y_φ`, `y_1` with `y_{1,00} > 0`, equal starting exponents `p`:

* if `y_{φ,00} ≠ 0`, then `Z[φ](N)/Z[1](N) → y_{φ,00}/y_{1,00}` (`chart_posterior_tendsto_const`);
* if `y_{φ,00} = 0` but the constant coefficient `B^φ_p ≠ 0`, then
  `(Z[φ](N)/Z[1](N)) · log N → B^φ_p / A^1_p` (`chart_posterior_tendsto_log`): the posterior
  expectation of an observable vanishing at the corner decays like `1/log N`, not like a power of
  `N` (Astra #14's correction to the naive vanishing-order heuristic).

The log coefficient vanishes exactly when the amplitude vanishes at the corner
(`leading_log_coeff_eq_zero_iff`). Zero `sorry`/`axiom`.
-/

open Asymptotics Filter Real Topology

namespace Laplace.Grammar

/-- `A_p = 0 ⇔ y₀₀ = 0` (equal starting exponents). -/
theorem leading_log_coeff_eq_zero_iff (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (x y : ℕ × ℕ → ℝ) :
    canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p = 0 ↔ y (0, 0) = 0 := by
  rw [leading_log_coeff β h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂ x y]
  have hk : (0 : ℝ) < (k₁ : ℝ) * k₂ := by exact_mod_cast Nat.mul_pos hk₁ hk₂
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hp : 0 < p := by rw [← hp₁]; positivity
  have hM := logMoment_exp_pos β p (x (0, 0)) hβ hp
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h1 | h1
    · exact (div_eq_zero_iff.1 h1).resolve_right hk.ne'
    · exact absurd h1 hM.ne'
  · intro h; rw [h]; simp

/-- **Constant limit** when the observable does not vanish at the corner. -/
theorem chart_posterior_tendsto_const (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x yφ y₁ : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hy₁0 : 0 < y₁ (0, 0))
    (hyφ0 : yφ (0, 0) ≠ 0) :
    Tendsto (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x yφ) b)
        / twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y₁) b)) atTop
      (𝓝 (yφ (0, 0) / y₁ (0, 0))) := by
  have hAφ : canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x yφ (i, j) s) p ≠ 0 := by
    rw [Ne, leading_log_coeff_eq_zero_iff β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂]; exact hyφ0
  have hA₁ : canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y₁ (i, j) s) p ≠ 0 :=
    (leading_log_coeff_pos β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂ x y₁ hy₁0).ne'
  have hEφ := chart_isEquivalent_log β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x yφ hx hyφ hAφ
  have hE₁ := chart_isEquivalent_log β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x y₁ hx hy₁ hA₁
  have h := tendsto_quotient_of_eq _ _ _ _ p 1 hEφ hE₁
  -- the ratio of leading coefficients is the corner-value ratio
  have hk : (0 : ℝ) < (k₁ : ℝ) * k₂ := by exact_mod_cast Nat.mul_pos hk₁ hk₂
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hp : 0 < p := by rw [← hp₁]; positivity
  rw [leading_log_coeff β h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂ x yφ,
    leading_log_coeff β h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂ x y₁] at h
  set M := logMoment β p 0 (fun s => Real.exp (β * s * x (0, 0))) with hMdef
  have hM : 0 < M := logMoment_exp_pos β p (x (0, 0)) hβ hp
  have hratio : yφ (0, 0) / ((k₁ : ℝ) * k₂) * M / (y₁ (0, 0) / ((k₁ : ℝ) * k₂) * M)
      = yφ (0, 0) / y₁ (0, 0) := by
    field_simp
  rw [hratio] at h
  exact h

/-- **`1/log N` decay** when the observable vanishes at the corner but `B^φ_p ≠ 0`. -/
theorem chart_posterior_tendsto_log (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x yφ y₁ : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hy₁0 : 0 < y₁ (0, 0))
    (hyφ0 : yφ (0, 0) = 0)
    (hB : canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x yφ) b) (anaFaceV (ampCoeff β x yφ) b)
      (fun i j s => ampCoeff β x yφ (i, j) s) p ≠ 0) :
    Tendsto (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x yφ) b)
        / twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y₁) b) * Real.log N) atTop
      (𝓝 (canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x yφ) b) (anaFaceV (ampCoeff β x yφ) b)
          (fun i j s => ampCoeff β x yφ (i, j) s) p
        / canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y₁ (i, j) s) p)) := by
  have hAφ : canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x yφ (i, j) s) p = 0 :=
    (leading_log_coeff_eq_zero_iff β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂ x yφ).2 hyφ0
  have hA₁ : canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y₁ (i, j) s) p ≠ 0 :=
    (leading_log_coeff_pos β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂ x y₁ hy₁0).ne'
  have hEφ := chart_isEquivalent_const β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x yφ hx hyφ
    hAφ hB
  have hE₁ := chart_isEquivalent_log β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x y₁ hx hy₁ hA₁
  exact tendsto_quotient_mul_log_of_eq _ _ _ _ p 0 hEφ hE₁

end Laplace.Grammar
