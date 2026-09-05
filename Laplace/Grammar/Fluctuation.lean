/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The fluctuation function (grammar paper §4)

Watanabe's *fluctuation function* (greybook, Definition 5.8), the building block
of the `Z_n[φ]` asymptotic expansion in *Expectations and the exceptional
divisor* (§4, `eq:fluctuation`):

  `S_λ(a) = ∫₀^∞ t^{λ-1} e^{-β t + β a √t} dt`,   `β, λ > 0`.

This module opens the §4 formalisation with the definition, its integrability
for every `a ∈ ℝ` (AM–GM domination `a√t ≤ t/2 + a²/2` against a Gamma
integrand), and the base value `S_λ(0) = β^{-λ} Γ(λ)`.

`lam` denotes the RLCT `λ` (`λ` is reserved syntax in Lean).
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- The **fluctuation function** `S_λ(a) = ∫₀^∞ t^{λ-1} e^{-β t + β a √t} dt`
(grammar §4 `eq:fluctuation`; Watanabe, Definition 5.8). -/
noncomputable def fluctuation (β lam a : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)

/-- The fluctuation integrand is integrable on `(0, ∞)` for every `a` (with
`β, λ > 0`): the AM–GM bound `a√t ≤ t/2 + a²/2` gives
`e^{-βt + βa√t} ≤ e^{βa²/2} · e^{-(β/2)t}`, and the majorant
`t^{λ-1} e^{-(β/2)t}` is Gamma-integrable. -/
theorem fluctuation_integrableOn (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    IntegrableOn
      (fun t => t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      (Set.Ioi (0 : ℝ)) := by
  -- Majorant: `exp(βa²/2) · (t^(λ-1) · exp(-(β/2)·t))`, Gamma-integrable at `p = 1`.
  have hmaj : IntegrableOn
      (fun t : ℝ => Real.exp (β * a ^ 2 / 2) *
        (t ^ (lam - 1) * Real.exp (-(β / 2) * t ^ (1 : ℝ)))) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos (by linarith)).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · -- `AEStronglyMeasurable` of the integrand: continuous on `(0, ∞)`.
    apply ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (Set.mem_Ioi.mp ht)))
    · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  · -- Pointwise domination via AM–GM `a√t ≤ t/2 + a²/2`.
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht0 : (0 : ℝ) < t := Set.mem_Ioi.mp ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
      abs_of_pos (Real.exp_pos _), Real.rpow_one,
      show Real.exp (β * a ^ 2 / 2) * (t ^ (lam - 1) * Real.exp (-(β / 2) * t))
        = t ^ (lam - 1) * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t)) by ring,
      ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht0.le _)
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (Real.sqrt t - a), Real.sq_sqrt ht0.le, hβ]

/-- Base value `S_λ(0) = β^{-λ} Γ(λ)` (grammar §4, remark after `eq:fluctuation`). -/
theorem fluctuation_zero (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    fluctuation β lam 0 = β ^ (-lam) * Real.Gamma lam := by
  have h : fluctuation β lam 0
      = ∫ t in Set.Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-β * t ^ (1 : ℝ)) := by
    unfold fluctuation
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [mul_zero, zero_mul, add_zero, Real.rpow_one]
  rw [h, integral_rpow_mul_exp_neg_mul_rpow one_pos (by linarith) hβ,
    show -(lam - 1 + 1) / 1 = -lam by ring, show (lam - 1 + 1) / 1 = lam by ring]
  simp

end Laplace.Grammar
