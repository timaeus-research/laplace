/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Fluctuation

/-!
# Gaussian domination of the fluctuation function (grammar §4)

The tail and convergence estimates of grammar §4.2 all rest on one elementary inequality: completing
the square in the fluctuation integrand,

  `e^{-β t + β a √t} ≤ e^{-(β/2) t + β a²/2}`,   since   `-β t + β a √t = -(β/2)t - (β/2)(√t - a)²
   + (β/2)a² ≤ -(β/2)t + (β/2)a²`

(the paper writes `e^{βξ₀²/2}` for the constant). Integrating against `t^{λ-1}` gives a closed-form
**Gaussian upper bound** on the fluctuation function,

  `S_λ(a) ≤ e^{β a²/2} (β/2)^{-λ} Γ(λ)`   for `λ > 0`,

the majorant that makes `S_λ` finite and drives the boundary-remainder estimate `eq:Deltaupper`.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- **Gaussian domination of the fluctuation integrand** (complete the square): for `t ≥ 0`,
`e^{-β t + β a √t} ≤ e^{-(β/2) t + β a²/2}`. The gap is `(β/2)(√t - a)² ≥ 0`. -/
theorem fluctuation_integrand_le (β a t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    Real.exp (-β * t + β * a * Real.sqrt t) ≤ Real.exp (-(β / 2) * t + β * a ^ 2 / 2) := by
  apply Real.exp_le_exp.2
  nlinarith [Real.sq_sqrt ht, mul_nonneg hβ.le (sq_nonneg (Real.sqrt t - a))]

/-- **Gaussian upper bound on the fluctuation function** (grammar §4): for `λ > 0`,
`S_λ(a) ≤ e^{β a²/2} (β/2)^{-λ} Γ(λ)`. Proved by dominating the integrand via
`fluctuation_integrand_le` and evaluating the resulting Gamma integral at `p = 1`. -/
theorem fluctuation_le_gaussian (β a lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    fluctuation β lam a ≤ Real.exp (β * a ^ 2 / 2) * (β / 2) ^ (-lam) * Real.Gamma lam := by
  have hmaj : IntegrableOn
      (fun t : ℝ => Real.exp (β * a ^ 2 / 2) *
        (t ^ (lam - 1) * Real.exp (-(β / 2) * t ^ (1 : ℝ)))) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos (by linarith)).const_mul _
  have hval : (∫ t in Set.Ioi (0 : ℝ), Real.exp (β * a ^ 2 / 2)
        * (t ^ (lam - 1) * Real.exp (-(β / 2) * t ^ (1 : ℝ))))
      = Real.exp (β * a ^ 2 / 2) * (β / 2) ^ (-lam) * Real.Gamma lam := by
    rw [integral_const_mul,
      integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by linarith) (by linarith)]
    simp only [div_one]
    rw [show lam - 1 + 1 = lam by ring]
    ring
  have hle : fluctuation β lam a
      ≤ ∫ t in Set.Ioi (0 : ℝ), Real.exp (β * a ^ 2 / 2)
          * (t ^ (lam - 1) * Real.exp (-(β / 2) * t ^ (1 : ℝ))) := by
    rw [fluctuation]
    refine setIntegral_mono_on (fluctuation_integrableOn β lam hβ hlam a) hmaj measurableSet_Ioi ?_
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htpow : (0 : ℝ) ≤ t ^ (lam - 1) := Real.rpow_nonneg ht0.le _
    rw [Real.rpow_one]
    calc t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
        ≤ t ^ (lam - 1) * Real.exp (-(β / 2) * t + β * a ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (fluctuation_integrand_le β a t hβ ht0.le) htpow
      _ = Real.exp (β * a ^ 2 / 2) * (t ^ (lam - 1) * Real.exp (-(β / 2) * t)) := by
          rw [Real.exp_add]; ring
  exact hle.trans_eq hval

end Laplace.Grammar
