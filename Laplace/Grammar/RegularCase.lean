/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ParabolicCylinder

/-!
# The regular case: `S_{1/2}` and the half-integer ladder (grammar §4 `ex:fluctuation_half`)

For regular models the RLCT is `λ = 1/2` on every chart, and the grammar paper's Example
`ex:fluctuation_half` records two facts about the base fluctuation function `S_{1/2}`:

* **Gaussian form.** Completing the square (`u = √t`, then `-βu²+βau = -β(u-a/2)²+βa²/4`),
  `S_{1/2}(a) = √(2/β) · e^{βa²/4} · ∫₀^∞ e^{-(u - a√(β/2))²/2} du`. The paper evaluates the
  remaining Gaussian tail as an error function; Mathlib has no `erf`, so we stop at the tail integral.
* **Half-integer ladder.** Every `S_{(n+1)/2}` is an `a`-derivative of `S_{1/2}`:
  `∂ₐⁿ S_{1/2}(a) = βⁿ S_{(n+1)/2}(a)`, so for regular models all fluctuation functions reduce to
  derivatives of the single function `S_{1/2}`.
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- **Half-integer ladder** (grammar §4 `ex:fluctuation_half`): the `n`-th `a`-derivative of `S_{1/2}`
is `βⁿ S_{(n+1)/2}`, so `S_{(n+1)/2}(a) = β^{-n} ∂ₐⁿ S_{1/2}(a)`. Iterates the derivative ladder
`S'_λ = β S_{λ+1/2}`. -/
theorem fluctuation_half_iteratedDeriv (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    iteratedDeriv n (fun a => fluctuation β (1 / 2) a)
      = fun a => β ^ n * fluctuation β (((n : ℝ) + 1) / 2) a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext a
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
    have hdiff : DifferentiableAt ℝ (fun a => fluctuation β (((n : ℝ) + 1) / 2) a) a :=
      (hasDerivAt_fluctuation β (((n : ℝ) + 1) / 2) hβ hpos a).differentiableAt
    rw [deriv_const_mul _ hdiff, deriv_fluctuation β (((n : ℝ) + 1) / 2) hβ hpos a,
      show ((n : ℝ) + 1) / 2 + 1 / 2 = ((↑(n + 1) : ℝ) + 1) / 2 by push_cast; ring, pow_succ]
    ring

/-- **Gaussian form of `S_{1/2}`** (grammar §4 `ex:fluctuation_half`): completing the square gives
`S_{1/2}(a) = √(2/β) · e^{βa²/4} · ∫₀^∞ e^{-(u - a√(β/2))²/2} du`. (The paper writes the tail integral
as `(√π/2)(1 + erf(a√β/2))`; Mathlib has no error function.) -/
theorem fluctuation_half_gaussian (β a : ℝ) (hβ : 0 < β) :
    fluctuation β (1 / 2) a
      = Real.sqrt (2 / β) * Real.exp (β * a ^ 2 / 4)
        * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(u - a * Real.sqrt (β / 2)) ^ 2 / 2) := by
  rw [fluctuation_eq_kernel β (1 / 2) a hβ]
  have hconst : (2 : ℝ) ^ (1 - 1 / 2 : ℝ) * β ^ (-(1 / 2) : ℝ) = Real.sqrt (2 / β) := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, Real.rpow_neg hβ.le,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_div' 2 hβ.le, div_eq_mul_inv]
  have hkernel : (∫ u in Set.Ioi (0 : ℝ),
        u ^ (2 * (1 / 2) - 1 : ℝ) * Real.exp (-u ^ 2 / 2 + a * Real.sqrt (β / 2) * u))
      = Real.exp (β * a ^ 2 / 4)
        * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(u - a * Real.sqrt (β / 2)) ^ 2 / 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    beta_reduce
    rw [show (2 * (1 / 2) - 1 : ℝ) = 0 by norm_num, Real.rpow_zero, one_mul, ← Real.exp_add]
    congr 1
    have hs : Real.sqrt (β / 2) ^ 2 = β / 2 := Real.sq_sqrt (by positivity)
    linear_combination (a ^ 2 / 2) * hs
  rw [hconst, hkernel, mul_assoc]

end Laplace.Grammar
