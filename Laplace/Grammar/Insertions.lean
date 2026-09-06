/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StandardIntegral

/-!
# Monomial insertions in the standard integral are `a`-derivatives (grammar §4.2)

Expanding `e^{β√n u^k (ξ(u)-ξ(0))}` in the standard integral produces, at order `p`, an insertion
`(√n u^k)^p` against the population kernel `e^{-βn u^{2k} + β√n u^k ξ(0)}`; the Taylor tree
(`thm:TaylorTree`) records the result through the `a`-derivatives `∂^p S_μ(ξ(0))` of the fluctuation
function. In one dimension the mechanism is exact:

  `∫₀^∞ u^h (√n u^k)^p e^{-βn u^{2k} + β√n u^k a} du
      = (2k)^{-1} n^{-(h+1)/(2k)} S_{(h+1)/(2k) + p/2}(a)
      = (2k)^{-1} n^{-(h+1)/(2k)} β^{-p} ∂_a^p S_{(h+1)/(2k)}(a)`.

The first form is `standardIntegral1D_eq_fluctuation` at `h + kp` (the insertion raises the order by
`p/2` and leaves the `n`-power `n^{-(h+1)/(2k)}` untouched); the second uses the general derivative
ladder `∂_a^p S_λ = β^p S_{λ+p/2}`, proved here for every `λ > 0`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- **Iterated derivative ladder** for every order `λ > 0`: `∂_a^p S_λ = β^p S_{λ+p/2}`
(generalising `fluctuation_half_iteratedDeriv`). -/
theorem iteratedDeriv_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (p : ℕ) :
    iteratedDeriv p (fun a => fluctuation β lam a)
      = fun a => β ^ p * fluctuation β (lam + (p : ℝ) / 2) a := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [iteratedDeriv_succ, ih]
    funext a
    have hpos : (0 : ℝ) < lam + (p : ℝ) / 2 := by positivity
    have hdiff : DifferentiableAt ℝ (fun a => fluctuation β (lam + (p : ℝ) / 2) a) a :=
      (hasDerivAt_fluctuation β (lam + (p : ℝ) / 2) hβ hpos a).differentiableAt
    rw [deriv_const_mul _ hdiff, deriv_fluctuation β (lam + (p : ℝ) / 2) hβ hpos a,
      show lam + (p : ℝ) / 2 + 1 / 2 = lam + ((↑(p + 1) : ℝ)) / 2 by push_cast; ring, pow_succ]
    ring

/-- **Insertion identity**: a `(√n u^k)^p` insertion in the 1D standard integral raises the order of
the fluctuation function by `p/2` and leaves the power of `n` unchanged. -/
theorem standardIntegral1D_insertion (β n a : ℝ) (h k p : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (∫ u in Set.Ioi (0 : ℝ), u ^ h * (Real.sqrt n * u ^ k) ^ p
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      = (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
        * fluctuation β (((h : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) a := by
  have hk0 : (2 * (k : ℝ)) ≠ 0 := by positivity
  have hsq : Real.sqrt n ^ p = n ^ ((p : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn.le]; congr 1; ring
  have hint : (fun u : ℝ => u ^ h * (Real.sqrt n * u ^ k) ^ p
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      = fun u => Real.sqrt n ^ p * (u ^ (h + k * p)
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a)) := by
    funext u; rw [mul_pow, ← pow_mul, pow_add]; ring
  rw [hint, integral_const_mul, standardIntegral1D_eq_fluctuation β n a (h + k * p) k hn hk, hsq,
    show (((h + k * p : ℕ) : ℝ) + 1) / (2 * k) = ((h : ℝ) + 1) / (2 * k) + (p : ℝ) / 2 by
      push_cast; field_simp; ring,
    show n ^ ((p : ℝ) / 2) * ((1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k) + (p : ℝ) / 2))
        * fluctuation β (((h : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) a)
      = (1 / (2 * (k : ℝ))) * (n ^ ((p : ℝ) / 2) * n ^ (-(((h : ℝ) + 1) / (2 * k) + (p : ℝ) / 2)))
        * fluctuation β (((h : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) a by ring,
    ← Real.rpow_add hn]
  congr 3; ring

/-- **Insertions are `a`-derivatives** (the 1D content of the Taylor tree's `∂^p S_μ(ξ(0))`): the
`(√n u^k)^p` insertion equals `β^{-p}` times the `p`-th `a`-derivative of the fluctuation function
at order `(h+1)/(2k)`. -/
theorem standardIntegral1D_insertion_deriv (β n a : ℝ) (h k p : ℕ) (hβ : 0 < β) (hn : 0 < n)
    (hk : 0 < k) :
    (∫ u in Set.Ioi (0 : ℝ), u ^ h * (Real.sqrt n * u ^ k) ^ p
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      = (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k))) * β ^ (-(p : ℤ))
        * iteratedDeriv p (fun a => fluctuation β (((h : ℝ) + 1) / (2 * k)) a) a := by
  have hlam : (0 : ℝ) < ((h : ℝ) + 1) / (2 * k) := by positivity
  rw [standardIntegral1D_insertion β n a h k p hn hk,
    iteratedDeriv_fluctuation β _ hβ hlam p, zpow_neg, zpow_natCast,
    show (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k))) * (β ^ p)⁻¹
        * (β ^ p * fluctuation β (((h : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) a)
      = (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k))) * ((β ^ p)⁻¹ * β ^ p)
        * fluctuation β (((h : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) a by ring,
    inv_mul_cancel₀ (pow_ne_zero p hβ.ne'), mul_one]

end Laplace.Grammar
