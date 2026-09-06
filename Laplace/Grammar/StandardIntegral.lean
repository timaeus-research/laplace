/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Fluctuation

/-!
# The standard integral and the fluctuation function (grammar §4.2)

The Taylor-tree analysis of grammar §4.2 rests on the *standard integral*
(`eq:per_chart_integral`), the per-chart Laplace integral

  `Z(β, n; ξ, η) = ∫_{[0,b]^d} u^h e^{-β n u^{2k} + β√n u^k ξ(u)} η(u) du`.

Its one-dimensional constant-coefficient population core — `d = 1`, `ξ ≡ a`, `η ≡ 1`, taken over the
full half-line `(0,∞)` — is exactly a rescaled fluctuation function. We prove

  `∫₀^∞ u^h e^{-β n u^{2k} + β√n u^k a} du = (2k)^{-1} n^{-(h+1)/(2k)} S_{(h+1)/(2k)}(a)`,

by the change of variables `t = n u^{2k}`. This identifies `S_λ` as the exact Mellin kernel of the
standard integral and shows where the *leading candidate exponent* `(h+1)/(2k)` of the exponent set
`Λ(h,k)` (`eq:candidateexponents`) comes from: it is the order of the fluctuation function produced
by the substitution. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- **The 1D constant-coefficient standard integral is a rescaled fluctuation function.** For the
substitution `t = n u^{2k}`, the full-line population standard integral (grammar §4.2
`eq:per_chart_integral`, `d = 1`, `ξ ≡ a`, `η ≡ 1`) equals
`(2k)^{-1} n^{-(h+1)/(2k)} S_{(h+1)/(2k)}(a)`. The order `(h+1)/(2k)` is the leading element of the
candidate exponent set `Λ(h,k)` (`eq:candidateexponents`). -/
theorem standardIntegral1D_eq_fluctuation (β n a : ℝ) (h k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    (∫ u in Set.Ioi (0 : ℝ), u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      = (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
        * fluctuation β (((h : ℝ) + 1) / (2 * k)) a := by
  set lam : ℝ := ((h : ℝ) + 1) / (2 * k) with hlamdef
  set p : ℝ := ((2 * k : ℕ) : ℝ) with hpdef
  have hp : (0 : ℝ) < p := by rw [hpdef]; positivity
  have hk0 : (2 * (k : ℝ)) ≠ 0 := by positivity
  have hpval : p = 2 * (k : ℝ) := by rw [hpdef]; push_cast; ring
  set G : ℝ → ℝ := fun t => t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t) with hGdef
  set Z : ℝ := ∫ u in Set.Ioi (0 : ℝ),
      u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a) with hZdef
  -- the change-of-variables substitutions
  have hmul : (∫ r in Set.Ioi (0 : ℝ), G (n * r)) = n⁻¹ * ∫ t in Set.Ioi (0 : ℝ), G t := by
    have := integral_comp_mul_left_Ioi G 0 hn
    rwa [mul_zero, smul_eq_mul] at this
  have hrpow : (∫ x in Set.Ioi (0 : ℝ), (p * x ^ (p - 1)) • G (n * x ^ p))
      = ∫ r in Set.Ioi (0 : ℝ), G (n * r) :=
    integral_comp_rpow_Ioi_of_pos (g := fun r => G (n * r)) hp
  -- the pointwise integrand identity after substitution
  have hintegrand : ∀ x ∈ Set.Ioi (0 : ℝ), (p * x ^ (p - 1)) • G (n * x ^ p)
      = 2 * (k : ℝ) * n ^ (lam - 1)
        * (x ^ h * Real.exp (-β * n * x ^ (2 * k) + β * Real.sqrt n * x ^ k * a)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hxp : x ^ p = x ^ (2 * k) := by rw [hpdef, Real.rpow_natCast]
    have hxsq : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    have hsqrt : Real.sqrt (n * x ^ (2 * k)) = Real.sqrt n * x ^ k := by
      rw [Real.sqrt_mul hn.le, hxsq, Real.sqrt_sq (pow_nonneg hx0.le k)]
    have hnpow : (n * x ^ p) ^ (lam - 1) = n ^ (lam - 1) * x ^ (p * (lam - 1)) := by
      rw [Real.mul_rpow hn.le (Real.rpow_nonneg hx0.le p), ← Real.rpow_mul hx0.le]
    have hexp : -β * (n * x ^ (2 * k)) + β * a * (Real.sqrt n * x ^ k)
        = -β * n * x ^ (2 * k) + β * Real.sqrt n * x ^ k * a := by ring
    have hexpo : x ^ (p - 1) * x ^ (p * (lam - 1)) = x ^ (h : ℝ) := by
      rw [← Real.rpow_add hx0]; congr 1; rw [hpval, hlamdef]; field_simp; ring
    have hxh : x ^ (h : ℝ) = x ^ h := Real.rpow_natCast x h
    simp only [smul_eq_mul, hGdef]
    rw [hnpow, hxp, hsqrt, hexp,
      show p * x ^ (p - 1) * (n ^ (lam - 1) * x ^ (p * (lam - 1))
          * Real.exp (-β * n * x ^ (2 * k) + β * Real.sqrt n * x ^ k * a))
        = p * n ^ (lam - 1) * (x ^ (p - 1) * x ^ (p * (lam - 1)))
          * Real.exp (-β * n * x ^ (2 * k) + β * Real.sqrt n * x ^ k * a) by ring,
      hexpo, hxh, hpval]
    ring
  -- assemble: fluctuation = 2k · n^lam · Z, then rearrange
  have hZeq : (∫ x in Set.Ioi (0 : ℝ), 2 * (k : ℝ) * n ^ (lam - 1)
        * (x ^ h * Real.exp (-β * n * x ^ (2 * k) + β * Real.sqrt n * x ^ k * a)))
      = 2 * (k : ℝ) * n ^ (lam - 1) * Z := by rw [integral_const_mul, hZdef]
  have hkey : fluctuation β lam a = 2 * (k : ℝ) * n ^ lam * Z := by
    have e1 : (∫ t in Set.Ioi (0 : ℝ), G t) = fluctuation β lam a := rfl
    calc fluctuation β lam a
        = ∫ t in Set.Ioi (0 : ℝ), G t := e1.symm
      _ = n * ∫ r in Set.Ioi (0 : ℝ), G (n * r) := by
          rw [hmul, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
      _ = n * ∫ x in Set.Ioi (0 : ℝ), (p * x ^ (p - 1)) • G (n * x ^ p) := by rw [hrpow]
      _ = n * (2 * (k : ℝ) * n ^ (lam - 1) * Z) := by
          rw [setIntegral_congr_fun measurableSet_Ioi hintegrand, hZeq]
      _ = 2 * (k : ℝ) * n ^ lam * Z := by
          rw [show n * (2 * (k : ℝ) * n ^ (lam - 1) * Z)
              = 2 * (k : ℝ) * (n * n ^ (lam - 1)) * Z by ring,
            show n * n ^ (lam - 1) = n ^ lam by
              nth_rewrite 1 [show n = n ^ (1 : ℝ) from (Real.rpow_one n).symm]
              rw [← Real.rpow_add hn]; congr 1; ring]
  rw [hkey,
    show (1 / (2 * (k : ℝ))) * n ^ (-lam) * (2 * (k : ℝ) * n ^ lam * Z)
      = ((2 * (k : ℝ)) / (2 * (k : ℝ))) * (n ^ (-lam) * n ^ lam) * Z by ring,
    div_self hk0, show n ^ (-lam) * n ^ lam = 1 by
      rw [← Real.rpow_add hn, neg_add_cancel, Real.rpow_zero]]
  ring

end Laplace.Grammar
