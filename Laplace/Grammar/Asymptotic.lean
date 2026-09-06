/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialTree

/-!
# Leading asymptotic of the chart standard integral (grammar §4.2)

The leading term of the standard asymptotic expansion (`cor:standardintegralexp`) in one dimension:
as `n → ∞`, the population standard integral over the chart `(0, b]` is asymptotically equivalent to

  `(2k)^{-1} S_{(h+1)/(2k)}(a) · n^{-(h+1)/(2k)}`,

with the *sharp* leading exponent `μ₁ = (h+1)/(2k)` (the first element of `Λ(h,k)`) and the
fluctuation function as its coefficient. This packages `standardIntegral1D_bounded_approx`: the
chart integral differs from the half-line value by `O(e^{-εn})`, which is `o(n^{-μ₁})`, and the
coefficient is nonzero because `S_λ(a) > 0` (`fluctuation_pos`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Asymptotics Filter Set

namespace Laplace.Grammar

/-- The fluctuation function is strictly positive: its integrand is positive on `(0, ∞)`. -/
theorem fluctuation_pos (β lam a : ℝ) (hβ : 0 < β) (hlam : 0 < lam) : 0 < fluctuation β lam a := by
  rw [fluctuation, setIntegral_pos_iff_support_of_nonneg_ae ?_
    (fluctuation_integrableOn β lam hβ hlam a)]
  · have hsub : Ioi (0 : ℝ) ⊆ Function.support
        (fun t : ℝ => t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)) ∩ Ioi 0 := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      refine ⟨?_, ht⟩
      rw [Function.mem_support]
      positivity
    calc (0 : ENNReal) < volume (Ioi (0 : ℝ)) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
      _ ≤ _ := measure_mono hsub
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    change (0 : ℝ) ≤ t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
    positivity

/-- **Leading asymptotic of the chart standard integral** (grammar §4.2, the leading term of
`cor:standardintegralexp` in one dimension): as `n → ∞`,
`∫₀^b u^h e^{-βn u^{2k} + β√n u^k a} du ~ (2k)^{-1} n^{-(h+1)/(2k)} S_{(h+1)/(2k)}(a)`. The exponent
`(h+1)/(2k)` is sharp since `S_{(h+1)/(2k)}(a) > 0`. -/
theorem standardIntegral1D_chart_isEquivalent (β a b : ℝ) (h k : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk : 0 < k) :
    (fun n : ℝ => ∫ u in Ioc 0 b,
        u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      ~[atTop] fun n : ℝ => (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
        * fluctuation β (((h : ℝ) + 1) / (2 * k)) a := by
  set lam : ℝ := ((h : ℝ) + 1) / (2 * k) with hlam
  have hlam0 : 0 < lam := by positivity
  set S : ℝ := fluctuation β lam a with hS
  have hSpos : 0 < S := fluctuation_pos β lam a hβ hlam0
  set K : ℝ := Real.exp (β * a ^ 2 / 2)
    * ((β / 4) ^ (-lam) * (1 / (2 * (k : ℝ))) * Real.Gamma lam) with hK
  set ε : ℝ := (β / 4) * b ^ (2 * k) with hε
  have hε0 : 0 < ε := by positivity
  apply IsLittleO.isEquivalent
  have hbigO : (fun n : ℝ => (∫ u in Ioc 0 b,
        u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
        - (1 / (2 * (k : ℝ))) * n ^ (-lam) * S)
      =O[atTop] fun n : ℝ => Real.exp (-ε * n) := by
    apply IsBigO.of_bound K
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
    have hbnd := standardIntegral1D_bounded_approx β n a b h k hβ hn hb hk
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc |(∫ u in Ioc 0 b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
          - (1 / (2 * (k : ℝ))) * n ^ (-lam) * S|
        ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 4) * n * b ^ (2 * k))
          * ((β / 4) ^ (-lam) * (1 / (2 * (k : ℝ))) * Real.Gamma lam) := hbnd
      _ = K * Real.exp (-ε * n) := by
          rw [show -(β / 4) * n * b ^ (2 * k) = -ε * n by rw [hε]; ring, hK]; ring
  have hlittle : (fun n : ℝ => Real.exp (-ε * n))
      =o[atTop] fun n : ℝ => (1 / (2 * (k : ℝ))) * n ^ (-lam) * S := by
    have := (isLittleO_exp_neg_mul_rpow_atTop hε0 (-lam)).const_mul_right
      (c := (1 / (2 * (k : ℝ))) * S) (by positivity)
    rwa [show (fun x : ℝ => (1 / (2 * (k : ℝ))) * S * x ^ (-lam))
      = fun n : ℝ => (1 / (2 * (k : ℝ))) * n ^ (-lam) * S from funext fun x => by ring] at this
  exact hbigO.trans_isLittleO hlittle

end Laplace.Grammar
