/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.GaussianBound
import Laplace.Grammar.StandardIntegral

/-!
# The boundary tail of the standard integral is exponentially small (grammar §4.2)

The paper's standard integral lives on the bounded chart `[0,b]`, while the fluctuation-function
identity `standardIntegral1D_eq_fluctuation` is stated on the full half-line. The difference is the
tail over `[b, ∞)`, which the proof of `thm:TaylorTree` controls by `e^{-βT/4}` with `T = n b^{2k}`
(`eq:Deltaupper`). We prove the one-dimensional population version:

  `∫_b^∞ u^h e^{-βn u^{2k} + β√n u^k a} du
      ≤ e^{βa²/2} e^{-(β/4) n b^{2k}} · (β/4)^{-(h+1)/(2k)} (2k)^{-1} Γ((h+1)/(2k))`   for `n ≥ 1`,

so the bounded-chart standard integral equals `(2k)^{-1} n^{-(h+1)/(2k)} S_{(h+1)/(2k)}(a)` up to an
`O(e^{-εn})` error with `ε = (β/4) b^{2k}`. Ingredients: Gaussian domination of the integrand
(`fluctuation_integrand_le` at `t = n u^{2k}`), `u^{2k} ≥ b^{2k}` on the tail, and the Gamma
integral.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- Gaussian domination of the standard integrand: `e^{-βn u^{2k} + β√n u^k a} ≤ e^{βa²/2}
e^{-(β/2) n u^{2k}}` (this is `fluctuation_integrand_le` at `t = n u^{2k}`). -/
theorem standardIntegrand_le (β n a u : ℝ) (k : ℕ) (hβ : 0 < β) (hn : 0 ≤ n) (hu : 0 ≤ u) :
    Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a)
      ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2 * n) * u ^ (2 * k)) := by
  have hsqrt : Real.sqrt (n * u ^ (2 * k)) = Real.sqrt n * u ^ k := by
    rw [Real.sqrt_mul hn, show u ^ (2 * k) = (u ^ k) ^ 2 by rw [← pow_mul, Nat.mul_comm],
      Real.sqrt_sq (pow_nonneg hu k)]
  have h := fluctuation_integrand_le β a (n * u ^ (2 * k)) hβ (by positivity)
  rw [hsqrt] at h
  rw [← Real.exp_add]
  calc Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a)
      = Real.exp (-β * (n * u ^ (2 * k)) + β * a * (Real.sqrt n * u ^ k)) := by congr 1; ring
    _ ≤ Real.exp (-(β / 2) * (n * u ^ (2 * k)) + β * a ^ 2 / 2) := h
    _ = Real.exp (β * a ^ 2 / 2 + -(β / 2 * n) * u ^ (2 * k)) := by congr 1; ring

/-- The standard integrand is integrable on `(0, ∞)`. -/
theorem standardIntegrand_integrableOn (β n a : ℝ) (h k : ℕ) (hβ : 0 < β) (hn : 0 < n)
    (hk : 0 < k) :
    IntegrableOn
      (fun u : ℝ => u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      (Ioi 0) := by
  have hh : (-1 : ℝ) < (h : ℝ) := by linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  have hmaj0 : IntegrableOn
      (fun u : ℝ => u ^ ((h : ℝ)) * Real.exp (-(β / 2 * n) * u ^ (((2 * k : ℕ) : ℝ)))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hh (by positivity) (by positivity)
  have hfun : (fun u : ℝ => u ^ ((h : ℝ)) * Real.exp (-(β / 2 * n) * u ^ (((2 * k : ℕ) : ℝ))))
      = fun u => u ^ h * Real.exp (-(β / 2 * n) * u ^ (2 * k)) := by
    funext u; rw [Real.rpow_natCast, Real.rpow_natCast]
  rw [hfun] at hmaj0
  refine Integrable.mono' (hmaj0.const_mul (Real.exp (β * a ^ 2 / 2))) ?_ ?_
  · exact (by fun_prop : Continuous
      (fun u : ℝ => u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a)))
      |>.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a)
        ≤ u ^ h * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2 * n) * u ^ (2 * k))) :=
          mul_le_mul_of_nonneg_left (standardIntegrand_le β n a u k hβ hn.le hu0.le)
            (pow_nonneg hu0.le h)
      _ = Real.exp (β * a ^ 2 / 2) * (u ^ h * Real.exp (-(β / 2 * n) * u ^ (2 * k))) := by ring

/-- **Exponentially small tail** (grammar §4.2, the `e^{-βT/4}` step of `eq:Deltaupper` with
`T = n b^{2k}`): for `n ≥ 1`, the tail of the 1D standard integral over `(b, ∞)` is at most
`e^{βa²/2} e^{-(β/4) n b^{2k}}` times the Gamma constant
`(β/4)^{-(h+1)/(2k)} (2k)^{-1} Γ((h+1)/(2k))`. -/
theorem standardIntegral1D_tail_le (β n a b : ℝ) (h k : ℕ) (hβ : 0 < β) (hn : 1 ≤ n) (hb : 0 < b)
    (hk : 0 < k) :
    (∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 4) * n * b ^ (2 * k))
        * ((β / 4) ^ (-(((h : ℝ) + 1) / (2 * k))) * (1 / (2 * (k : ℝ)))
          * Real.Gamma (((h : ℝ) + 1) / (2 * k))) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hh : (-1 : ℝ) < (h : ℝ) := by linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  set C : ℝ := Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 4) * n * b ^ (2 * k)) with hC
  set g : ℝ → ℝ := fun u => u ^ h * Real.exp (-(β / 4) * u ^ (2 * k)) with hg
  have hgfun : g = fun u => u ^ ((h : ℝ)) * Real.exp (-(β / 4) * u ^ (((2 * k : ℕ) : ℝ))) := by
    funext u; simp only [hg, Real.rpow_natCast]
  have hg0 : IntegrableOn g (Ioi 0) := by
    rw [hgfun]; exact integrableOn_rpow_mul_exp_neg_mul_rpow hh (by positivity) (by positivity)
  have hgval : (∫ u in Ioi 0, g u)
      = (β / 4) ^ (-(((h : ℝ) + 1) / (2 * k))) * (1 / (2 * (k : ℝ)))
        * Real.Gamma (((h : ℝ) + 1) / (2 * k)) := by
    rw [hgfun, integral_rpow_mul_exp_neg_mul_rpow (by positivity) hh (by positivity)]
    push_cast; rw [neg_div]
  have hf_int : IntegrableOn
      (fun u : ℝ => u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      (Ioi b) :=
    (standardIntegrand_integrableOn β n a h k hβ hn0 hk).mono_set (Ioi_subset_Ioi hb.le)
  have hCg0 : IntegrableOn (fun u => C * g u) (Ioi 0) := hg0.const_mul C
  have hCg_int : IntegrableOn (fun u => C * g u) (Ioi b) := hCg0.mono_set (Ioi_subset_Ioi hb.le)
  have hpt : ∀ u ∈ Ioi b,
      u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a) ≤ C * g u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hb.trans hu
    have hub : b ^ (2 * k) ≤ u ^ (2 * k) := pow_le_pow_left₀ hb.le (le_of_lt hu) _
    have hexp2 : Real.exp (-(β / 2 * n) * u ^ (2 * k))
        ≤ Real.exp (-(β / 4) * n * b ^ (2 * k)) * Real.exp (-(β / 4) * u ^ (2 * k)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg (mul_nonneg hβ.le hn0.le) (sub_nonneg.2 hub),
        mul_nonneg (mul_nonneg hβ.le (sub_nonneg.2 hn)) (pow_nonneg hu0.le (2 * k))]
    calc u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a)
        ≤ u ^ h * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2 * n) * u ^ (2 * k))) :=
          mul_le_mul_of_nonneg_left (standardIntegrand_le β n a u k hβ hn0.le hu0.le)
            (pow_nonneg hu0.le h)
      _ ≤ u ^ h * (Real.exp (β * a ^ 2 / 2)
            * (Real.exp (-(β / 4) * n * b ^ (2 * k)) * Real.exp (-(β / 4) * u ^ (2 * k)))) := by
          gcongr
      _ = C * g u := by simp only [hC, hg]; ring
  have hCg_nonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u => C * g u := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    simp only [hC, hg, Pi.zero_apply]
    positivity
  calc (∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      ≤ ∫ u in Ioi b, C * g u := setIntegral_mono_on hf_int hCg_int measurableSet_Ioi hpt
    _ ≤ ∫ u in Ioi 0, C * g u :=
        setIntegral_mono_set hCg0 hCg_nonneg (Ioi_subset_Ioi hb.le).eventuallyLE
    _ = C * ∫ u in Ioi 0, g u := integral_const_mul _ _
    _ = _ := by rw [hgval]

/-- **Bounded-chart standard integral up to an exponentially small error**: on the paper's chart
`(0, b]`, the 1D standard integral equals `(2k)^{-1} n^{-(h+1)/(2k)} S_{(h+1)/(2k)}(a)` up to
`O(e^{-(β/4) b^{2k} n})`. -/
theorem standardIntegral1D_bounded_approx (β n a b : ℝ) (h k : ℕ) (hβ : 0 < β) (hn : 1 ≤ n)
    (hb : 0 < b) (hk : 0 < k) :
    |(∫ u in Ioc 0 b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
        - (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
          * fluctuation β (((h : ℝ) + 1) / (2 * k)) a|
      ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 4) * n * b ^ (2 * k))
        * ((β / 4) ^ (-(((h : ℝ) + 1) / (2 * k))) * (1 / (2 * (k : ℝ)))
          * Real.Gamma (((h : ℝ) + 1) / (2 * k))) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hint := standardIntegrand_integrableOn β n a h k hβ hn0 hk
  have hsplit :
      (∫ u in Ioi 0, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
      = (∫ u in Ioc 0 b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a))
        + ∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a) := by
    rw [← Ioc_union_Ioi_eq_Ioi hb.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hb.le))]
  have htail_nonneg : 0 ≤ ∫ u in Ioi b,
      u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * a) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (pow_nonneg (hb.trans hu).le h) (Real.exp_pos _).le
  rw [← standardIntegral1D_eq_fluctuation β n a h k hn0 hk, hsplit, sub_add_cancel_left, abs_neg,
    abs_of_nonneg htail_nonneg]
  exact standardIntegral1D_tail_le β n a b h k hβ hn hb hk

end Laplace.Grammar
