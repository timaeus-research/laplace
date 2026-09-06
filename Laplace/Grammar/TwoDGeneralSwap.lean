/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDGeneralNoLog

/-!
# Symmetry of the general two-dimensional integral and the trichotomy (grammar §4.2)

The general chart integral is symmetric under exchanging the two coordinates (Fubini on the compact
box), which turns unit 46's `p₁ < p₂` theorem into the `p₁ > p₂` one. Together with unit 45 this
gives the **trichotomy** for the leading behaviour of the two-dimensional standard integral with
arbitrary exponents: with `p_i = (h_i+1)/k_i`,

* `p₁ < p₂`: `Z ~ c n^{-p₁/2}`;
* `p₁ = p₂`: `Z ~ c n^{-p₁/2} log n`;
* `p₁ > p₂`: `Z ~ c n^{-p₂/2}`,

and unconditionally `Z(n) = O(n^{-min(p₁,p₂)/2} log n)`, the leading-term content of
`thm:TaylorTree` in two dimensions. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- Exchanging the two coordinates. -/
theorem twoDGeneral_swap (β a b n : ℝ) (h₁ h₂ k₁ k₂ : ℕ) :
    twoDGeneral β a b n h₁ h₂ k₁ k₂ = twoDGeneral β a b n h₂ h₁ k₂ k₁ := by
  unfold twoDGeneral
  have hcont : Continuous (fun z : ℝ × ℝ => z.1 ^ h₁ * z.2 ^ h₂
      * Real.exp (-β * n * (z.1 ^ k₁ * z.2 ^ k₂) ^ 2
        + β * Real.sqrt n * (z.1 ^ k₁ * z.2 ^ k₂) * a)) := by fun_prop
  have hint : Integrable (Function.uncurry fun u v : ℝ => u ^ h₁ * v ^ h₂
      * Real.exp (-β * n * (u ^ k₁ * v ^ k₂) ^ 2 + β * Real.sqrt n * (u ^ k₁ * v ^ k₂) * a))
      (((volume : Measure ℝ).restrict (Ioc 0 b)).prod
        ((volume : Measure ℝ).restrict (Ioc 0 b))) := by
    rw [Measure.prod_restrict]
    exact (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [show u ^ k₁ * v ^ k₂ = v ^ k₂ * u ^ k₁ by ring]
  ring

/-- **`p₁ > p₂` ⇒ no logarithm**: the other coordinate is dominant. -/
theorem twoDGeneral_isEquivalent_of_gt (β a b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hgt : ((h₂ : ℝ) + 1) / k₂ < ((h₁ : ℝ) + 1) / k₁) :
    (fun n : ℝ => twoDGeneral β a b n h₁ h₂ k₁ k₂) ~[atTop]
      fun n : ℝ => 1 / ((k₂ : ℝ) * k₁)
        * b ^ ((k₁ : ℝ) * (((h₁ : ℝ) + 1) / k₁ - ((h₂ : ℝ) + 1) / k₂))
        * noLogConst β a (((h₂ : ℝ) + 1) / k₂) (((h₁ : ℝ) + 1) / k₁)
        * n ^ (-(((h₂ : ℝ) + 1) / k₂ / 2)) := by
  have h := twoDGeneral_isEquivalent_of_lt β a b h₂ h₁ k₂ k₁ hβ hb hk₂ hk₁ hgt
  refine h.congr_left (Filter.Eventually.of_forall fun n => ?_)
  exact (twoDGeneral_swap β a b n h₁ h₂ k₁ k₂).symm

/-- `n^r = O(n^r log n)`. -/
theorem isBigO_rpow_rpow_mul_log (r : ℝ) :
    (fun n : ℝ => n ^ r) =O[atTop] fun n : ℝ => n ^ r * Real.log n :=
  (isLittleO_rpow_rpow_mul_log r).isBigO

/-- **Trichotomy, unconditional form**: `Z(n) = O(n^{-min(p₁,p₂)/2} log n)`. -/
theorem twoDGeneral_isBigO_min (β a b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    (fun n : ℝ => twoDGeneral β a b n h₁ h₂ k₁ k₂) =O[atTop]
      fun n : ℝ => n ^ (-(min (((h₁ : ℝ) + 1) / k₁) (((h₂ : ℝ) + 1) / k₂) / 2)) * Real.log n := by
  rcases lt_trichotomy (((h₁ : ℝ) + 1) / k₁) (((h₂ : ℝ) + 1) / k₂) with hlt | heq | hgt
  · rw [min_eq_left hlt.le]
    have h := (twoDGeneral_isEquivalent_of_lt β a b h₁ h₂ k₁ k₂ hβ hb hk₁ hk₂ hlt).isBigO
    refine h.trans ?_
    have h2 := (isBigO_rpow_rpow_mul_log (-(((h₁ : ℝ) + 1) / k₁ / 2))).const_mul_left
      (1 / ((k₁ : ℝ) * k₂) * b ^ ((k₂ : ℝ) * (((h₂ : ℝ) + 1) / k₂ - ((h₁ : ℝ) + 1) / k₁))
        * noLogConst β a (((h₁ : ℝ) + 1) / k₁) (((h₂ : ℝ) + 1) / k₂))
    exact h2
  · rw [min_eq_left heq.le]
    have h := (twoDGeneral_isEquivalent_of_eq β a b h₁ h₂ k₁ k₂ hβ hb hk₁ hk₂ heq).isBigO
    refine h.trans ?_
    exact (isBigO_refl _ _).const_mul_left _
  · rw [min_eq_right hgt.le]
    have h := (twoDGeneral_isEquivalent_of_gt β a b h₁ h₂ k₁ k₂ hβ hb hk₁ hk₂ hgt).isBigO
    refine h.trans ?_
    have h2 := (isBigO_rpow_rpow_mul_log (-(((h₂ : ℝ) + 1) / k₂ / 2))).const_mul_left
      (1 / ((k₂ : ℝ) * k₁) * b ^ ((k₁ : ℝ) * (((h₁ : ℝ) + 1) / k₁ - ((h₂ : ℝ) + 1) / k₂))
        * noLogConst β a (((h₂ : ℝ) + 1) / k₂) (((h₁ : ℝ) + 1) / k₁))
    exact h2

end Laplace.Grammar
