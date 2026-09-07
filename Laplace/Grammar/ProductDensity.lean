/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ProductDensityHelpers

/-!
# The recursive product-density lemma (general-`d` monomial model, step 2b)

`productIntegral λ d g` is the recursively defined iterated integral
`∫_{(0,1]^d} g(∏ tᵢ) ∏ tᵢ^{λ−1} dt` (dimension `0` gives `g 1`). The main theorem
(`productIntegral_succ_eq`) is the **product-density formula**

`∫_{(0,1]^{m+1}} g(∏ tᵢ) ∏ tᵢ^{λ−1} dt = (1/m!) ∫₀¹ g(z) z^{λ−1} (−log z)^m dz`

i.e. the pushforward of `∏ tᵢ^{λ−1} dt` under `t ↦ ∏ tᵢ` has density `z^{λ−1}(−log z)^m/m!` on
`(0,1]`. The induction step scales the inner variable, swaps the order on the triangle and uses the
FTC identity `∫_w^1 (log t − log w)^m/t dt = (−log w)^{m+1}/(m+1)` (units 165, 171).
Everything is in
`ℝ≥0∞`, for arbitrary measurable `g`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real

namespace Laplace.Grammar

/-- The iterated weighted integral `∫_{(0,1]^d} g(∏ tᵢ) ∏ tᵢ^{λ−1} dt`, recursively. -/
noncomputable def productIntegral (l : ℝ) : ℕ → (ℝ → ENNReal) → ENNReal
  | 0, g => g 1
  | n + 1, g => ∫⁻ t in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (t ^ (l - 1)) * productIntegral l n (fun z => g (t * z))

theorem productIntegral_zero (l : ℝ) (g : ℝ → ENNReal) : productIntegral l 0 g = g 1 := rfl

theorem productIntegral_succ (l : ℝ) (n : ℕ) (g : ℝ → ENNReal) :
    productIntegral l (n + 1) g = ∫⁻ t in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (t ^ (l - 1)) * productIntegral l n (fun z => g (t * z)) := rfl

/-- The density weight `z^{λ−1} (−log z)^m`. -/
noncomputable def logDensity (l : ℝ) (m : ℕ) (z : ℝ) : ℝ := z ^ (l - 1) * (-Real.log z) ^ m

theorem logDensity_nonneg (l : ℝ) (m : ℕ) (z : ℝ) (hz : 0 < z) (hz1 : z ≤ 1) :
    0 ≤ logDensity l m z := by
  unfold logDensity
  have h1 : 0 ≤ z ^ (l - 1) := Real.rpow_nonneg hz.le _
  have h2 : 0 ≤ -Real.log z := by
    have := Real.log_nonpos hz.le hz1; linarith
  positivity

/-- Joint measurability of the triangle integrand. -/
theorem measurable_triangle_integrand (l : ℝ) (m : ℕ) (g : ℝ → ENNReal) (hg : Measurable g) :
    Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (q.2 ^ (l - 1) * (Real.log q.1 - Real.log q.2) ^ m / q.1) * g q.2 := by
  refine Measurable.mul (Measurable.ennreal_ofReal ?_) (hg.comp measurable_snd)
  exact ((measurable_snd.pow_const (l - 1)).mul
    (((Real.measurable_log.comp measurable_fst).sub
      (Real.measurable_log.comp measurable_snd)).pow_const m)).div measurable_fst

/-- **Product-density formula**:
`∫_{(0,1]^{m+1}} g(∏ tᵢ) ∏ tᵢ^{λ−1} dt = (1/m!) ∫₀¹ g z z^{λ−1}(−log z)^m dz`. -/
theorem productIntegral_succ_eq (l : ℝ) (m : ℕ) :
    ∀ g : ℝ → ENNReal, Measurable g →
      productIntegral l (m + 1) g
        = ENNReal.ofReal (1 / (m.factorial : ℝ))
          * ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (logDensity l m z) * g z := by
  induction m with
  | zero =>
    intro g _
    rw [productIntegral_succ]
    simp only [productIntegral_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one,
      ENNReal.ofReal_one, one_mul]
    refine setLIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    unfold logDensity
    rw [pow_zero, mul_one]
  | succ m ih =>
    intro g hg
    rw [productIntegral_succ]
    have hinner : ∀ t : ℝ, productIntegral l (m + 1) (fun z => g (t * z))
        = ENNReal.ofReal (1 / (m.factorial : ℝ))
          * ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (logDensity l m z) * g (t * z) :=
      fun t => ih _ (hg.comp (measurable_const.mul measurable_id))
    simp_rw [hinner]
    -- the integrand of the outer integral, as a triangle integral
    have hstep : ∀ t ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal (t ^ (l - 1)) * (ENNReal.ofReal (1 / (m.factorial : ℝ))
          * ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (logDensity l m z) * g (t * z))
        = ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ w in Ioc (0 : ℝ) t,
            ENNReal.ofReal (w ^ (l - 1) * (Real.log t - Real.log w) ^ m / t) * g w := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have hsub : ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (logDensity l m z) * g (t * z)
          = ENNReal.ofReal (1 / t)
            * ∫⁻ w in Ioc (0 : ℝ) t, ENNReal.ofReal (logDensity l m (w / t)) * g w := by
        rw [← lintegral_Ioc_scale t ht0 (fun w => ENNReal.ofReal (logDensity l m (w / t)) * g w)]
        refine setLIntegral_congr_fun measurableSet_Ioc fun z _ => ?_
        rw [mul_div_cancel_left₀ z ht0.ne']
      have hkey : ∀ w : ℝ, 0 < w → t ^ (l - 1) * (1 / t * logDensity l m (w / t))
          = w ^ (l - 1) * (Real.log t - Real.log w) ^ m / t := by
        intro w hw0
        unfold logDensity
        rw [Real.div_rpow hw0.le ht0.le, Real.log_div hw0.ne' ht0.ne', neg_sub]
        have : t ^ (l - 1) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
        field_simp
      calc ENNReal.ofReal (t ^ (l - 1)) * (ENNReal.ofReal (1 / (m.factorial : ℝ))
              * ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (logDensity l m z) * g (t * z))
          = ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ w in Ioc (0 : ℝ) t,
              ENNReal.ofReal (t ^ (l - 1)) * (ENNReal.ofReal (1 / t)
                * (ENNReal.ofReal (logDensity l m (w / t)) * g w)) := by
            rw [hsub, lintegral_const_mul' (ENNReal.ofReal (t ^ (l - 1))) _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' (ENNReal.ofReal (1 / t)) _ ENNReal.ofReal_ne_top]
            ring
        _ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ w in Ioc (0 : ℝ) t,
              ENNReal.ofReal (w ^ (l - 1) * (Real.log t - Real.log w) ^ m / t) * g w := by
            congr 1
            refine setLIntegral_congr_fun measurableSet_Ioc fun w hw => ?_
            rw [← hkey w hw.1, ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _),
              ENNReal.ofReal_mul (by positivity)]
            ring
    rw [setLIntegral_congr_fun measurableSet_Ioc hstep,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_triangle_swap
        (fun t w => ENNReal.ofReal (w ^ (l - 1) * (Real.log t - Real.log w) ^ m / t) * g w)
        (measurable_triangle_integrand l m g hg)]
    -- evaluate the inner `t`-integral with the FTC identity
    have hin : ∀ w ∈ Ioc (0 : ℝ) 1,
        ∫⁻ t in Icc w 1, ENNReal.ofReal (w ^ (l - 1) * (Real.log t - Real.log w) ^ m / t) * g w
          = ENNReal.ofReal (w ^ (l - 1)) * g w
            * ENNReal.ofReal ((-Real.log w) ^ (m + 1) / ((m : ℝ) + 1)) := by
      intro w hw
      have hw0 : 0 < w := hw.1
      have hmeas : Measurable fun t : ℝ => ENNReal.ofReal ((Real.log t - Real.log w) ^ m / t) :=
        Measurable.ennreal_ofReal
          (((Real.measurable_log.sub measurable_const).pow_const m).div measurable_id)
      rw [← lintegral_log_sub_pow_div w hw0 hw.2 m, ← lintegral_const_mul'' _ hmeas.aemeasurable]
      refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
      rw [mul_div_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg hw0.le _)]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioc hin,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioc fun w hw => ?_
    have hw0 : 0 < w := hw.1
    have hfac : (1 : ℝ) / ((m + 1).factorial : ℝ) * logDensity l (m + 1) w
        = 1 / (m.factorial : ℝ) * (w ^ (l - 1) * ((-Real.log w) ^ (m + 1) / ((m : ℝ) + 1))) := by
      unfold logDensity
      rw [Nat.factorial_succ]
      push_cast
      have : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    have h1 : ENNReal.ofReal (1 / ((m + 1).factorial : ℝ))
          * (ENNReal.ofReal (logDensity l (m + 1) w) * g w)
        = ENNReal.ofReal (1 / ((m + 1).factorial : ℝ) * logDensity l (m + 1) w) * g w := by
      rw [ENNReal.ofReal_mul (by positivity)]; ring
    rw [h1, hfac, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (Real.rpow_nonneg hw0.le _)]
    ring

end Laplace.Grammar
