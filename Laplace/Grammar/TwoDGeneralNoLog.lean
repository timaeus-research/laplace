/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDGeneralLog

/-!
# The general `(k, h)` two-dimensional integral: distinct exponents give no logarithm (grammar §4.2)

For `p₁ < p₂` (the first coordinate carries the strictly smaller candidate exponent `p₁/2`,
multiplicity one) the integral `∫₀^∞ x^{p₁−p₂−1} F_{p₂−1}(x) dx` converges to a positive constant
`C(p₁, p₂)` (`noLogConst`), and the exact reduction of unit 44 gives

  `Z(n) ~ (1/(k₁k₂)) · b^{k₂(p₂−p₁)} · C(p₁, p₂) · n^{-p₁/2}`.

At `k = (1,1)`, `h = (0,1)` this is unit 37's `(b S_{1/2}(a)/2) n^{-1/2}` (there `C = A`).
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- `F_γ(x) > 0` for `x > 0`. -/
theorem weightedPrimitive_pos (β a γ x : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hx : 0 < x) :
    0 < weightedPrimitive β a γ x := by
  rw [weightedPrimitive, setIntegral_pos_iff_support_of_nonneg_ae ?_
    ((weightedKernel_integrableOn β a γ hβ hγ).mono_set Ioc_subset_Ioi_self)]
  · have hsub : Ioc (0 : ℝ) x
        ⊆ Function.support (fun t : ℝ => t ^ γ * quadKernel β a t) ∩ Ioc 0 x := by
      intro t ht
      refine ⟨?_, ht⟩
      rw [Function.mem_support]
      exact (mul_pos (Real.rpow_pos_of_pos ht.1 γ) (quadKernel_pos β a t)).ne'
    calc (0 : ENNReal) < volume (Ioc (0 : ℝ) x) := by
          rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_pos.2 hx
      _ ≤ _ := measure_mono hsub
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun t ht =>
      mul_nonneg (Real.rpow_nonneg ht.1.le γ) (quadKernel_pos β a t).le

/-- The noncritical integrand `x^{p₁−p₂−1} F_{p₂−1}(x)` is integrable on `(0, ∞)` when
`0 < p₁ < p₂`. -/
theorem noLog_integrand_integrableOn (β a p₁ p₂ : ℝ) (hβ : 0 < β) (hp₁ : 0 < p₁)
    (hlt : p₁ < p₂) :
    IntegrableOn (fun x => x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x) (Ioi 0) := by
  have hγ : -1 < p₂ - 1 := by linarith
  have hmeas : Measurable (fun x : ℝ => x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x) :=
    (measurable_id.pow_const _).mul (weightedPrimitive_measurable β a (p₂ - 1) hβ hγ)
  have h1 : IntegrableOn (fun x => x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x)
      (Ioc 0 1) := by
    refine Integrable.mono' (g := fun x => Real.exp (β * a ^ 2 / 2) / p₂ * x ^ (p₁ - 1))
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < p₁ - 1)
        (a := 0) (b := 1)).1.const_mul _)
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _)
      (weightedPrimitive_nonneg β a _ x))]
    calc x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x
        ≤ x ^ (p₁ - p₂ - 1) * (Real.exp (β * a ^ 2 / 2) * x ^ (p₂ - 1 + 1) / (p₂ - 1 + 1)) :=
          mul_le_mul_of_nonneg_left (weightedPrimitive_le β a (p₂ - 1) x hβ hγ hx0.le)
            (Real.rpow_nonneg hx0.le _)
      _ = Real.exp (β * a ^ 2 / 2) / p₂ * x ^ (p₁ - 1) := by
          rw [show p₂ - 1 + 1 = p₂ by ring, show p₁ - 1 = (p₁ - p₂ - 1) + p₂ by ring,
            Real.rpow_add hx0]
          ring
  have h2 : IntegrableOn (fun x => x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x)
      (Ioi 1) := by
    refine Integrable.mono' (g := fun x => weightedMass β a (p₂ - 1) * x ^ (p₁ - p₂ - 1))
      ((integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _)
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _)
      (weightedPrimitive_nonneg β a _ x))]
    calc x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x
        ≤ x ^ (p₁ - p₂ - 1) * weightedMass β a (p₂ - 1) :=
          mul_le_mul_of_nonneg_left (weightedPrimitive_le_mass β a (p₂ - 1) x hβ hγ hx0.le)
            (Real.rpow_nonneg hx0.le _)
      _ = weightedMass β a (p₂ - 1) * x ^ (p₁ - p₂ - 1) := mul_comm _ _
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this

/-- The noncritical constant `C(p₁, p₂) = ∫₀^∞ x^{p₁−p₂−1} F_{p₂−1}(x) dx`. -/
noncomputable def noLogConst (β a p₁ p₂ : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x

theorem noLogConst_pos (β a p₁ p₂ : ℝ) (hβ : 0 < β) (hp₁ : 0 < p₁) (hlt : p₁ < p₂) :
    0 < noLogConst β a p₁ p₂ := by
  have hγ : -1 < p₂ - 1 := by linarith
  rw [noLogConst, setIntegral_pos_iff_support_of_nonneg_ae ?_
    (noLog_integrand_integrableOn β a p₁ p₂ hβ hp₁ hlt)]
  · have hsub : Ioi (0 : ℝ) ⊆ Function.support
        (fun x : ℝ => x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x) ∩ Ioi 0 := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      refine ⟨?_, hx⟩
      rw [Function.mem_support]
      exact (mul_pos (Real.rpow_pos_of_pos hx0 _)
        (weightedPrimitive_pos β a (p₂ - 1) x hβ hγ hx0)).ne'
    calc (0 : ENNReal) < volume (Ioi (0 : ℝ)) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
      _ ≤ _ := measure_mono hsub
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    exact mul_nonneg (Real.rpow_nonneg hx0.le _) (weightedPrimitive_nonneg β a _ x)

/-- The truncated integral converges to `C(p₁, p₂)` along `L = √n b^k → ∞`. -/
theorem noLog_tendsto (β a b p₁ p₂ : ℝ) (k : ℕ) (hβ : 0 < β) (hb : 0 < b) (hp₁ : 0 < p₁)
    (hlt : p₁ < p₂) :
    Tendsto (fun n : ℝ => ∫ x in Ioc (0 : ℝ) (Real.sqrt n * b ^ k),
        x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x)
      atTop (𝓝 (noLogConst β a p₁ p₂)) := by
  have hL : Tendsto (fun n : ℝ => Real.sqrt n * b ^ k) atTop atTop :=
    tendsto_sqrt_atTop.atTop_mul_const (pow_pos hb _)
  have h := intervalIntegral_tendsto_integral_Ioi 0
    (noLog_integrand_integrableOn β a p₁ p₂ hβ hp₁ hlt) hL
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with n hn
  exact intervalIntegral.integral_of_le (by positivity)

/-- **Distinct exponents ⇒ no logarithm, general `(k, h)`**: for `p₁ = (h₁+1)/k₁ < p₂ = (h₂+1)/k₂`,
`Z(n) ~ (1/(k₁k₂)) b^{k₂(p₂−p₁)} C(p₁,p₂) n^{-p₁/2}`. -/
theorem twoDGeneral_isEquivalent_of_lt (β a b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hlt : ((h₁ : ℝ) + 1) / k₁ < ((h₂ : ℝ) + 1) / k₂) :
    (fun n : ℝ => twoDGeneral β a b n h₁ h₂ k₁ k₂) ~[atTop]
      fun n : ℝ => 1 / ((k₁ : ℝ) * k₂)
        * b ^ ((k₂ : ℝ) * (((h₂ : ℝ) + 1) / k₂ - ((h₁ : ℝ) + 1) / k₁))
        * noLogConst β a (((h₁ : ℝ) + 1) / k₁) (((h₂ : ℝ) + 1) / k₂)
        * n ^ (-(((h₁ : ℝ) + 1) / k₁ / 2)) := by
  obtain ⟨p₁, hp₁⟩ : ∃ p : ℝ, p = ((h₁ : ℝ) + 1) / k₁ := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂⟩ : ∃ p : ℝ, p = ((h₂ : ℝ) + 1) / k₂ := ⟨_, rfl⟩
  rw [← hp₁, ← hp₂] at hlt ⊢
  have hp₁0 : 0 < p₁ := by rw [hp₁]; positivity
  have hC := noLogConst_pos β a p₁ p₂ hβ hp₁0 hlt
  have hZ : ∀ n : ℝ, 0 < n → twoDGeneral β a b n h₁ h₂ k₁ k₂
      = (1 / ((k₁ : ℝ) * k₂) * b ^ ((k₂ : ℝ) * (p₂ - p₁))) * n ^ (-(p₁ / 2))
        * ∫ x in Ioc (0 : ℝ) (Real.sqrt n * b ^ (k₁ + k₂)),
            x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x := by
    intro n hn
    rw [twoDGeneral_eq β a b n h₁ h₂ k₁ k₂ hn hb hk₁ hk₂, ← hp₁, ← hp₂]
    ring
  have hI : (fun n : ℝ => ∫ x in Ioc (0 : ℝ) (Real.sqrt n * b ^ (k₁ + k₂)),
      x ^ (p₁ - p₂ - 1) * weightedPrimitive β a (p₂ - 1) x)
      ~[atTop] Function.const ℝ (noLogConst β a p₁ p₂) :=
    (isEquivalent_const_iff_tendsto hC.ne').2 (noLog_tendsto β a b p₁ p₂ (k₁ + k₂) hβ hb hp₁0 hlt)
  have hmain := (IsEquivalent.refl
    (u := fun n : ℝ => (1 / ((k₁ : ℝ) * k₂) * b ^ ((k₂ : ℝ) * (p₂ - p₁))) * n ^ (-(p₁ / 2)))
    (l := atTop)).mul hI
  refine (hmain.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    simp only [Pi.mul_apply]
    exact (hZ n hn).symm
  · refine Filter.Eventually.of_forall fun n => ?_
    simp only [Pi.mul_apply, Function.const_apply]
    ring

end Laplace.Grammar
