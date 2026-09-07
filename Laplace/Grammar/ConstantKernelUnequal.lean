/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ConstantKernelBound

/-!
# The product-kernel block with unequal exponents (grammar §4.2, mixed blocks)

For `p₁ = (h₁+1)/k₁ < p₂ = (h₂+1)/k₂` and a nonnegative kernel `g`, the product-kernel block is
bounded by the smaller exponent alone (Astra #5(d)):

  `J(t) ≤ b^{k₂(p₂-p₁)} / (k₁k₂(p₂-p₁)) · M_{p₁}(g) · t^{-p₁}`,   `t > 0`.

The density of unit 103 with the constant amplitude `g` is
`k₂⁻¹ r^{p₂-1} g(tr) (ε^{-γ} − b^{-γ})/γ`, `γ = k₁(p₂−p₁)`, `ε = (r/b^{k₂})^{1/k₁}`, which is at
most `b^{k₂(p₂-p₁)}/(k₁k₂(p₂-p₁)) · r^{p₁-1} g(tr)`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- The constant-amplitude density with unequal exponents is dominated by `C r^{p₁-1} g(tr)`. -/
theorem genDensity_const_le (b p₁ p₂ : ℝ) (h₁ k₁ k₂ : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hlt : p₁ < p₂) (g : ℝ → ℝ) (hg0 : ∀ s, 0 ≤ g s)
    (r s : ℝ) (hr : 0 < r) (hrR : r ≤ b ^ (k₁ + k₂)) :
    genDensity p₂ b h₁ k₁ k₂ (fun _ s => g s) r s
      ≤ b ^ ((k₂ : ℝ) * (p₂ - p₁)) / ((k₁ : ℝ) * k₂ * (p₂ - p₁)) * (r ^ (p₁ - 1) * g s) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hδ : 0 < p₂ - p₁ := by linarith
  have hbk : 0 < b ^ k₂ := by positivity
  set ε : ℝ := (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos (div_pos hr hbk) _
  have hεb : ε ≤ b := by
    have : (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) ≤ (b ^ k₁) ^ ((k₁ : ℝ)⁻¹) := by
      refine Real.rpow_le_rpow (div_pos hr hbk).le ?_ (by positivity)
      rw [div_le_iff₀ hbk, ← pow_add]; exact hrR
    rwa [Real.pow_rpow_inv_natCast hb.le hk₁.ne'] at this
  -- the weight exponent
  set w : ℝ := (h₁ : ℝ) - k₁ * p₂ with hw
  have hw1 : w + 1 = -((k₁ : ℝ) * (p₂ - p₁)) := by
    rw [hw, ← hp₁]; field_simp; ring
  have hwne : w ≠ -1 := by
    intro h
    have : w + 1 = 0 := by linarith
    rw [hw1] at this
    have : (k₁ : ℝ) * (p₂ - p₁) = 0 := by linarith
    exact absurd this (by positivity)
  unfold genDensity
  beta_reduce
  rw [integral_mul_const, integral_Icc_eq_integral_Ioc, integral_rpow_Ioc ε b w hε0 hεb,
    if_neg hwne, hw1]
  -- `ε^{-γ} = r^{-(p₂-p₁)} b^{k₂(p₂-p₁)}`
  have hεpow : ε ^ (-((k₁ : ℝ) * (p₂ - p₁)))
      = r ^ (-(p₂ - p₁)) * b ^ ((k₂ : ℝ) * (p₂ - p₁)) := by
    rw [hε, ← Real.rpow_mul (div_pos hr hbk).le, Real.div_rpow hr.le hbk.le,
      show (k₁ : ℝ)⁻¹ * -((k₁ : ℝ) * (p₂ - p₁)) = -(p₂ - p₁) by field_simp,
      ← Real.rpow_natCast b k₂, ← Real.rpow_mul hb.le, div_eq_mul_inv, ← Real.rpow_neg hb.le]
    congr 2
    ring
  have hbneg : 0 ≤ b ^ (-((k₁ : ℝ) * (p₂ - p₁))) := Real.rpow_nonneg hb.le _
  have hrp : r ^ (p₂ - 1) * r ^ (-(p₂ - p₁)) = r ^ (p₁ - 1) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hgs := hg0 s
  have hr2 : 0 ≤ r ^ (p₂ - 1) := Real.rpow_nonneg hr.le _
  have hbpow : 0 ≤ b ^ ((k₂ : ℝ) * (p₂ - p₁)) := Real.rpow_nonneg hb.le _
  calc 1 / (k₂ : ℝ) * r ^ (p₂ - 1)
        * ((b ^ (-((k₁ : ℝ) * (p₂ - p₁))) - ε ^ (-((k₁ : ℝ) * (p₂ - p₁))))
          / (-((k₁ : ℝ) * (p₂ - p₁))) * g s)
      = 1 / (k₂ : ℝ) * r ^ (p₂ - 1)
        * ((ε ^ (-((k₁ : ℝ) * (p₂ - p₁))) - b ^ (-((k₁ : ℝ) * (p₂ - p₁))))
          / ((k₁ : ℝ) * (p₂ - p₁)) * g s) := by
        rw [div_neg, ← neg_div, neg_sub]
    _ ≤ 1 / (k₂ : ℝ) * r ^ (p₂ - 1)
        * (ε ^ (-((k₁ : ℝ) * (p₂ - p₁))) / ((k₁ : ℝ) * (p₂ - p₁)) * g s) := by
        gcongr
        linarith
    _ = _ := by
        rw [hεpow, show 1 / (k₂ : ℝ) * r ^ (p₂ - 1)
            * (r ^ (-(p₂ - p₁)) * b ^ ((k₂ : ℝ) * (p₂ - p₁)) / ((k₁ : ℝ) * (p₂ - p₁)) * g s)
            = b ^ ((k₂ : ℝ) * (p₂ - p₁)) / ((k₁ : ℝ) * k₂ * (p₂ - p₁))
              * ((r ^ (p₂ - 1) * r ^ (-(p₂ - p₁))) * g s) by field_simp; try ring, hrp]

/-- **Explicit unequal-exponent bound**: for `p₁ < p₂` and `t > 0`,
`J(t) ≤ b^{k₂(p₂-p₁)}/(k₁k₂(p₂-p₁)) · M_{p₁}(g) · t^{-p₁}`. -/
theorem prodKernel_le_unequal (b p₁ p₂ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (hlt : p₁ < p₂)
    (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ s, 0 ≤ g s)
    (hM : IntegrableOn (fun s => s ^ (p₁ - 1) * g s) (Ioi 0)) (t : ℝ) (ht : 0 < t) :
    prodKernel b h₁ h₂ k₁ k₂ g t
      ≤ b ^ ((k₂ : ℝ) * (p₂ - p₁)) / ((k₁ : ℝ) * k₂ * (p₂ - p₁)) * kernelMoment p₁ g
        * t ^ (-p₁) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hp₁0 : 0 < p₁ := by rw [← hp₁]; positivity
  set R : ℝ := b ^ (k₁ + k₂) with hR
  have hR0 : 0 < R := by positivity
  set C₀ : ℝ := b ^ ((k₂ : ℝ) * (p₂ - p₁)) / ((k₁ : ℝ) * k₂ * (p₂ - p₁)) with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    have := Real.rpow_nonneg hb.le ((k₂ : ℝ) * (p₂ - p₁))
    have : 0 < p₂ - p₁ := by linarith
    positivity
  rw [prodKernel_eq_twoDAmp, twoDAmp_uOnly_eq_transferZ' 0 b t p₂ h₁ h₂ k₁ k₂ le_rfl hb ht.le hk₁
    hk₂ hp₂ (fun _ s => g s) (hg.comp continuous_snd)]
  unfold transferZ
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
  -- the dominating integrand `C₀ r^{p₁-1} g(tr)` is integrable on `(0, R]`
  obtain ⟨G₀, hG₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t * R)).exists_bound_of_continuousOn
    hg.continuousOn
  have hdom : IntegrableOn (fun r : ℝ => C₀ * (r ^ (p₁ - 1) * g (t * r))) (Ioc 0 R) := by
    have hpow : IntegrableOn (fun r : ℝ => r ^ (p₁ - 1)) (Ioc 0 R) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (by linarith)).1
    refine Integrable.mono' ((hpow.const_mul (C₀ * G₀))) ?_ ?_
    · exact (measurable_const.mul ((measurable_id.pow_const _).mul
        (hg.measurable.comp (measurable_const.mul measurable_id)))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      have hr0 : 0 < r := hr.1
      have hmem : t * r ∈ Icc (0 : ℝ) (t * R) := ⟨by positivity, by gcongr; exact hr.2⟩
      have hgle : g (t * r) ≤ G₀ := by
        have := hG₀ (t * r) hmem
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
      have hrp : 0 ≤ r ^ (p₁ - 1) := Real.rpow_nonneg hr0.le _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC₀0 (mul_nonneg hrp (hg0 _)))]
      calc C₀ * (r ^ (p₁ - 1) * g (t * r)) ≤ C₀ * (r ^ (p₁ - 1) * G₀) := by gcongr
        _ = C₀ * G₀ * r ^ (p₁ - 1) := by ring
  have hpt : ∀ r ∈ Ioc (0 : ℝ) R, genDensity p₂ b h₁ k₁ k₂ (fun _ s => g s) r (t * r)
      ≤ C₀ * (r ^ (p₁ - 1) * g (t * r)) := fun r hr =>
    genDensity_const_le b p₁ p₂ h₁ k₁ k₂ hb hk₁ hk₂ hp₁ hlt g hg0 r (t * r) hr.1 hr.2
  have hnn : ∀ r ∈ Ioc (0 : ℝ) R, 0 ≤ genDensity p₂ b h₁ k₁ k₂ (fun _ s => g s) r (t * r) := by
    intro r hr
    unfold genDensity
    beta_reduce
    have hr2 : 0 ≤ r ^ (p₂ - 1) := Real.rpow_nonneg hr.1.le _
    have hint : 0 ≤ ∫ u in Icc ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹)) b,
        u ^ ((h₁ : ℝ) - k₁ * p₂) * g (t * r) :=
      setIntegral_nonneg measurableSet_Icc fun u hu =>
        mul_nonneg (Real.rpow_nonneg (lt_of_lt_of_le
          (Real.rpow_pos_of_pos (div_pos hr.1 (by positivity)) _) hu.1).le _) (hg0 _)
    positivity
  have h1 : ∫ r in Ioc (0 : ℝ) R, genDensity p₂ b h₁ k₁ k₂ (fun _ s => g s) r (t * r)
      ≤ ∫ r in Ioc (0 : ℝ) R, C₀ * (r ^ (p₁ - 1) * g (t * r)) := by
    refine integral_mono_of_nonneg ?_ hdom ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hnn)
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hpt)
  -- substitute and extend
  have h2 : ∫ r in Ioc (0 : ℝ) R, C₀ * (r ^ (p₁ - 1) * g (t * r))
      = C₀ * (t ^ (-p₁) * ∫ x in Ioc (0 : ℝ) (t * R), x ^ (p₁ - 1) * g x) := by
    rw [integral_const_mul, integral_Ioc_rpow_mul_comp_mul_left (p₁ - 1) t R g ht hR0.le,
      show -(p₁ - 1 + 1) = -p₁ by ring]
  have h3 : ∫ x in Ioc (0 : ℝ) (t * R), x ^ (p₁ - 1) * g x ≤ kernelMoment p₁ g := by
    unfold kernelMoment
    refine setIntegral_mono_set hM ?_
      (Filter.Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (hg0 x))
  have ht' : 0 ≤ t ^ (-p₁) := Real.rpow_nonneg ht.le _
  calc ∫ r in Ioc (0 : ℝ) R, genDensity p₂ b h₁ k₁ k₂ (fun _ s => g s) r (t * r)
      ≤ C₀ * (t ^ (-p₁) * ∫ x in Ioc (0 : ℝ) (t * R), x ^ (p₁ - 1) * g x) := h1.trans (le_of_eq h2)
    _ ≤ C₀ * (t ^ (-p₁) * kernelMoment p₁ g) := by gcongr
    _ = _ := by ring

end Laplace.Grammar
