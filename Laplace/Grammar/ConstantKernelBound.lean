/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FaceMomentsEnvelope

/-!
# Quantitative bounds for the product-kernel block (grammar §4.2, mixed blocks)

For a nonnegative kernel `g`, the product-kernel block
`J(t) = ∫∫_{(0,b]²} u^{h₁} v^{h₂} g(t u^{k₁} v^{k₂}) du dv` is bounded explicitly, not just
asymptotically (Astra #5(d)): with equal exponents `p` and `R = b^{k₁+k₂}`,

  `J(t) ≤ t^{-p}/(k₁k₂) · (log t · M_p(g) + U_{p,R}(g))`,   `t ≥ 1`,

where `M_p = ∫₀^∞ s^{p-1} g` and `U_{p,R} = ∫₀^∞ s^{p-1} log₊(R/s) g`; with unequal exponents
`p₁ < p₂`, `J(t) ≤ b^{k₂(p₂-p₁)}/(k₁k₂(p₂-p₁)) · M_{p₁}(g) t^{-p₁}`; and for bounded `g`,
`J(t) ≤ ‖g‖_∞ b^{h₁+1} b^{h₂+1}/((h₁+1)(h₂+1))` for every `t`. These replace the `IsBigO` bounds
of the mixed remainder by explicit constants, as needed to feed the strict-gap parameter wrapper.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- The product-kernel block `J(t) = ∫∫ u^{h₁} v^{h₂} g(t u^{k₁} v^{k₂})`. -/
noncomputable def prodKernel (b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, u ^ h₁ * ∫ v in Ioc (0 : ℝ) b, v ^ h₂ * g (t * (u ^ k₁ * v ^ k₂))

theorem prodKernel_eq_twoDAmp (b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (g : ℝ → ℝ) (t : ℝ) :
    prodKernel b h₁ h₂ k₁ k₂ g t = twoDAmp 0 b t h₁ h₂ k₁ k₂ (fun _ _ s => g s) := by
  unfold prodKernel twoDAmp
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]

/-- The moment `M_α(g) = ∫₀^∞ s^{α-1} g(s) ds`. -/
noncomputable def kernelMoment (α : ℝ) (g : ℝ → ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), s ^ (α - 1) * g s

/-- The log-plus moment `U_{α,R}(g) = ∫₀^∞ s^{α-1} log₊(R/s) g(s) ds`. -/
noncomputable def kernelLogMoment (α R : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (α - 1) * logPlus (R / s) * g s

/-- `∫_ε^b u⁻¹ du = log b − log ε` for `0 < ε ≤ b`. -/
theorem integral_inv_Icc (ε b : ℝ) (hε : 0 < ε) (hεb : ε ≤ b) :
    ∫ u in Icc ε b, u⁻¹ = Real.log b - Real.log ε := by
  have hb : 0 < b := lt_of_lt_of_le hε hεb
  have h0 : (0 : ℝ) ∉ uIcc ε b := by
    rw [uIcc_of_le hεb]
    intro h
    exact absurd h.1 (not_le.2 hε)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hεb, integral_inv h0,
    Real.log_div hb.ne' hε.ne']

/-- The logarithmic factor of the equal-exponent density:
`log b − log((r/b^{k₂})^{1/k₁}) = k₁⁻¹ (log R − log r)`, `R = b^{k₁+k₂}`. -/
theorem log_density_factor (b r : ℝ) (k₁ k₂ : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁) (hr : 0 < r) :
    Real.log b - Real.log ((r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹))
      = 1 / (k₁ : ℝ) * (Real.log (b ^ (k₁ + k₂)) - Real.log r) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hbk : 0 < b ^ k₂ := by positivity
  rw [Real.log_rpow (div_pos hr hbk), Real.log_div hr.ne' hbk.ne', Real.log_pow, Real.log_pow]
  push_cast
  field_simp
  ring

/-- **The equal-exponent product-kernel density**: for continuous `g` and `t ≥ 0`,
`J(t) = (k₁k₂)⁻¹ ∫₀^R r^{p-1} (log R − log r) g(t r) dr`. -/
theorem prodKernel_eq_density (b p : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (g : ℝ → ℝ) (hg : Continuous g) (t : ℝ) (ht : 0 ≤ t) :
    prodKernel b h₁ h₂ k₁ k₂ g t
      = ∫ r in Ioc (0 : ℝ) (b ^ (k₁ + k₂)),
          1 / ((k₁ : ℝ) * k₂) * r ^ (p - 1) * (Real.log (b ^ (k₁ + k₂)) - Real.log r)
            * g (t * r) := by
  rw [prodKernel_eq_twoDAmp, twoDAmp_uOnly_eq_transferZ 0 b t p h₁ h₂ k₁ k₂ le_rfl hb ht hk₁ hk₂
    hp₁ hp₂ (fun _ s => g s) (hg.comp continuous_snd)]
  unfold transferZ uDensity
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hbk : 0 < b ^ k₂ := by positivity
  have hε : 0 < (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) := Real.rpow_pos_of_pos (div_pos hr.1 hbk) _
  have hεb : (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) ≤ b := by
    have : (r / b ^ k₂) ^ ((k₁ : ℝ)⁻¹) ≤ (b ^ k₁) ^ ((k₁ : ℝ)⁻¹) := by
      refine Real.rpow_le_rpow (div_pos hr.1 hbk).le ?_ (by positivity)
      rw [div_le_iff₀ hbk, ← pow_add]; exact hr.2
    rwa [Real.pow_rpow_inv_natCast hb.le hk₁.ne'] at this
  beta_reduce
  rw [integral_mul_const, integral_inv_Icc _ b hε hεb, log_density_factor b r k₁ k₂ hb hk₁ hr.1]
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
  ring

/-- **Explicit equal-exponent bound**: for `t ≥ 1`,
`J(t) ≤ t^{-p}/(k₁k₂) (log t · M_p(g) + U_{p,R}(g))`. -/
theorem prodKernel_le_equal (b p : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hb : 0 < b) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ s, 0 ≤ g s)
    (hM : IntegrableOn (fun s => s ^ (p - 1) * g s) (Ioi 0))
    (hU : IntegrableOn (fun s => s ^ (p - 1) * logPlus (b ^ (k₁ + k₂) / s) * g s) (Ioi 0))
    (t : ℝ) (ht : 1 ≤ t) :
    prodKernel b h₁ h₂ k₁ k₂ g t
      ≤ t ^ (-p) / ((k₁ : ℝ) * k₂)
        * (Real.log t * kernelMoment p g + kernelLogMoment p (b ^ (k₁ + k₂)) g) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have ht0 : 0 < t := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hp0 : 0 < p := by rw [← hp₁]; positivity
  set R : ℝ := b ^ (k₁ + k₂) with hR
  have hR0 : 0 < R := by positivity
  rw [prodKernel_eq_density b p h₁ h₂ k₁ k₂ hb hk₁ hk₂ hp₁ hp₂ g hg t ht0.le]
  -- substitute `x = t r`
  set G : ℝ → ℝ := fun x => (Real.log t + Real.log R - Real.log x) * g x with hG
  have hpt : ∀ r ∈ Ioc (0 : ℝ) R,
      1 / ((k₁ : ℝ) * k₂) * r ^ (p - 1) * (Real.log R - Real.log r) * g (t * r)
        = 1 / ((k₁ : ℝ) * k₂) * (r ^ (p - 1) * G (t * r)) := by
    intro r hr
    simp only [hG]
    rw [Real.log_mul ht0.ne' hr.1.ne']
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_const_mul,
    integral_Ioc_rpow_mul_comp_mul_left (p - 1) t R G ht0 hR0.le,
    show -(p - 1 + 1) = -p by ring]
  -- the dominating integrand
  set F : ℝ → ℝ := fun x => x ^ (p - 1) * ((Real.log t + logPlus (R / x)) * g x) with hF
  have hFint : IntegrableOn F (Ioi 0) := by
    have h1 : IntegrableOn (fun x => Real.log t * (x ^ (p - 1) * g x)) (Ioi 0) := hM.const_mul _
    have h2 : IntegrableOn (fun x => Real.log t * (x ^ (p - 1) * g x)
        + x ^ (p - 1) * logPlus (R / x) * g x) (Ioi 0) := h1.add hU
    refine h2.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [hF]; ring
  have hF0 : ∀ x, 0 < x → 0 ≤ F x := fun x hx => by
    simp only [hF]
    have := logPlus_nonneg (R / x)
    have := hg0 x
    have := Real.rpow_nonneg hx.le (p - 1)
    positivity
  have hFint' : IntegrableOn F (Ioc 0 (t * R)) := hFint.mono_set Ioc_subset_Ioi_self
  have hGle : ∀ x ∈ Ioc (0 : ℝ) (t * R), x ^ (p - 1) * G x ≤ F x := by
    intro x hx
    simp only [hG, hF]
    have hx0 : 0 < x := hx.1
    have hlog : Real.log R - Real.log x ≤ logPlus (R / x) := by
      rw [← Real.log_div hR0.ne' hx0.ne']
      exact log_le_logPlus _
    have := Real.rpow_nonneg hx0.le (p - 1)
    have := hg0 x
    have : x ^ (p - 1) * ((Real.log t + Real.log R - Real.log x) * g x)
        ≤ x ^ (p - 1) * ((Real.log t + logPlus (R / x)) * g x) := by
      gcongr
      linarith
    linarith
  have hGint : IntegrableOn (fun x => x ^ (p - 1) * G x) (Ioc 0 (t * R)) := by
    refine Integrable.mono' hFint' ?_ ?_
    · exact ((measurable_id.pow_const _).mul (((measurable_const.add measurable_const).sub
        Real.measurable_log).mul hg.measurable)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hGle x hx
      · simp only [hG]
        have hx0 : 0 < x := hx.1
        have hlow : -Real.log t ≤ Real.log R - Real.log x := by
          have h1 : Real.log x ≤ Real.log (t * R) := Real.log_le_log hx0 hx.2
          rw [Real.log_mul ht0.ne' hR0.ne'] at h1
          linarith
        have := Real.rpow_nonneg hx0.le (p - 1)
        have := hg0 x
        exact mul_nonneg (by assumption) (mul_nonneg (by linarith) (by assumption))
  have h1 : ∫ x in Ioc (0 : ℝ) (t * R), x ^ (p - 1) * G x ≤ ∫ x in Ioc (0 : ℝ) (t * R), F x :=
    setIntegral_mono_on hGint hFint' measurableSet_Ioc hGle
  have h2 : ∫ x in Ioc (0 : ℝ) (t * R), F x ≤ ∫ x in Ioi (0 : ℝ), F x :=
    setIntegral_mono_set hFint ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun x hx => hF0 x hx)) (Filter.Eventually.of_forall
        fun x hx => Ioc_subset_Ioi_self hx)
  have h3 : ∫ x in Ioi (0 : ℝ), F x
      = Real.log t * kernelMoment p g + kernelLogMoment p R g := by
    unfold kernelMoment kernelLogMoment
    rw [← integral_const_mul]
    have hint1 : IntegrableOn (fun x => Real.log t * (x ^ (p - 1) * g x)) (Ioi 0) := hM.const_mul _
    rw [← integral_add hint1 hU]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [hF]; ring
  have hpos : 0 ≤ 1 / ((k₁ : ℝ) * k₂) * t ^ (-p) := by positivity
  calc 1 / ((k₁ : ℝ) * k₂) * (t ^ (-p) * ∫ x in Ioc (0 : ℝ) (t * R), x ^ (p - 1) * G x)
      ≤ 1 / ((k₁ : ℝ) * k₂) * (t ^ (-p) * ∫ x in Ioi (0 : ℝ), F x) := by
        gcongr
        exact h1.trans h2
    _ = _ := by rw [h3]; ring

/-- **The bounded-kernel bound**: if `0 ≤ g ≤ G₀`, then for every `t`,
`J(t) ≤ G₀ b^{h₁+1} b^{h₂+1} / ((h₁+1)(h₂+1))`. -/
theorem prodKernel_le_of_bounded (b G₀ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hb : 0 < b) (g : ℝ → ℝ)
    (hg : Continuous g) (hgG : ∀ s, g s ≤ G₀) (t : ℝ) :
    prodKernel b h₁ h₂ k₁ k₂ g t
      ≤ G₀ * (b ^ (h₁ + 1) / ((h₁ : ℝ) + 1)) * (b ^ (h₂ + 1) / ((h₂ : ℝ) + 1)) := by
  have hpow : ∀ (h : ℕ), ∫ v in Ioc (0 : ℝ) b, v ^ h = b ^ (h + 1) / ((h : ℝ) + 1) := by
    intro h
    rw [← intervalIntegral.integral_of_le hb.le, integral_pow, zero_pow (Nat.succ_ne_zero h),
      sub_zero]
  have hΦ : Continuous fun x : ℝ × ℝ × ℝ => (fun _ _ s => g s : ℝ → ℝ → ℝ → ℝ) x.1 x.2.1 x.2.2 :=
    hg.comp (continuous_snd.comp continuous_snd)
  rw [prodKernel_eq_twoDAmp, twoDAmp_eq_prod 0 b t h₁ h₂ k₁ k₂ (fun _ _ s => g s) hΦ]
  have hW : Integrable (fun z : ℝ × ℝ => G₀ * (z.1 ^ h₁ * z.2 ^ h₂)) (boxMeasure₂ b) := by
    unfold boxMeasure₂
    rw [Measure.prod_restrict]
    exact ((continuous_const.mul ((continuous_fst.pow h₁).mul
      (continuous_snd.pow h₂))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hI := twoDIntegrand_integrable 0 b t h₁ h₂ k₁ k₂ (fun _ _ s => g s) hΦ
  have hmem : ∀ᵐ z ∂(boxMeasure₂ b), z ∈ Ioc (0 : ℝ) b ×ˢ Ioc (0 : ℝ) b := by
    unfold boxMeasure₂
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  calc ∫ z, twoDIntegrand 0 t h₁ h₂ k₁ k₂ (fun _ _ s => g s) z ∂(boxMeasure₂ b)
      ≤ ∫ z, G₀ * (z.1 ^ h₁ * z.2 ^ h₂) ∂(boxMeasure₂ b) := by
        refine integral_mono_ae hI hW ?_
        filter_upwards [hmem] with z hz
        simp only [twoDIntegrand, neg_zero, zero_mul, Real.exp_zero, one_mul]
        have h1 : 0 ≤ z.1 ^ h₁ := pow_nonneg hz.1.1.le _
        have h2 : 0 ≤ z.2 ^ h₂ := pow_nonneg hz.2.1.le _
        calc z.1 ^ h₁ * (z.2 ^ h₂ * g (t * (z.1 ^ k₁ * z.2 ^ k₂)))
            ≤ z.1 ^ h₁ * (z.2 ^ h₂ * G₀) := by gcongr; exact hgG _
          _ = G₀ * (z.1 ^ h₁ * z.2 ^ h₂) := by ring
    _ = _ := by
        rw [integral_const_mul]
        unfold boxMeasure₂
        rw [integral_prod_mul (f := fun u : ℝ => u ^ h₁) (g := fun v : ℝ => v ^ h₂), hpow h₁,
          hpow h₂]
        ring

end Laplace.Grammar
