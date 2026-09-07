/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TaylorTreeGeneral
import Laplace.Grammar.ConstantKernelBound
import Laplace.Grammar.ConstantKernelUnequal
import Laplace.Grammar.MixedShiftBound
import Laplace.Grammar.TwoDGeneralSwap

/-!
# Explicit constants for the mixed remainder (grammar §4.2, Astra #9 R5, step 1)

The mixed-remainder estimate `twoDAmp_env_isBigO` was the only genuinely asymptotic step of the
`d = 2` cutoff theorem. Here it is made explicit: `twoDGeneral β a b (N²) h₁ h₂ k₁ k₂` is the
product kernel of the Gaussian kernel `g(s) = e^{−βs² + βas}` (`twoDGeneral_sq_eq_prodKernel`), so
the explicit product-kernel bounds of units 111–112 give, for `N ≥ 1`,

  `twoDGeneral β a b (N²) h₁ h₂ k₁ k₂ ≤ mixConst β a b h₁ h₂ k₁ k₂ · N^{−min(p₁,p₂)} (1 + log N)`

(`twoDGeneral_sq_le`) with `mixConst` a finite expression in the Gaussian moments
`kernelMoment p g = ∫₀^∞ s^{p−1} g` and `kernelLogMoment p R g = ∫₀^∞ s^{p−1} log₊(R/s) g`
(equal case) or the single moment at the smaller exponent (unequal case). Consequently
`|twoDAmp β b N h₁ h₂ k₁ k₂ Φ| ≤ C e^{D²/β} mixConst(β/2, 2L, b, h+M, k) N^{−E'} (1 + log N)`
for an amplitude with the rectangular envelope (`twoDAmp_env_explicit`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- `twoDGeneral` at `N²` is the product kernel of the Gaussian kernel. -/
theorem twoDGeneral_sq_eq_prodKernel (β a b N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hN : 0 ≤ N) :
    twoDGeneral β a b (N ^ 2) h₁ h₂ k₁ k₂ = prodKernel b h₁ h₂ k₁ k₂ (quadKernel β a) N := by
  unfold twoDGeneral prodKernel quadKernel
  rw [Real.sqrt_sq hN]
  congr 1
  funext u
  rw [← integral_const_mul]
  congr 1
  funext v
  rw [mul_assoc, show -β * N ^ 2 * (u ^ k₁ * v ^ k₂) ^ 2 + β * N * (u ^ k₁ * v ^ k₂) * a
    = -β * (N * (u ^ k₁ * v ^ k₂)) ^ 2 + β * a * (N * (u ^ k₁ * v ^ k₂)) by ring]

theorem quadKernel_eq_mul (β a s : ℝ) :
    quadKernel β a s = Real.exp (-β * s ^ 2) * Real.exp (β * s * a) := by
  unfold quadKernel
  rw [← Real.exp_add]
  congr 1
  ring

/-- Integrability of `s^{p−1} g(s)` for the Gaussian kernel, `p > 0`. -/
theorem quadKernel_moment_integrableOn (β a p : ℝ) (hβ : 0 < β) (hp : 0 < p) :
    IntegrableOn (fun s => s ^ (p - 1) * quadKernel β a s) (Ioi 0) := by
  have h := moment_integrableOn_of_envelope β a (p - 1) 1 hβ (by linarith) 0 0
    (fun s => Real.exp (β * s * a)) (by fun_prop)
    (fun s _ => by rw [abs_of_pos (Real.exp_pos _)]; simp)
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [pow_zero, mul_one, abs_of_pos (Real.exp_pos _)]
  rw [quadKernel_eq_mul]

/-- `log₊(R/s) ≤ (1 + |log R|)(1 + |log s|)` for `R, s > 0`. -/
theorem logPlus_div_le (R s : ℝ) (hR : 0 < R) (hs : 0 < s) :
    logPlus (R / s) ≤ (1 + |Real.log R|) * (1 + |Real.log s|) := by
  unfold logPlus
  rw [Real.log_div hR.ne' hs.ne']
  refine (max_le (by positivity) (le_abs_self _)).trans ?_
  refine (abs_sub _ _).trans ?_
  nlinarith [abs_nonneg (Real.log R), abs_nonneg (Real.log s)]

/-- Integrability of `s^{p−1} log₊(R/s) g(s)` for the Gaussian kernel. -/
theorem quadKernel_logMoment_integrableOn (β a p R : ℝ) (hβ : 0 < β) (hp : 0 < p) (hR : 0 < R) :
    IntegrableOn (fun s => s ^ (p - 1) * logPlus (R / s) * quadKernel β a s) (Ioi 0) := by
  have h := moment_integrableOn_of_envelope β a (p - 1) 1 hβ (by linarith) 1 0
    (fun s => Real.exp (β * s * a)) (by fun_prop)
    (fun s _ => by rw [abs_of_pos (Real.exp_pos _)]; simp)
  refine Integrable.mono' (h.const_mul (1 + |Real.log R|)) ?_ ?_
  · have hm : Measurable fun s : ℝ => s ^ (p - 1) * logPlus (R / s) * quadKernel β a s := by
      unfold logPlus
      exact ((measurable_id.pow_const _).mul
        (measurable_const.max (Real.measurable_log.comp (measurable_const.div measurable_id)))).mul
        (quadKernel_continuous β a).measurable
    exact hm.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := hs
    have hg := quadKernel_pos β a s
    have hsp : 0 ≤ s ^ (p - 1) := Real.rpow_nonneg hs0.le _
    have hlp := logPlus_nonneg (R / s)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_one, abs_of_pos (Real.exp_pos _),
      ← quadKernel_eq_mul]
    have hb := logPlus_div_le R s hR hs0
    calc s ^ (p - 1) * logPlus (R / s) * quadKernel β a s
        ≤ s ^ (p - 1) * ((1 + |Real.log R|) * (1 + |Real.log s|)) * quadKernel β a s := by
          gcongr
      _ = (1 + |Real.log R|) * (s ^ (p - 1) * (1 + |Real.log s|) * quadKernel β a s) := by ring

theorem kernelMoment_nonneg (α : ℝ) (g : ℝ → ℝ) (hg : ∀ s, 0 ≤ g s) : 0 ≤ kernelMoment α g :=
  setIntegral_nonneg measurableSet_Ioi fun s hs =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (hg s)

theorem kernelLogMoment_nonneg (α R : ℝ) (g : ℝ → ℝ) (hg : ∀ s, 0 ≤ g s) :
    0 ≤ kernelLogMoment α R g :=
  setIntegral_nonneg measurableSet_Ioi fun s hs =>
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (logPlus_nonneg _)) (hg s)

/-- The explicit mixed constant: Gaussian moments of `g = quadKernel β a`, by case on the
starting exponents. -/
noncomputable def mixConst (β a b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) : ℝ :=
  if ((h₁ : ℝ) + 1) / k₁ = ((h₂ : ℝ) + 1) / k₂ then
    (kernelMoment (((h₁ : ℝ) + 1) / k₁) (quadKernel β a)
      + kernelLogMoment (((h₁ : ℝ) + 1) / k₁) (b ^ (k₁ + k₂)) (quadKernel β a)) / ((k₁ : ℝ) * k₂)
  else if ((h₁ : ℝ) + 1) / k₁ < ((h₂ : ℝ) + 1) / k₂ then
    b ^ ((k₂ : ℝ) * (((h₂ : ℝ) + 1) / k₂ - ((h₁ : ℝ) + 1) / k₁))
      / ((k₁ : ℝ) * k₂ * (((h₂ : ℝ) + 1) / k₂ - ((h₁ : ℝ) + 1) / k₁))
      * kernelMoment (((h₁ : ℝ) + 1) / k₁) (quadKernel β a)
  else
    b ^ ((k₁ : ℝ) * (((h₁ : ℝ) + 1) / k₁ - ((h₂ : ℝ) + 1) / k₂))
      / ((k₂ : ℝ) * k₁ * (((h₁ : ℝ) + 1) / k₁ - ((h₂ : ℝ) + 1) / k₂))
      * kernelMoment (((h₂ : ℝ) + 1) / k₂) (quadKernel β a)

/-- **Explicit bound for `twoDGeneral` at `N²`**, `N ≥ 1`. -/
theorem twoDGeneral_sq_le (β a b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (N : ℝ) (hN : 1 ≤ N) :
    twoDGeneral β a b (N ^ 2) h₁ h₂ k₁ k₂
      ≤ mixConst β a b h₁ h₂ k₁ k₂
        * N ^ (-min (((h₁ : ℝ) + 1) / k₁) (((h₂ : ℝ) + 1) / k₂)) * (1 + Real.log N) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  set p₁ : ℝ := ((h₁ : ℝ) + 1) / k₁ with hp₁
  set p₂ : ℝ := ((h₂ : ℝ) + 1) / k₂ with hp₂
  have hp₁0 : 0 < p₁ := by positivity
  have hp₂0 : 0 < p₂ := by positivity
  set g := quadKernel β a with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s => (quadKernel_pos β a s).le
  have hgc : Continuous g := quadKernel_continuous β a
  have hM₁ := quadKernel_moment_integrableOn β a p₁ hβ hp₁0
  have hM₂ := quadKernel_moment_integrableOn β a p₂ hβ hp₂0
  have hbR : 0 < b ^ (k₁ + k₂) := by positivity
  rw [twoDGeneral_sq_eq_prodKernel β a b N h₁ h₂ k₁ k₂ hN0.le]
  unfold mixConst
  rcases lt_trichotomy p₁ p₂ with hlt | heq | hgt
  · rw [if_neg hlt.ne, if_pos hlt, min_eq_left hlt.le]
    have h := prodKernel_le_unequal b p₁ p₂ h₁ h₂ k₁ k₂ hb hk₁ hk₂ rfl rfl hlt g hgc hg0 hM₁ N hN0
    have hc0 : 0 ≤ b ^ ((k₂ : ℝ) * (p₂ - p₁)) / ((k₁ : ℝ) * k₂ * (p₂ - p₁))
        * kernelMoment p₁ g := by
      have : 0 < p₂ - p₁ := by linarith
      exact mul_nonneg (by positivity) (kernelMoment_nonneg p₁ g hg0)
    calc prodKernel b h₁ h₂ k₁ k₂ g N
        ≤ b ^ ((k₂ : ℝ) * (p₂ - p₁)) / ((k₁ : ℝ) * k₂ * (p₂ - p₁)) * kernelMoment p₁ g
          * N ^ (-p₁) := h
      _ ≤ b ^ ((k₂ : ℝ) * (p₂ - p₁)) / ((k₁ : ℝ) * k₂ * (p₂ - p₁)) * kernelMoment p₁ g
          * N ^ (-p₁) * (1 + Real.log N) := by
          refine le_mul_of_one_le_right (mul_nonneg hc0 (Real.rpow_nonneg hN0.le _)) ?_
          linarith
  · rw [if_pos heq, min_eq_left heq.le]
    have hU := quadKernel_logMoment_integrableOn β a p₁ (b ^ (k₁ + k₂)) hβ hp₁0 hbR
    have h := prodKernel_le_equal b p₁ h₁ h₂ k₁ k₂ hb hk₁ hk₂ rfl heq.symm g hgc hg0 hM₁ hU N hN
    have hM0 := kernelMoment_nonneg p₁ g hg0
    have hU0 := kernelLogMoment_nonneg p₁ (b ^ (k₁ + k₂)) g hg0
    have hNp : 0 ≤ N ^ (-p₁) := Real.rpow_nonneg hN0.le _
    calc prodKernel b h₁ h₂ k₁ k₂ g N
        ≤ N ^ (-p₁) / ((k₁ : ℝ) * k₂)
          * (Real.log N * kernelMoment p₁ g + kernelLogMoment p₁ (b ^ (k₁ + k₂)) g) := h
      _ ≤ N ^ (-p₁) / ((k₁ : ℝ) * k₂)
          * ((kernelMoment p₁ g + kernelLogMoment p₁ (b ^ (k₁ + k₂)) g) * (1 + Real.log N)) := by
          gcongr
          nlinarith
      _ = (kernelMoment p₁ g + kernelLogMoment p₁ (b ^ (k₁ + k₂)) g) / ((k₁ : ℝ) * k₂)
          * N ^ (-p₁) * (1 + Real.log N) := by ring
  · rw [if_neg hgt.ne', if_neg (not_lt.2 hgt.le), min_eq_right hgt.le]
    rw [← twoDGeneral_sq_eq_prodKernel β a b N h₁ h₂ k₁ k₂ hN0.le, twoDGeneral_swap,
      twoDGeneral_sq_eq_prodKernel β a b N h₂ h₁ k₂ k₁ hN0.le]
    have h := prodKernel_le_unequal b p₂ p₁ h₂ h₁ k₂ k₁ hb hk₂ hk₁ rfl rfl hgt g hgc hg0 hM₂ N hN0
    have hc0 : 0 ≤ b ^ ((k₁ : ℝ) * (p₁ - p₂)) / ((k₂ : ℝ) * k₁ * (p₁ - p₂))
        * kernelMoment p₂ g := by
      have : 0 < p₁ - p₂ := by linarith
      exact mul_nonneg (by positivity) (kernelMoment_nonneg p₂ g hg0)
    calc prodKernel b h₂ h₁ k₂ k₁ g N
        ≤ b ^ ((k₁ : ℝ) * (p₁ - p₂)) / ((k₂ : ℝ) * k₁ * (p₁ - p₂)) * kernelMoment p₂ g
          * N ^ (-p₂) := h
      _ ≤ b ^ ((k₁ : ℝ) * (p₁ - p₂)) / ((k₂ : ℝ) * k₁ * (p₁ - p₂)) * kernelMoment p₂ g
          * N ^ (-p₂) * (1 + Real.log N) := by
          refine le_mul_of_one_le_right (mul_nonneg hc0 (Real.rpow_nonneg hN0.le _)) ?_
          linarith

/-- **Explicit mixed-remainder bound**: for an amplitude with the rectangular envelope and `N ≥ 1`,
`|twoDAmp Φ| ≤ C e^{D²/β} · mixConst(β/2, 2L, b, h₁+M₁, h₂+M₂, k) · N^{−E'} (1 + log N)`. -/
theorem twoDAmp_env_explicit (β b L C N : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (hβ : 0 < β) (hb : 0 < b) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hC : 0 ≤ C) (hN : 1 ≤ N)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2)
    (hbound : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |Φ u v s| ≤ C * (u ^ M₁ * v ^ M₂) * ((1 + s) ^ D * Real.exp (β * s * L))) :
    |twoDAmp β b N h₁ h₂ k₁ k₂ Φ|
      ≤ C * Real.exp ((D : ℝ) ^ 2 / β) * mixConst (β / 2) (2 * L) b (h₁ + M₁) (h₂ + M₂) k₁ k₂
        * N ^ (-min ((((h₁ + M₁ : ℕ) : ℝ) + 1) / k₁) ((((h₂ + M₂ : ℕ) : ℝ) + 1) / k₂))
        * (1 + Real.log N) := by
  have h1 := twoDAmp_env_le β b L C N h₁ h₂ k₁ k₂ M₁ M₂ D Φ hβ (by linarith) hC hΦ hbound
  have h2 := twoDGeneral_sq_le (β / 2) (2 * L) b (h₁ + M₁) (h₂ + M₂) k₁ k₂ (by linarith) hb hk₁
    hk₂ N hN
  have hc0 : 0 ≤ C * Real.exp ((D : ℝ) ^ 2 / β) := by positivity
  calc |twoDAmp β b N h₁ h₂ k₁ k₂ Φ|
      ≤ C * Real.exp ((D : ℝ) ^ 2 / β)
        * twoDGeneral (β / 2) (2 * L) b (N ^ 2) (h₁ + M₁) (h₂ + M₂) k₁ k₂ := h1
    _ ≤ C * Real.exp ((D : ℝ) ^ 2 / β)
        * (mixConst (β / 2) (2 * L) b (h₁ + M₁) (h₂ + M₂) k₁ k₂
          * N ^ (-min ((((h₁ + M₁ : ℕ) : ℝ) + 1) / k₁) ((((h₂ + M₂ : ℕ) : ℝ) + 1) / k₂))
          * (1 + Real.log N)) := mul_le_mul_of_nonneg_left h2 hc0
    _ = _ := by ring

end Laplace.Grammar
