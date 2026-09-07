/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FaceDensityExpansion

/-!
# The mixed remainder with arbitrary shifts (grammar §4.2, higher-order `d = 2`)

The mixed term of the anchored decomposition (unit 88) was bounded by the constant-kernel block
with both exponents shifted by one. Here the bound is generalised to an amplitude dominated by
`C u^{M₁} v^{M₂} (1+s)^D e^{βsL}`: the block integral is at most a constant times
`twoDGeneral (β/2) (2L) b N² (h₁+M₁) (h₂+M₂) k₁ k₂` (`twoDAmp_env_le`), which is
`O(N^{-min((h₁+M₁+1)/k₁, (h₂+M₂+1)/k₂)} (1 + log N))` (`twoDGeneral_shift_isBigO`,
`twoDAmp_env_isBigO`). This is the remainder estimate of the rectangular face-jet decomposition:
with `M₁/k₁, M₂/k₂ > τ` the mixed remainder is `O(N^{-(p+τ)}(1+log N))`. The polynomial envelope
is absorbed by `(1+s)^D ≤ e^{D²/β} e^{βs²/2}` (`one_add_pow_le_exp`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- `(1+s)^D ≤ e^{D²/β} e^{βs²/2}` for `s ≥ 0`. -/
theorem one_add_pow_le_exp (β s : ℝ) (D : ℕ) (hβ : 0 < β) (hs : 0 ≤ s) :
    (1 + s) ^ D ≤ Real.exp ((D : ℝ) ^ 2 / β) * Real.exp (β / 2 * s ^ 2) := by
  have h1 : (1 + s) ^ D ≤ Real.exp ((D : ℝ) * s) := by
    calc (1 + s) ^ D ≤ (Real.exp s) ^ D :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp s]) D
      _ = Real.exp ((D : ℝ) * s) := by rw [← Real.exp_nat_mul]
  have h2 : (D : ℝ) * s ≤ (D : ℝ) ^ 2 / β + β / 2 * s ^ 2 := by
    have hsq : 0 ≤ (β * s / 2 - D) ^ 2 := sq_nonneg _
    have : (D : ℝ) * s * β ≤ (D : ℝ) ^ 2 + β ^ 2 * s ^ 2 / 2 := by nlinarith
    rw [← sub_nonneg]
    have : (D : ℝ) ^ 2 / β + β / 2 * s ^ 2 - (D : ℝ) * s
        = ((D : ℝ) ^ 2 + β ^ 2 * s ^ 2 / 2 - (D : ℝ) * s * β) / β := by field_simp
    rw [this]
    exact div_nonneg (by linarith) hβ.le
  calc (1 + s) ^ D ≤ Real.exp ((D : ℝ) * s) := h1
    _ ≤ Real.exp ((D : ℝ) ^ 2 / β + β / 2 * s ^ 2) := Real.exp_le_exp.2 h2
    _ = _ := Real.exp_add _ _

/-- **The shifted constant-kernel bound**: an amplitude dominated by
`C u^{M₁} v^{M₂} (1+s)^D e^{βsL}` has block integral at most
`C e^{D²/β} · twoDGeneral (β/2) (2L) b N² (h₁+M₁) (h₂+M₂) k₁ k₂`. -/
theorem twoDAmp_env_le (β b L C N : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (hβ : 0 < β) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2)
    (hbound : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |Φ u v s| ≤ C * (u ^ M₁ * v ^ M₂) * ((1 + s) ^ D * Real.exp (β * s * L))) :
    |twoDAmp β b N h₁ h₂ k₁ k₂ Φ|
      ≤ C * Real.exp ((D : ℝ) ^ 2 / β)
        * twoDGeneral (β / 2) (2 * L) b (N ^ 2) (h₁ + M₁) (h₂ + M₂) k₁ k₂ := by
  set W : ℝ × ℝ → ℝ := fun z => z.1 ^ (h₁ + M₁) * z.2 ^ (h₂ + M₂)
    * Real.exp (-(β / 2) * N ^ 2 * (z.1 ^ k₁ * z.2 ^ k₂) ^ 2
      + β / 2 * Real.sqrt (N ^ 2) * (z.1 ^ k₁ * z.2 ^ k₂) * (2 * L)) with hW
  have hWc : Continuous W := by simp only [hW]; fun_prop
  have hWi : Integrable W (boxMeasure₂ b) := by
    unfold boxMeasure₂
    rw [Measure.prod_restrict]
    exact (hWc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hWeq : twoDGeneral (β / 2) (2 * L) b (N ^ 2) (h₁ + M₁) (h₂ + M₂) k₁ k₂
      = ∫ z, W z ∂(boxMeasure₂ b) := by
    unfold twoDGeneral boxMeasure₂
    rw [integral_prod _ (by unfold boxMeasure₂ at hWi; exact hWi)]
  have hsqrt : Real.sqrt (N ^ 2) = N := Real.sqrt_sq hN
  have hmem : ∀ᵐ z ∂(boxMeasure₂ b), z ∈ Ioc (0 : ℝ) b ×ˢ Ioc (0 : ℝ) b := by
    unfold boxMeasure₂
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hK : 0 ≤ Real.exp ((D : ℝ) ^ 2 / β) := (Real.exp_pos _).le
  have hpt : ∀ᵐ z ∂(boxMeasure₂ b), ‖twoDIntegrand β N h₁ h₂ k₁ k₂ Φ z‖
      ≤ C * Real.exp ((D : ℝ) ^ 2 / β) * W z := by
    filter_upwards [hmem] with z hz
    obtain ⟨hu, hv⟩ := hz
    set u := z.1 with hu_def
    set v := z.2 with hv_def
    have hu0 : 0 < u := hu.1
    have hv0 : 0 < v := hv.1
    set s : ℝ := N * (u ^ k₁ * v ^ k₂) with hs
    have hs0 : 0 ≤ s := by positivity
    have hm := hbound u ⟨hu.1.le, hu.2⟩ v ⟨hv.1.le, hv.2⟩ s hs0
    have hE := one_add_pow_le_exp β s D hβ hs0
    simp only [twoDIntegrand, hW]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hu.1.le _),
      abs_of_nonneg (pow_nonneg hv.1.le _), abs_of_pos (Real.exp_pos _), hsqrt, ← hs]
    have hker : Real.exp (-(β / 2) * N ^ 2 * (u ^ k₁ * v ^ k₂) ^ 2
          + β / 2 * N * (u ^ k₁ * v ^ k₂) * (2 * L))
        = Real.exp (-β * s ^ 2) * (Real.exp (β / 2 * s ^ 2) * Real.exp (β * s * L)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hs]; ring
    rw [hker]
    have huv : 0 ≤ u ^ M₁ * v ^ M₂ := by positivity
    calc u ^ h₁ * (v ^ h₂ * (Real.exp (-β * s ^ 2) * |Φ u v s|))
        ≤ u ^ h₁ * (v ^ h₂ * (Real.exp (-β * s ^ 2)
            * (C * (u ^ M₁ * v ^ M₂) * ((1 + s) ^ D * Real.exp (β * s * L))))) := by
          gcongr
      _ ≤ u ^ h₁ * (v ^ h₂ * (Real.exp (-β * s ^ 2)
            * (C * (u ^ M₁ * v ^ M₂)
              * (Real.exp ((D : ℝ) ^ 2 / β) * Real.exp (β / 2 * s ^ 2)
                * Real.exp (β * s * L))))) := by
          gcongr
      _ = C * Real.exp ((D : ℝ) ^ 2 / β) * (u ^ (h₁ + M₁) * v ^ (h₂ + M₂)
            * (Real.exp (-β * s ^ 2) * (Real.exp (β / 2 * s ^ 2) * Real.exp (β * s * L)))) := by
          rw [pow_add, pow_add]; ring
  rw [twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ Φ hΦ, hWeq, ← Real.norm_eq_abs, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hWi.const_mul _) hpt

/-- The constant-kernel block at `n = N²` is `O(N^{-min(p₁,p₂)} (1 + log N))`. -/
theorem twoDGeneral_shift_isBigO (β a b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    (fun N : ℝ => twoDGeneral β a b (N ^ 2) h₁ h₂ k₁ k₂) =O[atTop]
      fun N : ℝ => N ^ (-min (((h₁ : ℝ) + 1) / k₁) (((h₂ : ℝ) + 1) / k₂)) * (1 + Real.log N) := by
  set m : ℝ := min (((h₁ : ℝ) + 1) / k₁) (((h₂ : ℝ) + 1) / k₂) with hm
  have h := twoDGeneral_isBigO_min β a b h₁ h₂ k₁ k₂ hβ hb hk₁ hk₂
  have hsq : Tendsto (fun N : ℝ => N ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hcomp := h.comp_tendsto hsq
  refine hcomp.trans (IsBigO.of_bound 2 ?_)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  simp only [Function.comp]
  rw [← hm, Real.norm_eq_abs, Real.norm_eq_abs, Real.log_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul hN0.le]
  have hpow' : N ^ (((2 : ℕ) : ℝ) * (-(m / 2))) = N ^ (-m) := by
    congr 1; push_cast; ring
  rw [hpow', abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (by positivity)),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (by linarith))]
  have hr : 0 ≤ N ^ (-m) := Real.rpow_nonneg hN0.le _
  push_cast
  nlinarith [mul_nonneg hr hlogN]

/-- **The mixed remainder with shifts `(M₁, M₂)`** is
`O(N^{-min((h₁+M₁+1)/k₁, (h₂+M₂+1)/k₂)} (1 + log N))`. -/
theorem twoDAmp_env_isBigO (β b L C : ℝ) (h₁ h₂ k₁ k₂ M₁ M₂ D : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (hβ : 0 < β) (hb : 0 < b) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hC : 0 ≤ C)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2)
    (hbound : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |Φ u v s| ≤ C * (u ^ M₁ * v ^ M₂) * ((1 + s) ^ D * Real.exp (β * s * L))) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ Φ) =O[atTop]
      fun N : ℝ => N ^ (-min ((((h₁ + M₁ : ℕ) : ℝ) + 1) / k₁) ((((h₂ + M₂ : ℕ) : ℝ) + 1) / k₂))
        * (1 + Real.log N) := by
  have hG := (twoDGeneral_shift_isBigO (β / 2) (2 * L) b (h₁ + M₁) (h₂ + M₂) k₁ k₂ (by linarith)
    hb hk₁ hk₂).const_mul_left (C * Real.exp ((D : ℝ) ^ 2 / β))
  refine IsBigO.trans (IsBigO.of_bound 1 ?_) hG
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h := twoDAmp_env_le β b L C N h₁ h₂ k₁ k₂ M₁ M₂ D Φ hβ hN hC hΦ hbound
  refine h.trans (le_abs_self _)

end Laplace.Grammar
