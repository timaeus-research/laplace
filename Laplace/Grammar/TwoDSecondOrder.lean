/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AxisExpansion

/-!
# The `d = 2` equal-exponent theorem with a nonconstant amplitude (grammar §4.2, `thm:TaylorTree`)

For the two-dimensional chart integral with general amplitude `Φ(u, v, s)` and equal exponents
`(h₁+1)/k₁ = (h₂+1)/k₂ = p`, the **anchored decomposition**

  `Φ(u,v,s) = Φ(u,0,s) + Φ(0,v,s) − Φ(0,0,s) + [Φ(u,v,s) − Φ(u,0,s) − Φ(0,v,s) + Φ(0,0,s)]`

splits `Z_Φ` into two axis integrals (unit 87), a corner integral, and a mixed term dominated by a
constant-kernel block with both exponents shifted (one logarithm lost, unit 47). Hence

  `Z_Φ(N) = N^{-p} (A log N + B) + O(N^{-(p+δ)} (1 + log N))`,   `δ = min(1/k₁, 1/k₂)`,

with `A = (k₁k₂)⁻¹ ∫ s^{p-1} e^{-βs²} Φ(0,0,s) ds` and
`B = (k₁k₂)⁻¹ ∫ s^{p-1}(log R − log s) e^{-βs²} Φ(0,0,s) ds + k₂⁻¹ ∫ s^{p-1} e^{-βs²} I₁(s) ds
   + k₁⁻¹ ∫ s^{p-1} e^{-βs²} I₂(s) ds`, `Iⱼ` the axis integrals (`twoDAmp_second_order`).
This is the first complete nonconstant-`ξ,η` log polynomial of `thm:TaylorTree`: the constant `B`
sees both axes `{v = 0}`, `{u = 0}`, not only the corner. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- The product-box measure on `ℝ × ℝ`. -/
noncomputable def boxMeasure₂ (b : ℝ) : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Ioc 0 b)).prod ((volume : Measure ℝ).restrict (Ioc 0 b))

/-- The product-form integrand of `twoDAmp`. -/
noncomputable def twoDIntegrand (β N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1 ^ h₁ * (z.2 ^ h₂ * (Real.exp (-β * (N * (z.1 ^ k₁ * z.2 ^ k₂)) ^ 2)
    * Φ z.1 z.2 (N * (z.1 ^ k₁ * z.2 ^ k₂))))

theorem twoDIntegrand_continuous (β N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2) :
    Continuous (twoDIntegrand β N h₁ h₂ k₁ k₂ Φ) := by
  unfold twoDIntegrand
  have h1 : Continuous fun z : ℝ × ℝ => Φ z.1 z.2 (N * (z.1 ^ k₁ * z.2 ^ k₂)) :=
    hΦ.comp (continuous_fst.prodMk (continuous_snd.prodMk (by fun_prop)))
  fun_prop

theorem twoDIntegrand_integrable (β b N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2) :
    Integrable (twoDIntegrand β N h₁ h₂ k₁ k₂ Φ) (boxMeasure₂ b) := by
  unfold boxMeasure₂
  rw [Measure.prod_restrict]
  exact ((twoDIntegrand_continuous β N h₁ h₂ k₁ k₂ Φ hΦ).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- `twoDAmp` in product form. -/
theorem twoDAmp_eq_prod (β b N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2) :
    twoDAmp β b N h₁ h₂ k₁ k₂ Φ = ∫ z, twoDIntegrand β N h₁ h₂ k₁ k₂ Φ z ∂(boxMeasure₂ b) := by
  unfold boxMeasure₂
  rw [integral_prod _ (twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ Φ hΦ)]
  unfold twoDAmp twoDIntegrand
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [← integral_const_mul]

/-- The anchored (mixed) remainder amplitude. -/
noncomputable def mixedAmp (Φ : ℝ → ℝ → ℝ → ℝ) (u v s : ℝ) : ℝ :=
  Φ u v s - Φ u 0 s - Φ 0 v s + Φ 0 0 s

/-- **Anchored decomposition** of the two-dimensional integral. -/
theorem twoDAmp_anchored (β b N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2) :
    twoDAmp β b N h₁ h₂ k₁ k₂ Φ
      = twoDAmp β b N h₁ h₂ k₁ k₂ (fun u _ s => Φ u 0 s)
        + twoDAmp β b N h₁ h₂ k₁ k₂ (fun _ v s => Φ 0 v s)
        - twoDAmp β b N h₁ h₂ k₁ k₂ (fun _ _ s => Φ 0 0 s)
        + twoDAmp β b N h₁ h₂ k₁ k₂ (mixedAmp Φ) := by
  have hA : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 0 x.2.2 :=
    hΦ.comp (continuous_fst.prodMk (continuous_const.prodMk (continuous_snd.comp continuous_snd)))
  have hB : Continuous fun x : ℝ × ℝ × ℝ => Φ 0 x.2.1 x.2.2 :=
    hΦ.comp (continuous_const.prodMk continuous_snd)
  have h0 : Continuous fun x : ℝ × ℝ × ℝ => Φ 0 0 x.2.2 :=
    hΦ.comp (continuous_const.prodMk (continuous_const.prodMk (continuous_snd.comp continuous_snd)))
  have hG : Continuous fun x : ℝ × ℝ × ℝ => mixedAmp Φ x.1 x.2.1 x.2.2 := by
    unfold mixedAmp; exact ((hΦ.sub hA).sub hB).add h0
  have iA := twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ (fun u _ s => Φ u 0 s) hA
  have iB := twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ (fun _ v s => Φ 0 v s) hB
  have i0 := twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ (fun _ _ s => Φ 0 0 s) h0
  have iG := twoDIntegrand_integrable β b N h₁ h₂ k₁ k₂ (mixedAmp Φ) hG
  have iAB : Integrable (fun z => twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u _ s => Φ u 0 s) z
      + twoDIntegrand β N h₁ h₂ k₁ k₂ (fun _ v s => Φ 0 v s) z) (boxMeasure₂ b) := iA.add iB
  have iAB0 : Integrable (fun z => (twoDIntegrand β N h₁ h₂ k₁ k₂ (fun u _ s => Φ u 0 s) z
      + twoDIntegrand β N h₁ h₂ k₁ k₂ (fun _ v s => Φ 0 v s) z)
      - twoDIntegrand β N h₁ h₂ k₁ k₂ (fun _ _ s => Φ 0 0 s) z) (boxMeasure₂ b) := iAB.sub i0
  rw [twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ Φ hΦ,
    twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ (fun u _ s => Φ u 0 s) hA,
    twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ (fun _ v s => Φ 0 v s) hB,
    twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ (fun _ _ s => Φ 0 0 s) h0,
    twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ (mixedAmp Φ) hG, ← integral_add iA iB,
    ← integral_sub iAB i0, ← integral_add iAB0 iG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  unfold twoDIntegrand mixedAmp
  ring

/-- `(1+s)² ≤ max 2 (4/β) · e^{(β/2)s²}`. -/
theorem one_add_sq_le_exp (β s : ℝ) (hβ : 0 < β) :
    (1 + s) ^ 2 ≤ max 2 (4 / β) * Real.exp (β / 2 * s ^ 2) := by
  have h1 : 1 + β / 2 * s ^ 2 ≤ Real.exp (β / 2 * s ^ 2) := by
    linarith [Real.add_one_le_exp (β / 2 * s ^ 2)]
  have h2 : (1 + s) ^ 2 ≤ 2 + 2 * s ^ 2 := by nlinarith [sq_nonneg (1 - s)]
  have hc2 : 2 ≤ max 2 (4 / β) := le_max_left _ _
  have hc4 : 4 / β ≤ max 2 (4 / β) := le_max_right _ _
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have h3 : 2 * s ^ 2 ≤ max 2 (4 / β) * (β / 2 * s ^ 2) := by
    have : (4 / β) * (β / 2 * s ^ 2) = 2 * s ^ 2 := by field_simp; ring
    rw [← this]
    exact mul_le_mul_of_nonneg_right hc4 (by positivity)
  have hm0 : 0 ≤ max 2 (4 / β) := by linarith
  calc (1 + s) ^ 2 ≤ 2 + 2 * s ^ 2 := h2
    _ ≤ max 2 (4 / β) * 1 + max 2 (4 / β) * (β / 2 * s ^ 2) := by linarith
    _ = max 2 (4 / β) * (1 + β / 2 * s ^ 2) := by ring
    _ ≤ max 2 (4 / β) * Real.exp (β / 2 * s ^ 2) := mul_le_mul_of_nonneg_left h1 hm0

/-- The mixed term is dominated by the constant-kernel integral with both exponents shifted:
`|Z_G(N)| ≤ C₂ C₃ · twoDGeneral (β/2) (2L) b (N²) (h₁+1) (h₂+1) k₁ k₂`. -/
theorem twoDAmp_mixed_le (β b L C₂ N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ) (hβ : 0 < β)
    (hN : 0 ≤ N) (hC₂ : 0 ≤ C₂)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2)
    (hmix : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |mixedAmp Φ u v s| ≤ C₂ * (u * v) * ((1 + s) ^ 2 * Real.exp (β * s * L))) :
    |twoDAmp β b N h₁ h₂ k₁ k₂ (mixedAmp Φ)|
      ≤ C₂ * max 2 (4 / β) * twoDGeneral (β / 2) (2 * L) b (N ^ 2) (h₁ + 1) (h₂ + 1) k₁ k₂ := by
  have hG : Continuous fun x : ℝ × ℝ × ℝ => mixedAmp Φ x.1 x.2.1 x.2.2 := by
    unfold mixedAmp
    have hA : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 0 x.2.2 :=
      hΦ.comp (continuous_fst.prodMk (continuous_const.prodMk (continuous_snd.comp continuous_snd)))
    have hB : Continuous fun x : ℝ × ℝ × ℝ => Φ 0 x.2.1 x.2.2 :=
      hΦ.comp (continuous_const.prodMk continuous_snd)
    have h0 : Continuous fun x : ℝ × ℝ × ℝ => Φ 0 0 x.2.2 :=
      hΦ.comp (continuous_const.prodMk (continuous_const.prodMk
        (continuous_snd.comp continuous_snd)))
    exact ((hΦ.sub hA).sub hB).add h0
  -- the constant-kernel integrand in product form
  set W : ℝ × ℝ → ℝ := fun z => z.1 ^ (h₁ + 1) * z.2 ^ (h₂ + 1)
    * Real.exp (-(β / 2) * N ^ 2 * (z.1 ^ k₁ * z.2 ^ k₂) ^ 2
      + β / 2 * Real.sqrt (N ^ 2) * (z.1 ^ k₁ * z.2 ^ k₂) * (2 * L)) with hW
  have hWc : Continuous W := by simp only [hW]; fun_prop
  have hWi : Integrable W (boxMeasure₂ b) := by
    unfold boxMeasure₂
    rw [Measure.prod_restrict]
    exact (hWc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hWeq : twoDGeneral (β / 2) (2 * L) b (N ^ 2) (h₁ + 1) (h₂ + 1) k₁ k₂
      = ∫ z, W z ∂(boxMeasure₂ b) := by
    unfold twoDGeneral boxMeasure₂
    rw [integral_prod _ (by unfold boxMeasure₂ at hWi; exact hWi)]
  have hsqrt : Real.sqrt (N ^ 2) = N := Real.sqrt_sq hN
  have hmem : ∀ᵐ z ∂(boxMeasure₂ b), z ∈ Ioc (0 : ℝ) b ×ˢ Ioc (0 : ℝ) b := by
    unfold boxMeasure₂
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hpt : ∀ᵐ z ∂(boxMeasure₂ b), ‖twoDIntegrand β N h₁ h₂ k₁ k₂ (mixedAmp Φ) z‖
      ≤ C₂ * max 2 (4 / β) * W z := by
    filter_upwards [hmem] with z hz
    obtain ⟨hu, hv⟩ := hz
    set u := z.1 with hu_def
    set v := z.2 with hv_def
    have hu0 : 0 < u := hu.1
    have hv0 : 0 < v := hv.1
    set s : ℝ := N * (u ^ k₁ * v ^ k₂) with hs
    have hs0 : 0 ≤ s := by positivity
    have huv : 0 ≤ u ^ k₁ * v ^ k₂ := by positivity
    have hm := hmix u ⟨hu.1.le, hu.2⟩ v ⟨hv.1.le, hv.2⟩ s hs0
    have hE := one_add_sq_le_exp β s hβ
    have hmax : 0 ≤ max 2 (4 / β) := le_trans zero_le_two (le_max_left _ _)
    simp only [twoDIntegrand, hW]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hu.1.le _),
      abs_of_nonneg (pow_nonneg hv.1.le _), abs_of_pos (Real.exp_pos _), hsqrt, ← hs]
    -- kernel identity
    have hker : Real.exp (-(β / 2) * N ^ 2 * (u ^ k₁ * v ^ k₂) ^ 2
          + β / 2 * N * (u ^ k₁ * v ^ k₂) * (2 * L))
        = Real.exp (-β * s ^ 2) * (Real.exp (β / 2 * s ^ 2) * Real.exp (β * s * L)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hs]; ring
    rw [hker]
    have hstep : Real.exp (-β * s ^ 2) * |mixedAmp Φ u v s|
        ≤ Real.exp (-β * s ^ 2) * (C₂ * (u * v) * ((1 + s) ^ 2 * Real.exp (β * s * L))) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    have hstep2 : (1 + s) ^ 2 * Real.exp (β * s * L)
        ≤ max 2 (4 / β) * Real.exp (β / 2 * s ^ 2) * Real.exp (β * s * L) :=
      mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le
    calc u ^ h₁ * (v ^ h₂ * (Real.exp (-β * s ^ 2) * |mixedAmp Φ u v s|))
        ≤ u ^ h₁ * (v ^ h₂ * (Real.exp (-β * s ^ 2)
            * (C₂ * (u * v) * ((1 + s) ^ 2 * Real.exp (β * s * L))))) := by
          gcongr
      _ ≤ u ^ h₁ * (v ^ h₂ * (Real.exp (-β * s ^ 2)
            * (C₂ * (u * v)
              * (max 2 (4 / β) * Real.exp (β / 2 * s ^ 2) * Real.exp (β * s * L))))) := by
          gcongr
      _ = C₂ * max 2 (4 / β) * (u ^ (h₁ + 1) * v ^ (h₂ + 1)
            * (Real.exp (-β * s ^ 2) * (Real.exp (β / 2 * s ^ 2) * Real.exp (β * s * L)))) := by
          ring
  rw [twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ (mixedAmp Φ) hG, hWeq, ← Real.norm_eq_abs,
    ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hWi.const_mul _) hpt

/-- The shifted constant-kernel integral at `n = N²` is `O(N^{-(p+δ)} (1 + log N))`. -/
theorem twoDGeneral_mixed_isBigO (β a b p : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) :
    (fun N : ℝ => twoDGeneral β a b (N ^ 2) (h₁ + 1) (h₂ + 1) k₁ k₂) =O[atTop]
      fun N : ℝ => N ^ (-(p + min (k₁ : ℝ)⁻¹ (k₂ : ℝ)⁻¹)) * (1 + Real.log N) := by
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have h := twoDGeneral_isBigO_min β a b (h₁ + 1) (h₂ + 1) k₁ k₂ hβ hb hk₁ hk₂
  have hsq : Tendsto (fun N : ℝ => N ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hcomp := h.comp_tendsto hsq
  -- the exponent
  have hm : min ((((h₁ + 1 : ℕ) : ℝ) + 1) / k₁) ((((h₂ + 1 : ℕ) : ℝ) + 1) / k₂)
      = p + min (k₁ : ℝ)⁻¹ (k₂ : ℝ)⁻¹ := by
    have e1 : (((h₁ + 1 : ℕ) : ℝ) + 1) / k₁ = p + (k₁ : ℝ)⁻¹ := by
      rw [← hp₁]; push_cast; field_simp
    have e2 : (((h₂ + 1 : ℕ) : ℝ) + 1) / k₂ = p + (k₂ : ℝ)⁻¹ := by
      rw [← hp₂]; push_cast; field_simp
    rw [e1, e2, min_add_add_left]
  refine hcomp.trans (IsBigO.of_bound 2 ?_)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  simp only [Function.comp]
  rw [hm, Real.norm_eq_abs, Real.norm_eq_abs, Real.log_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul hN0.le]
  have hpow : 0 ≤ N ^ (((2 : ℕ) : ℝ) * (-((p + min (k₁ : ℝ)⁻¹ (k₂ : ℝ)⁻¹) / 2))) :=
    Real.rpow_nonneg hN0.le _
  have hpow' : N ^ (((2 : ℕ) : ℝ) * (-((p + min (k₁ : ℝ)⁻¹ (k₂ : ℝ)⁻¹) / 2)))
      = N ^ (-(p + min (k₁ : ℝ)⁻¹ (k₂ : ℝ)⁻¹)) := by
    congr 1; push_cast; ring
  rw [hpow', abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (by positivity)),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (by linarith))]
  have hr : 0 ≤ N ^ (-(p + min (k₁ : ℝ)⁻¹ (k₂ : ℝ)⁻¹)) := Real.rpow_nonneg hN0.le _
  nlinarith [mul_nonneg hr hlogN]

/-- The axis integral of an amplitude constant in `u` vanishes. -/
theorem axisIntegral_const (b : ℝ) (c : ℝ → ℝ) : axisIntegral b (fun _ s => c s) = fun _ => 0 := by
  funext s; simp [axisIntegral]

theorem logMoment_zero_fun (β α : ℝ) (ℓ : ℕ) : logMoment β α ℓ (fun _ => (0 : ℝ)) = 0 := by
  simp [logMoment]

/-- The log coefficient `A = (k₁k₂)⁻¹ ∫ s^{p-1} e^{-βs²} Φ(0,0,s) ds`. -/
noncomputable def twoDA (β p : ℝ) (k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  1 / ((k₁ : ℝ) * k₂) * logMoment β p 0 (fun s => Φ 0 0 s)

/-- The constant coefficient
`B = (k₁k₂)⁻¹ ∫ s^{p-1}(log R − log s) e^{-βs²} Φ(0,0,s) + k₂⁻¹ ∫ s^{p-1} e^{-βs²} I₁
   + k₁⁻¹ ∫ s^{p-1} e^{-βs²} I₂`. -/
noncomputable def twoDB (β b p : ℝ) (k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  1 / ((k₁ : ℝ) * k₂) * (Real.log (b ^ (k₁ + k₂)) * logMoment β p 0 (fun s => Φ 0 0 s)
    - logMoment β p 1 (fun s => Φ 0 0 s))
  + 1 / (k₂ : ℝ) * logMoment β p 0 (axisIntegral b (fun u s => Φ u 0 s))
  + 1 / (k₁ : ℝ) * logMoment β p 0 (axisIntegral b (fun v s => Φ 0 v s))

/-- Converting the `N ≥ 1` bound of unit 87 into `O(N^{-(p+δ)} (1 + log N))`. -/
theorem isBigO_of_axis_bound (p e δ : ℝ) (hδe : δ ≤ e) (f : ℝ → ℝ) (K : ℝ)
    (hf : ∀ N : ℝ, 1 ≤ N → |f N| ≤ K * N ^ (-(p + e)) * (1 + Real.log N)) :
    f =O[atTop] fun N : ℝ => N ^ (-(p + δ)) * (1 + Real.log N) := by
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (by linarith))]
  have hexp : N ^ (-(p + e)) ≤ N ^ (-(p + δ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hK : 0 ≤ K := by
    have := hf 1 le_rfl
    simp only [Real.log_one, add_zero, mul_one, Real.one_rpow] at this
    exact (abs_nonneg _).trans this
  calc |f N| ≤ K * N ^ (-(p + e)) * (1 + Real.log N) := hf N hN
    _ ≤ K * N ^ (-(p + δ)) * (1 + Real.log N) := by gcongr
    _ = K * (N ^ (-(p + δ)) * (1 + Real.log N)) := by ring

/-- **The `d = 2` equal-exponent theorem** (`thm:TaylorTree` at `d = 2`, first log polynomial):
`Z_Φ(N) = N^{-p} (A log N + B) + O(N^{-(p+δ)} (1 + log N))`, `δ = min(1/k₁, 1/k₂)`. -/
theorem twoDAmp_second_order (β b L C₁ C₂ M p : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (hβ : 0 < β) (hb : 0 < b) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hΦ : Continuous fun x : ℝ × ℝ × ℝ => Φ x.1 x.2.1 x.2.2)
    (hlipA : ∀ u ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |Φ u 0 s - Φ 0 0 s| ≤ C₁ * u * ((1 + s) * Real.exp (β * s * L)))
    (hlipB : ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |Φ 0 v s - Φ 0 0 s| ≤ C₁ * v * ((1 + s) * Real.exp (β * s * L)))
    (hmix : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b, ∀ s, 0 ≤ s →
      |mixedAmp Φ u v s| ≤ C₂ * (u * v) * ((1 + s) ^ 2 * Real.exp (β * s * L)))
    (hΦ₀ : ∀ s, 0 ≤ s → |Φ 0 0 s| ≤ M * Real.exp (β * s * L)) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ Φ
        - N ^ (-p) * (twoDA β p k₁ k₂ Φ * Real.log N + twoDB β b p k₁ k₂ Φ)) =O[atTop]
      fun N : ℝ => N ^ (-(p + min (k₁ : ℝ)⁻¹ (k₂ : ℝ)⁻¹)) * (1 + Real.log N) := by
  set δ : ℝ := min (k₁ : ℝ)⁻¹ (k₂ : ℝ)⁻¹ with hδ
  have hδ₁ : δ ≤ (k₁ : ℝ)⁻¹ := min_le_left _ _
  have hδ₂ : δ ≤ (k₂ : ℝ)⁻¹ := min_le_right _ _
  -- continuity of the one-variable amplitudes
  have hAc : Continuous (Function.uncurry fun u s => Φ u 0 s) :=
    hΦ.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  have hBc : Continuous (Function.uncurry fun v s => Φ 0 v s) :=
    hΦ.comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
  have h0c : Continuous (Function.uncurry fun (_ : ℝ) s => Φ 0 0 s) :=
    hΦ.comp (continuous_const.prodMk (continuous_const.prodMk continuous_snd))
  -- the three one-variable expansions
  obtain ⟨KA, hKA⟩ := twoDAmp_uOnly_expansion β b L C₁ M p h₁ h₂ k₁ k₂ (fun u s => Φ u 0 s) hβ hb
    hk₁ hk₂ hp₁ hp₂ hC₁ hAc hlipA hΦ₀
  obtain ⟨KB, hKB⟩ := twoDAmp_uOnly_expansion β b L C₁ M p h₂ h₁ k₂ k₁ (fun v s => Φ 0 v s) hβ hb
    hk₂ hk₁ hp₂ hp₁ hC₁ hBc hlipB hΦ₀
  obtain ⟨K0, hK0⟩ := twoDAmp_uOnly_expansion β b L C₁ M p h₁ h₂ k₁ k₂ (fun _ s => Φ 0 0 s) hβ hb
    hk₁ hk₂ hp₁ hp₂ hC₁ h0c (fun u hu s hs => by
      simp only [sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC₁ hu.1) (mul_nonneg (by linarith) (Real.exp_pos _).le)) hΦ₀
  have hOA := isBigO_of_axis_bound p (k₁ : ℝ)⁻¹ δ hδ₁ _ KA hKA
  have hOB := isBigO_of_axis_bound p (k₂ : ℝ)⁻¹ δ hδ₂ _ KB hKB
  have hO0 := isBigO_of_axis_bound p (k₁ : ℝ)⁻¹ δ hδ₁ _ K0 hK0
  -- the mixed term
  have hOG : (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (mixedAmp Φ)) =O[atTop]
      fun N : ℝ => N ^ (-(p + δ)) * (1 + Real.log N) := by
    have hG := twoDGeneral_mixed_isBigO (β / 2) (2 * L) b p h₁ h₂ k₁ k₂ (by positivity) hb hk₁ hk₂
      hp₁ hp₂
    refine (IsBigO.of_bound (C₂ * max 2 (4 / β)) ?_).trans hG
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hle := twoDAmp_mixed_le β b L C₂ N h₁ h₂ k₁ k₂ Φ hβ hN hC₂ hΦ hmix
    have hmax : 0 ≤ C₂ * max 2 (4 / β) :=
      mul_nonneg hC₂ (le_trans zero_le_two (le_max_left _ _))
    calc |twoDAmp β b N h₁ h₂ k₁ k₂ (mixedAmp Φ)|
        ≤ C₂ * max 2 (4 / β) * twoDGeneral (β / 2) (2 * L) b (N ^ 2) (h₁ + 1) (h₂ + 1) k₁ k₂ := hle
      _ ≤ C₂ * max 2 (4 / β) * |twoDGeneral (β / 2) (2 * L) b (N ^ 2) (h₁ + 1) (h₂ + 1) k₁ k₂| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hmax
  -- assemble
  have hsum := ((hOA.add hOB).sub hO0).add hOG
  refine hsum.congr_left fun N => ?_
  rw [twoDAmp_anchored β b N h₁ h₂ k₁ k₂ Φ hΦ,
    twoDAmp_swap β b N h₁ h₂ k₁ k₂ (fun _ v s => Φ 0 v s)
      (hΦ.comp (continuous_const.prodMk continuous_snd))]
  have hR : b ^ (k₂ + k₁) = b ^ (k₁ + k₂) := by rw [add_comm]
  simp only [axisA, axisB, twoDA, twoDB, axisIntegral_const, logMoment_zero_fun, hR]
  ring

end Laplace.Grammar
