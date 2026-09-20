/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AbelianTransferLog

/-!
# The multiplicity-two instance: `x²y²` on the unit square

For `K(x, y) = (xy)²` on `[0, 1]²` the sublevel volume is elementary and
carries a logarithm:

  `vol{(x, y) ∈ [0,1]² : (xy)² ≤ ε} = ∫₀¹ min(1, √ε/x) dx = √ε (1 - log √ε)`

(`sublevelMass_sq_mul_sq`: Fubini in `x`, the section over `x ∈ (0, 1]` is the
interval `[0, min(1, √ε/x)]`, and the one-dimensional integral splits at
`x = √ε`). For `ε ≤ e^{-2}` this is squeezed between `½ √ε log(1/ε)` and
`√ε log(1/ε)`, so the log-multiplicity transfer gives

  `∫_{[0,1]²} e^{-t x²y²} = Θ(t^{-1/2} log t)`   (`boltzmannMass_sq_mul_sq_transfer`),

the real log canonical threshold `1/2` with multiplicity `2`, with no
resolution of singularities.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Laplace

/-- The unit square. -/
def unitSquare : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

theorem measurableSet_unitSquare : MeasurableSet unitSquare :=
  measurableSet_Icc.prod measurableSet_Icc

instance : IsFiniteMeasure (volume.restrict unitSquare) :=
  isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne

/-- The section over `x ∈ (0, 1]` of the sublevel set on the square. -/
theorem section_sublevel_sq_mul_sq {a x : ℝ} (ha : 0 < a) (hx : x ∈ Ioc (0 : ℝ) 1) :
    Prod.mk x ⁻¹' ({p : ℝ × ℝ | (p.1 * p.2) ^ 2 ≤ a ^ 2} ∩ unitSquare) =
      Icc 0 (min 1 (a / x)) := by
  obtain ⟨hx0, hx1⟩ := hx
  ext y
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, unitSquare, mem_prod, mem_Icc,
    le_min_iff]
  constructor
  · rintro ⟨hsq, ⟨-, -⟩, hy0, hy1⟩
    refine ⟨hy0, hy1, ?_⟩
    have hxy : 0 ≤ x * y := mul_nonneg hx0.le hy0
    have h : x * y ≤ a := (pow_le_pow_iff_left₀ hxy ha.le two_ne_zero).mp hsq
    rwa [le_div_iff₀ hx0, mul_comm]
  · rintro ⟨hy0, hy1, hya⟩
    refine ⟨?_, ⟨hx0.le, hx1⟩, hy0, hy1⟩
    have h : x * y ≤ a := by rwa [le_div_iff₀ hx0, mul_comm] at hya
    exact pow_le_pow_left₀ (mul_nonneg hx0.le hy0) h 2

/-- The one-dimensional integral `∫₀¹ min(1, a/x) dx = a - a log a` for `0 < a ≤ 1`. -/
theorem integral_min_one_div {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∫ x in Ioc (0 : ℝ) 1, min 1 (a / x) = a - a * Real.log a := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hint : IntegrableOn (fun x ↦ min 1 (a / x)) (Ioc (0 : ℝ) 1) := by
    refine Integrable.of_bound
      (by fun_prop : Measurable fun x : ℝ ↦ min 1 (a / x)).aestronglyMeasurable 1 ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx ↦ ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [le_min zero_le_one (div_nonneg ha0.le hx.1.le)]
    · exact min_le_left _ _
  have hf1 : IntervalIntegrable (fun x ↦ min 1 (a / x)) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0.le).mpr
      (hint.mono_set (Ioc_subset_Ioc_right ha1))
  have hf2 : IntervalIntegrable (fun x ↦ min 1 (a / x)) volume a 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).mpr
      (hint.mono_set (Ioc_subset_Ioc_left ha0.le))
  rw [← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals hf1 hf2]
  have h1 : ∫ x in (0 : ℝ)..a, min 1 (a / x) = a := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (1 : ℝ)) ?_,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    refine Eventually.of_forall fun x hx ↦ ?_
    rw [uIoc_of_le ha0.le] at hx
    exact min_eq_left ((le_div_iff₀ hx.1).mpr (by linarith [hx.2]))
  have h2 : ∫ x in a..1, min 1 (a / x) = -(a * Real.log a) := by
    rw [intervalIntegral.integral_congr_ae (g := fun x ↦ a * x⁻¹) ?_,
      intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 one_pos, one_div,
      Real.log_inv]
    · ring
    refine Eventually.of_forall fun x hx ↦ ?_
    rw [uIoc_of_le ha1] at hx
    rw [min_eq_right ((div_le_iff₀ (ha0.trans hx.1)).mpr (by linarith [hx.1])), div_eq_mul_inv]
  rw [h1, h2]
  ring

/-- **Sublevel mass of `x²y²` on the unit square**: `√ε (1 - log √ε)` for `0 < ε ≤ 1`. -/
theorem sublevelMass_sq_mul_sq {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    sublevelMass (volume.restrict unitSquare) (fun p : ℝ × ℝ ↦ (p.1 * p.2) ^ 2) ε =
      √ε - √ε * Real.log √ε := by
  set a : ℝ := √ε with ha_def
  have ha0 : 0 < a := Real.sqrt_pos.mpr hε
  have ha1 : a ≤ 1 := Real.sqrt_le_one.mpr hε1
  have haε : a ^ 2 = ε := Real.sq_sqrt hε.le
  set T : Set (ℝ × ℝ) := {p | (p.1 * p.2) ^ 2 ≤ a ^ 2} with hT_def
  have hTm : MeasurableSet T := measurableSet_le (by fun_prop) measurable_const
  have hset : {p : ℝ × ℝ | (p.1 * p.2) ^ 2 ≤ ε} = T := by rw [hT_def, haε]
  unfold sublevelMass
  rw [hset, measureReal_def, Measure.restrict_apply hTm, Measure.volume_eq_prod ℝ ℝ,
    Measure.prod_apply (hTm.inter measurableSet_unitSquare)]
  have hae : (fun x ↦ volume (Prod.mk x ⁻¹' (T ∩ unitSquare))) =ᵐ[volume]
      (Ioc (0 : ℝ) 1).indicator fun x ↦ ENNReal.ofReal (min 1 (a / x)) := by
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with x hx0
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hx, section_sublevel_sq_mul_sq ha0 hx, Real.volume_Icc, sub_zero]
    · rw [indicator_of_notMem hx]
      have hempty : Prod.mk x ⁻¹' (T ∩ unitSquare) = ∅ := by
        ext y
        simp only [mem_preimage, mem_inter_iff, unitSquare, mem_prod, mem_Icc,
          mem_empty_iff_false, iff_false]
        rintro ⟨-, ⟨hx0', hx1⟩, -⟩
        exact hx ⟨lt_of_le_of_ne hx0' (Ne.symm hx0), hx1⟩
      rw [hempty, measure_empty]
  rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Ioc]
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hint : IntegrableOn (fun x ↦ min 1 (a / x)) (Ioc (0 : ℝ) 1) := by
    refine Integrable.of_bound
      (by fun_prop : Measurable fun x : ℝ ↦ min 1 (a / x)).aestronglyMeasurable 1 ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx ↦ ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [le_min zero_le_one (div_nonneg ha0.le hx.1.le)]
    · exact min_le_left _ _
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), 0 ≤ min 1 (a / x) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun x hx ↦ le_min zero_le_one (div_nonneg ha0.le hx.1.le)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn), integral_min_one_div ha0 ha1]

/-- **The multiplicity-two instance**: `∫_{[0,1]²} e^{-t x²y²} = Θ(t^{-1/2} log t)`. -/
theorem boltzmannMass_sq_mul_sq_transfer :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ t : ℝ in atTop,
      C₁ * t ^ (-(1 / 2 : ℝ)) * Real.log t ≤
          boltzmannMass (volume.restrict unitSquare) (fun p : ℝ × ℝ ↦ (p.1 * p.2) ^ 2) t ∧
      boltzmannMass (volume.restrict unitSquare) (fun p : ℝ × ℝ ↦ (p.1 * p.2) ^ 2) t ≤
          C₂ * t ^ (-(1 / 2 : ℝ)) * Real.log t := by
  have hε₀ : (0 : ℝ) < Real.exp (-2) := Real.exp_pos _
  have hε₀1 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  -- the two-sided log bound on the sublevel mass for `ε ≤ e^{-2}`
  have hbounds : ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-2) →
      1 / 2 * ε ^ (1 / 2 : ℝ) * (Real.log ε⁻¹) ^ 1 ≤
          sublevelMass (volume.restrict unitSquare) (fun p : ℝ × ℝ ↦ (p.1 * p.2) ^ 2) ε ∧
      sublevelMass (volume.restrict unitSquare) (fun p : ℝ × ℝ ↦ (p.1 * p.2) ^ 2) ε ≤
          1 * ε ^ (1 / 2 : ℝ) * (Real.log ε⁻¹) ^ 1 := by
    intro ε hε hεle
    have hε1 : ε ≤ 1 := hεle.trans hε₀1.le
    rw [sublevelMass_sq_mul_sq hε hε1, ← Real.sqrt_eq_rpow, Real.log_sqrt hε.le, Real.log_inv,
      pow_one]
    have hs : 0 ≤ √ε := Real.sqrt_nonneg ε
    have hL : 2 ≤ -Real.log ε := by
      have := Real.log_le_log hε hεle
      rw [Real.log_exp] at this
      linarith
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := boltzmannMass_log_transfer (volume.restrict unitSquare)
    (fun p : ℝ × ℝ ↦ (p.1 * p.2) ^ 2) (by fun_prop) (fun p ↦ sq_nonneg _) 1 (by norm_num) hε₀
    hε₀1 (by norm_num) one_pos (fun ε hε hεle ↦ (hbounds ε hε hεle).1)
    (fun ε hε hεle ↦ (hbounds ε hε hεle).2)
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  filter_upwards [h] with t ht
  simpa [pow_one] using ht

end Laplace
