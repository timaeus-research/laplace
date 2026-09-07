/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.WeightedPowerSubstitution

/-!
# Helpers for the recursive product-density lemma (general-`d` monomial model, step 2a)

Three transport lemmas for Lebesgue integrals on `(0,1]`, used in the induction for the density of
`∏ tᵢ` under `∏ tᵢ^{λ−1} dt`:

* scaling: `∫_{(0,1]} F(t z) dz = (1/t) ∫_{(0,t]} F(w) dw` for `t > 0` (`lintegral_Ioc_scale`);
* the triangle swap: `∫_{(0,1]} ∫_{(0,t]} G(t,w) dw dt = ∫_{(0,1]} ∫_{[w,1]} G(t,w) dt dw`
  (`lintegral_triangle_swap`);
* the FTC identity of unit 165 in `ℝ≥0∞` form on `[z,1]` (`lintegral_log_sub_pow_div`).

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real

namespace Laplace.Grammar

/-- `z ↦ t z` maps `(0,1]` onto `(0,t]` for `t > 0`. -/
theorem image_mul_Ioc (t : ℝ) (ht : 0 < t) : (fun z : ℝ => t * z) '' Ioc 0 1 = Ioc 0 t := by
  ext w
  constructor
  · rintro ⟨z, ⟨hz0, hz1⟩, rfl⟩
    exact ⟨by positivity, by nlinarith⟩
  · rintro ⟨hw0, hwt⟩
    refine ⟨w / t, ⟨by positivity, (div_le_one ht).2 hwt⟩, ?_⟩
    change t * (w / t) = w
    field_simp

/-- **Scaling**: `∫_{(0,1]} F(t z) dz = (1/t) ∫_{(0,t]} F(w) dw`. -/
theorem lintegral_Ioc_scale (t : ℝ) (ht : 0 < t) (F : ℝ → ENNReal) :
    ∫⁻ z in Ioc (0 : ℝ) 1, F (t * z) = ENNReal.ofReal (1 / t) * ∫⁻ w in Ioc (0 : ℝ) t, F w := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioc (0 : ℝ) 1)
    (f := fun z : ℝ => t * z) (f' := fun _ => t) measurableSet_Ioc
    (fun z _ => ((hasDerivAt_id z).const_mul t).hasDerivWithinAt.congr_deriv (by simp))
    (fun z _ z' _ h => mul_left_cancel₀ ht.ne' h) F
  rw [image_mul_Ioc t ht] at h
  rw [h, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioc fun z _ => ?_
  rw [abs_of_pos ht, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    one_div_mul_cancel ht.ne', ENNReal.ofReal_one, one_mul]

/-- **Triangle swap**: `∫_{(0,1]} ∫_{(0,t]} G(t,w) dw dt = ∫_{(0,1]} ∫_{[w,1]} G(t,w) dt dw`. -/
theorem lintegral_triangle_swap (G : ℝ → ℝ → ENNReal)
    (hG : Measurable fun q : ℝ × ℝ => G q.1 q.2) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ w in Ioc (0 : ℝ) t, G t w
      = ∫⁻ w in Ioc (0 : ℝ) 1, ∫⁻ t in Icc w 1, G t w := by
  -- both inner integrals as integrals over `(0,1]` against an indicator of the triangle
  have hleft : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ w in Ioc (0 : ℝ) t, G t w
      = ∫⁻ w in Ioc (0 : ℝ) 1, {q : ℝ × ℝ | q.2 ≤ q.1}.indicator (fun q => G q.1 q.2) (t, w) := by
    intro t ht
    have hset : Ioc (0 : ℝ) t = Iic t ∩ Ioc 0 1 := by
      ext w; simp only [mem_Ioc, mem_inter_iff, mem_Iic]
      constructor
      · rintro ⟨h0, h1⟩; exact ⟨h1, h0, h1.trans ht.2⟩
      · rintro ⟨h1, h0, _⟩; exact ⟨h0, h1⟩
    rw [hset, ← Measure.restrict_restrict measurableSet_Iic,
      ← lintegral_indicator measurableSet_Iic]
    refine lintegral_congr fun w => ?_
    by_cases hw : w ≤ t
    · rw [indicator_of_mem (show w ∈ Iic t from hw),
        indicator_of_mem (show (t, w) ∈ {q : ℝ × ℝ | q.2 ≤ q.1} from hw)]
    · rw [indicator_of_notMem (show w ∉ Iic t from hw),
        indicator_of_notMem (show (t, w) ∉ {q : ℝ × ℝ | q.2 ≤ q.1} from hw)]
  have hright : ∀ w ∈ Ioc (0 : ℝ) 1, ∫⁻ t in Icc w 1, G t w
      = ∫⁻ t in Ioc (0 : ℝ) 1, {q : ℝ × ℝ | q.2 ≤ q.1}.indicator (fun q => G q.1 q.2) (t, w) := by
    intro w hw
    have hset : Icc w 1 = Ici w ∩ Ioc 0 1 := by
      ext t; simp only [mem_Icc, mem_Ioc, mem_inter_iff, mem_Ici]
      constructor
      · rintro ⟨h0, h1⟩; exact ⟨h0, lt_of_lt_of_le hw.1 h0, h1⟩
      · rintro ⟨h0, _, h1⟩; exact ⟨h0, h1⟩
    rw [hset, ← Measure.restrict_restrict measurableSet_Ici,
      ← lintegral_indicator measurableSet_Ici]
    refine lintegral_congr fun t => ?_
    by_cases hwt : w ≤ t
    · rw [indicator_of_mem (show t ∈ Ici w from hwt),
        indicator_of_mem (show (t, w) ∈ {q : ℝ × ℝ | q.2 ≤ q.1} from hwt)]
    · rw [indicator_of_notMem (show t ∉ Ici w from hwt),
        indicator_of_notMem (show (t, w) ∉ {q : ℝ × ℝ | q.2 ≤ q.1} from hwt)]
  rw [setLIntegral_congr_fun measurableSet_Ioc hleft,
    setLIntegral_congr_fun measurableSet_Ioc hright]
  -- Tonelli on `(0,1] × (0,1]`
  have hmeas : Measurable fun q : ℝ × ℝ =>
      {q : ℝ × ℝ | q.2 ≤ q.1}.indicator (fun q => G q.1 q.2) q :=
    hG.indicator (measurableSet_le measurable_snd measurable_fst)
  exact lintegral_lintegral_swap hmeas.aemeasurable

/-- The FTC identity of unit 165 in `ℝ≥0∞` form: `∫_{[z,1]} (log t − log z)^d / t dt`. -/
theorem lintegral_log_sub_pow_div (z : ℝ) (hz : 0 < z) (hz1 : z ≤ 1) (d : ℕ) :
    ∫⁻ t in Icc z 1, ENNReal.ofReal ((Real.log t - Real.log z) ^ d / t)
      = ENNReal.ofReal ((-Real.log z) ^ (d + 1) / ((d : ℝ) + 1)) := by
  rw [← integral_log_sub_pow_div z hz hz1 d, intervalIntegral.integral_of_le hz1,
    setLIntegral_congr Ioc_ae_eq_Icc.symm]
  have hint : IntegrableOn (fun t => (Real.log t - Real.log z) ^ d / t) (Ioc z 1) := by
    have hcont : ContinuousOn (fun t => (Real.log t - Real.log z) ^ d / t) (uIcc z 1) := by
      rw [uIcc_of_le hz1]
      refine ContinuousOn.div (ContinuousOn.pow (ContinuousOn.sub ?_ continuousOn_const) d)
        continuousOn_id fun t ht => (lt_of_lt_of_le hz ht.1).ne'
      exact Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le hz ht.1).ne'
    have := (hcont.intervalIntegrable (μ := volume)).def'
    rwa [uIoc_of_le hz1] at this
  rw [ofReal_integral_eq_lintegral_ofReal hint]
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
  have ht0 : 0 < t := lt_trans hz ht.1
  have hlog : 0 ≤ Real.log t - Real.log z := by
    have := Real.log_le_log hz ht.1.le; linarith
  change (0 : ℝ) ≤ (Real.log t - Real.log z) ^ d / t
  positivity

end Laplace.Grammar
