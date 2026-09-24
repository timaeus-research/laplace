/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The weighted mixed truth: a positive exponent removes the logarithm

The model fibre integral of the truth `xy = s` on the square `(0, b)²` against the weight
`x^{h−1} dx` (the coarea measure `dx/x` times `x^h`): for `h > 0` the fibre integral converges,
with no logarithm, to the finite measure `x^{h−1} dx` on the axis `y = 0` (`tendsto_weightedMixed`,
dominated convergence with the bound `C x^{h−1}`). The logarithmic corner mass of `MixedTruthLog`
is the threshold `h = 0`; every positive weight exponent gives a finite, non-point-supported
limit (Astra, round 5, the weighted family, case `h > 0`).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

/-- The range identity `Ioi c ∩ Ioo 0 b = Ioo c b` for `0 < c`. -/
theorem Ioi_inter_Ioo_eq {b c : ℝ} (hc : 0 < c) : Ioi c ∩ Ioo 0 b = Ioo c b := by
  ext x
  simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, hc.trans h1, h2⟩

/-- **The weighted mixed truth with a positive exponent.** For `h > 0` and `f` continuous,
`∫_{σ/(bt)}^{b} x^{h−1} f(x, σ/(tx)) dx → ∫_0^b x^{h−1} f(x, 0) dx`. -/
theorem tendsto_weightedMixed {b σ h : ℝ} (hb : 0 < b) (hσ : 0 < σ) (hh : 0 < h)
    {f : ℝ → ℝ → ℝ} (hf : Continuous (fun p : ℝ × ℝ ↦ f p.1 p.2)) :
    Tendsto (fun t ↦ ∫ x in Ioo (σ / (b * t)) b, x ^ (h - 1) * f x (σ / (t * x))) atTop
      (𝓝 (∫ x in Ioo 0 b, x ^ (h - 1) * f x 0)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hf.continuousOn (s := Icc (0 : ℝ) b ×ˢ Icc (0 : ℝ) b))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0, 0) ⟨⟨le_rfl, hb.le⟩, ⟨le_rfl, hb.le⟩⟩)
  -- the integrand on the fixed domain `Ioo 0 b`
  set G : ℝ → ℝ → ℝ := fun t x ↦ (Ioi (σ / (b * t))).indicator
    (fun x ↦ x ^ (h - 1) * f x (σ / (t * x))) x with hG
  have hGmeas : ∀ t, Measurable (G t) := fun t ↦ by
    refine Measurable.indicator ?_ measurableSet_Ioi
    exact (measurable_id.pow_const _).mul (hf.measurable.comp (measurable_id.prodMk
      (measurable_const.div (measurable_const.mul measurable_id))))
  have hbound_int : IntegrableOn (fun x : ℝ ↦ C * x ^ (h - 1)) (Ioo 0 b) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
      (by linarith : (-1 : ℝ) < h - 1)).1
    exact (this.mono_set Ioo_subset_Ioc_self).const_mul C
  have key : Tendsto (fun t ↦ ∫ x in Ioo 0 b, G t x) atTop
      (𝓝 (∫ x in Ioo 0 b, x ^ (h - 1) * f x 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ C * x ^ (h - 1))
      (Eventually.of_forall fun t ↦ (hGmeas t).aestronglyMeasurable) ?_ hbound_int ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
      rw [hG]
      beta_reduce
      by_cases hxt : x ∈ Ioi (σ / (b * t))
      · rw [Set.indicator_of_mem hxt, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (rpow_nonneg hx.1.le _), mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg hx.1.le _)
        have hy0 : 0 ≤ σ / (t * x) := div_nonneg hσ.le (mul_pos ht hx.1).le
        have hyb : σ / (t * x) ≤ b := by
          rw [div_le_iff₀ (mul_pos ht hx.1)]
          have := hxt
          rw [mem_Ioi, div_lt_iff₀ (mul_pos hb ht)] at this
          linarith
        have := hC (x, σ / (t * x)) ⟨⟨hx.1.le, hx.2.le⟩, ⟨hy0, hyb⟩⟩
        rwa [Real.norm_eq_abs] at this
      · rw [Set.indicator_of_notMem hxt, norm_zero]
        exact mul_nonneg hC0 (rpow_nonneg hx.1.le _)
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
      have hlim : Tendsto (fun t ↦ σ / (t * x)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_const hx.1)
      have hfl : Tendsto (fun t ↦ f x (σ / (t * x))) atTop (𝓝 (f x 0)) :=
        (hf.tendsto (x, 0)).comp (tendsto_const_nhds.prodMk_nhds hlim)
      refine (hfl.const_mul (x ^ (h - 1))).congr' ?_
      have hev : ∀ᶠ t in atTop, σ / (b * t) < x := by
        have : Tendsto (fun t ↦ σ / (b * t)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hb)
        exact this.eventually_lt_const hx.1
      filter_upwards [hev] with t ht
      rw [hG]
      beta_reduce
      rw [Set.indicator_of_mem (mem_Ioi.mpr ht)]
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hc : 0 < σ / (b * t) := div_pos hσ (mul_pos hb ht)
  rw [hG]
  beta_reduce
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioo_eq hc]

end Laplace.Multi
