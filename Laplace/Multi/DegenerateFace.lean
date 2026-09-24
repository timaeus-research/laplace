/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# A degenerate face: active truth and loss constraints with a one-dimensional optimal face

Astra's three-coordinate example (round 6): the model integral
`I(t) = ∫_{(0,1)³} 1_{xyz > t^{-2}} z² e^{-t³ x y z²}` has the LP
`min α + β + 3ζ` over `α, β, ζ ≥ 0`, `α + β + ζ ≤ 2`, `α + β + 2ζ ≥ 3`, whose optimal face is the
segment `ζ = 1, α + β = 1` (both constraints active, independent normals, dimension one), and
`t⁴ I(t)/log t → 1`: the logarithm of the face dimension. The first step is the product-fibre
factor: the product `xy` of two uniforms on `(0,1)` has density `−log s`
(`lintegral_unitSquare_mul`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

/-- Scaling on an interval: `∫⁻_{(0,1)} G(y x) dx = (1/y) ∫⁻_{(0,y)} G`. -/
theorem lintegral_Ioo_comp_mul_left {y : ℝ} (hy : 0 < y) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x in Ioo (0 : ℝ) 1, G (y * x) = ENNReal.ofReal (1 / y) * ∫⁻ s in Ioo (0 : ℝ) y, G s := by
  have hmap := Real.map_volume_mul_left hy.ne'
  have hpre : (fun x : ℝ ↦ y * x) ⁻¹' Ioo 0 y = Ioo 0 1 := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hy.le, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hy h1, by nlinarith⟩
  have e : ∀ x, (Ioo (0 : ℝ) 1).indicator (fun x ↦ G (y * x)) x =
      (Ioo (0 : ℝ) y).indicator G (y * x) := by
    intro x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · have hx' : y * x ∈ Ioo 0 y := by rw [← hpre] at hx; exact hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · have hx' : y * x ∉ Ioo 0 y := fun h ↦ hx (by rw [← hpre]; exact h)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  simp_rw [e]
  have hg : Measurable fun x : ℝ ↦ y * x := measurable_const_mul y
  rw [← lintegral_map (hG.indicator measurableSet_Ioo) hg, hmap, lintegral_smul_measure, abs_inv,
    abs_of_pos hy, one_div, smul_eq_mul]

/-- The reciprocal integral `∫⁻_{(s,1)} 1/y dy = −log s`. -/
theorem lintegral_inv_Ioo {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∫⁻ y in Ioo s 1, ENNReal.ofReal (1 / y) = ENNReal.ofReal (-log s) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs1,
      integral_one_div_of_pos hs one_pos, one_div, Real.log_inv]
  · have := (intervalIntegral.intervalIntegrable_one_div (μ := volume) (f := fun x ↦ x)
      (fun x hx ↦ ?_) (a := s) (b := 1) continuousOn_id).1
    · exact this.mono_set Ioo_subset_Ioc_self
    · rw [uIcc_of_le hs1] at hx
      exact (hs.trans_le hx.1).ne'
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun y hy ↦ ?_)
    exact div_nonneg zero_le_one (hs.trans hy.1).le

/-- **The product of two uniforms has density `−log s`.** -/
theorem lintegral_unitSquare_mul {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1, G (x * y) =
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (-log s) * G s := by
  have h1 : ∀ y ∈ Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1, G (x * y) =
      ∫⁻ s, (Ioo (0 : ℝ) y).indicator (fun s ↦ ENNReal.ofReal (1 / y) * G s) s := by
    intro y hy
    simp_rw [mul_comm _ y]
    rw [lintegral_Ioo_comp_mul_left hy.1 hG, ← lintegral_const_mul _ hG, ← lintegral_indicator
      measurableSet_Ioo]
  rw [setLIntegral_congr_fun measurableSet_Ioo h1, ← lintegral_indicator measurableSet_Ioo]
  -- the triangle `0 < s < y < 1`
  have hswap : ∫⁻ y, (Ioo (0 : ℝ) 1).indicator (fun y ↦ ∫⁻ s,
      (Ioo (0 : ℝ) y).indicator (fun s ↦ ENNReal.ofReal (1 / y) * G s) s) y =
      ∫⁻ s, ∫⁻ y, (Ioo (0 : ℝ) 1).indicator (fun y ↦
        (Ioo (0 : ℝ) y).indicator (fun s ↦ ENNReal.ofReal (1 / y) * G s) s) y := by
    have hm : Measurable (Function.uncurry fun y s ↦ (Ioo (0 : ℝ) 1).indicator (fun y ↦
        (Ioo (0 : ℝ) y).indicator (fun s ↦ ENNReal.ofReal (1 / y) * G s) s) y) := by
      have hset1 : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Ioo (0 : ℝ) 1} :=
        measurable_fst measurableSet_Ioo
      have hset2 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioo (0 : ℝ) p.1} := by
        refine (measurableSet_lt measurable_const measurable_snd).inter ?_
        exact measurableSet_lt measurable_snd measurable_fst
      have hf : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (1 / p.1) * G p.2 :=
        (ENNReal.measurable_ofReal.comp (measurable_const.div measurable_fst)).mul
          (hG.comp measurable_snd)
      have : (Function.uncurry fun y s ↦ (Ioo (0 : ℝ) 1).indicator (fun y ↦
          (Ioo (0 : ℝ) y).indicator (fun s ↦ ENNReal.ofReal (1 / y) * G s) s) y) =
          fun p : ℝ × ℝ ↦ ({p : ℝ × ℝ | p.1 ∈ Ioo (0 : ℝ) 1} ∩
            {p : ℝ × ℝ | p.2 ∈ Ioo (0 : ℝ) p.1}).indicator
            (fun p ↦ ENNReal.ofReal (1 / p.1) * G p.2) p := by
        funext p
        rcases p with ⟨y, s⟩
        simp only [Function.uncurry_apply_pair]
        by_cases hy : y ∈ Ioo (0 : ℝ) 1
        · by_cases hs : s ∈ Ioo (0 : ℝ) y
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hs,
              Set.indicator_of_mem (show (y, s) ∈ {p : ℝ × ℝ | p.1 ∈ Ioo (0 : ℝ) 1} ∩
                {p : ℝ × ℝ | p.2 ∈ Ioo (0 : ℝ) p.1} from ⟨hy, hs⟩)]
          · rw [Set.indicator_of_mem hy, Set.indicator_of_notMem hs,
              Set.indicator_of_notMem (show (y, s) ∉ {p : ℝ × ℝ | p.1 ∈ Ioo (0 : ℝ) 1} ∩
                {p : ℝ × ℝ | p.2 ∈ Ioo (0 : ℝ) p.1} from fun h ↦ hs h.2)]
        · rw [Set.indicator_of_notMem hy,
            Set.indicator_of_notMem (show (y, s) ∉ {p : ℝ × ℝ | p.1 ∈ Ioo (0 : ℝ) 1} ∩
              {p : ℝ × ℝ | p.2 ∈ Ioo (0 : ℝ) p.1} from fun h ↦ hy h.1)]
      rw [this]
      exact hf.indicator (hset1.inter hset2)
    have := lintegral_lintegral_swap (μ := volume) (ν := volume)
      (hm.aemeasurable (μ := volume.prod volume))
    calc ∫⁻ y, (Ioo (0 : ℝ) 1).indicator (fun y ↦ ∫⁻ s,
          (Ioo (0 : ℝ) y).indicator (fun s ↦ ENNReal.ofReal (1 / y) * G s) s) y
        = ∫⁻ y, ∫⁻ s, (Ioo (0 : ℝ) 1).indicator (fun y ↦
            (Ioo (0 : ℝ) y).indicator (fun s ↦ ENNReal.ofReal (1 / y) * G s) s) y := by
          refine lintegral_congr fun y ↦ ?_
          by_cases hy : y ∈ Ioo (0 : ℝ) 1
          · simp only [Set.indicator_of_mem hy]
          · simp only [Set.indicator_of_notMem hy, lintegral_zero]
      _ = _ := this
  rw [hswap, ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr fun s ↦ ?_
  by_cases hs : s ∈ Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem hs]
    have e : ∀ y, (Ioo (0 : ℝ) 1).indicator (fun y ↦
        (Ioo (0 : ℝ) y).indicator (fun s ↦ ENNReal.ofReal (1 / y) * G s) s) y =
        (Ioo s 1).indicator (fun y ↦ ENNReal.ofReal (1 / y)) y * G s := by
      intro y
      by_cases hy : y ∈ Ioo s 1
      · have hy1 : y ∈ Ioo (0 : ℝ) 1 := ⟨hs.1.trans hy.1, hy.2⟩
        have hsy : s ∈ Ioo (0 : ℝ) y := ⟨hs.1, hy.1⟩
        rw [Set.indicator_of_mem hy1, Set.indicator_of_mem hsy, Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, zero_mul]
        by_cases hy1 : y ∈ Ioo (0 : ℝ) 1
        · rw [Set.indicator_of_mem hy1]
          have hsy : s ∉ Ioo (0 : ℝ) y := fun h ↦ hy ⟨h.2, hy1.2⟩
          rw [Set.indicator_of_notMem hsy]
        · rw [Set.indicator_of_notMem hy1]
    simp_rw [e]
    have hmeas : Measurable fun y : ℝ ↦ (Ioo s 1).indicator (fun y ↦ ENNReal.ofReal (1 / y)) y :=
      (ENNReal.measurable_ofReal.comp (measurable_const.div measurable_id)).indicator
        measurableSet_Ioo
    rw [lintegral_mul_const _ hmeas, lintegral_indicator measurableSet_Ioo,
      lintegral_inv_Ioo hs.1 hs.2.le]
  · rw [Set.indicator_of_notMem hs]
    refine (lintegral_congr fun y ↦ ?_).trans lintegral_zero
    by_cases hy : y ∈ Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hy,
        Set.indicator_of_notMem (fun h : s ∈ Ioo (0 : ℝ) y ↦ hs ⟨h.1, h.2.trans hy.2⟩)]
    · rw [Set.indicator_of_notMem hy]

end Laplace.Multi
