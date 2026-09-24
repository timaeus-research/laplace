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

/-- Scaling on an interval `(0, T)`: `∫⁻_{(0,T)} G(y x) dx = (1/y) ∫⁻_{(0,yT)} G`. -/
theorem lintegral_Ioo_comp_mul_left' {y T : ℝ} (hy : 0 < y) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ x in Ioo (0 : ℝ) T, G (y * x) =
      ENNReal.ofReal (1 / y) * ∫⁻ s in Ioo (0 : ℝ) (y * T), G s := by
  have hmap := Real.map_volume_mul_left hy.ne'
  have hpre : (fun x : ℝ ↦ y * x) ⁻¹' Ioo 0 (y * T) = Ioo 0 T := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hy.le, lt_of_mul_lt_mul_left h2 hy.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hy h1, mul_lt_mul_of_pos_left h2 hy⟩
  have e : ∀ x, (Ioo (0 : ℝ) T).indicator (fun x ↦ G (y * x)) x =
      (Ioo (0 : ℝ) (y * T)).indicator G (y * x) := by
    intro x
    by_cases hx : x ∈ Ioo (0 : ℝ) T
    · have hx' : y * x ∈ Ioo 0 (y * T) := by rw [← hpre] at hx; exact hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · have hx' : y * x ∉ Ioo 0 (y * T) := fun h ↦ hx (by rw [← hpre]; exact h)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  simp_rw [e]
  have hg : Measurable fun x : ℝ ↦ y * x := measurable_const_mul y
  rw [← lintegral_map (hG.indicator measurableSet_Ioo) hg, hmap, lintegral_smul_measure, abs_inv,
    abs_of_pos hy, one_div, smul_eq_mul]

/-- The unit interval as a scaled interval: `∫⁻_{(0,1)} H = (1/t) ∫⁻_{(0,t)} H(u/t)`. -/
theorem lintegral_Ioo_one_eq_scale {t : ℝ} (ht : 0 < t) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ s in Ioo (0 : ℝ) 1, H s = ENNReal.ofReal (1 / t) * ∫⁻ u in Ioo (0 : ℝ) t, H (u / t) := by
  have := lintegral_Ioo_comp_mul_left' ht (T := 1) (G := fun u ↦ H (u / t))
    (hH.comp (measurable_id.div_const t))
  rw [mul_one] at this
  rw [← this]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x _ ↦ ?_
  rw [mul_div_cancel_left₀ _ ht.ne']

/-! ### The three-coordinate example -/

/-- The integrand `1_{xyz > t^{-2}} z² e^{-t³ x y z²}`. -/
noncomputable def degIntegrand (t x y z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ioi (t ^ (-2 : ℝ))).indicator (fun _ ↦ (1 : ℝ)) (x * y * z) *
    (z ^ 2 * exp (-(t ^ 3 * (x * y * z ^ 2)))))

/-- The model integral `I(t)` over the unit cube, iterated. -/
noncomputable def degI (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1, degIntegrand t x y z

/-- The collapsed integrand in the product variable `s = xy`. -/
noncomputable def degG (t z s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ioi (t ^ (-2 : ℝ))).indicator (fun _ ↦ (1 : ℝ)) (s * z) *
    (z ^ 2 * exp (-(t ^ 3 * (s * z ^ 2)))))

/-- The scaled integrand `1_{uv > 1} v² e^{-uv²}`. -/
noncomputable def degK (u v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ioi (1 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (u * v) * (v ^ 2 * exp (-(u * v ^ 2))))

/-- The scaled form `t⁴ I(t) = ∫_{(0,t)²} (log t − log u) 1_{uv>1} v² e^{-uv²} du dv`. -/
noncomputable def degJ (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Ioo (0 : ℝ) t, ∫⁻ u in Ioo (0 : ℝ) t, ENNReal.ofReal (log t - log u) * degK u v

theorem measurable_degG_uncurry (t : ℝ) : Measurable (Function.uncurry (degG t)) := by
  unfold degG Function.uncurry
  refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
  · exact (measurable_const.indicator measurableSet_Ioi).comp (measurable_snd.mul measurable_fst)
  · exact (measurable_fst.pow_const _).mul (Real.measurable_exp.comp
      ((measurable_const.mul (measurable_snd.mul (measurable_fst.pow_const _))).neg))

theorem measurable_degG (t z : ℝ) : Measurable (degG t z) :=
  (measurable_degG_uncurry t).of_uncurry_left

/-- The collapse of `xy`: `I(t) = ∫_0^1 ∫_0^1 (−log s) G_t(z, s) ds dz`. -/
theorem degI_eq_collapse (t : ℝ) :
    degI t = ∫⁻ z in Ioo (0 : ℝ) 1, ∫⁻ s in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (-log s) * degG t z s := by
  unfold degI
  refine setLIntegral_congr_fun measurableSet_Ioo fun z _ ↦ ?_
  change ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1, degG t z (x * y) = _
  exact lintegral_unitSquare_mul (measurable_degG t z)

/-- The scaling of the collapsed integrand: `G_t(v/t, u/t) = t^{-2} K(u, v)`. -/
theorem degG_scale {t : ℝ} (ht : 0 < t) (u v : ℝ) :
    degG t (v / t) (u / t) = ENNReal.ofReal (1 / t ^ 2) * degK u v := by
  unfold degG degK
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e : u / t * (v / t) = u * v / t ^ 2 := by field_simp
  have ht2 : t ^ (-2 : ℝ) = 1 / t ^ 2 := by rw [Real.rpow_neg ht.le, Real.rpow_two, one_div]
  have e2 : t ^ 3 * (u / t * (v / t) ^ 2) = u * v ^ 2 := by field_simp
  have hind : (Ioi (t ^ (-2 : ℝ))).indicator (fun _ ↦ (1 : ℝ)) (u / t * (v / t)) =
      (Ioi (1 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (u * v) := by
    rw [e, ht2]
    by_cases h : 1 < u * v
    · rw [Set.indicator_of_mem (mem_Ioi.mpr h),
        Set.indicator_of_mem (mem_Ioi.mpr ((div_lt_div_iff_of_pos_right (pow_pos ht 2)).mpr h))]
    · rw [Set.indicator_of_notMem (fun h' ↦ h (mem_Ioi.mp h')),
        Set.indicator_of_notMem (fun h' ↦ h ((div_lt_div_iff_of_pos_right (pow_pos ht 2)).mp
          (mem_Ioi.mp h')))]
  rw [hind, e2, div_pow]
  ring

/-- **The scaled form**: `I(t) = t^{-4} J(t)` for `t > 0`. -/
theorem degI_eq_scale {t : ℝ} (ht : 0 < t) : degI t = ENNReal.ofReal (1 / t ^ 4) * degJ t := by
  rw [degI_eq_collapse]
  have hjoint : Measurable (Function.uncurry fun z s ↦ ENNReal.ofReal (-log s) * degG t z s) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_log.comp measurable_snd).neg).mul
      (measurable_degG_uncurry t)
  have hΦ : Measurable fun z ↦ ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (-log s) * degG t z s :=
    hjoint.lintegral_prod_right'
  rw [lintegral_Ioo_one_eq_scale ht hΦ]
  have hinner : ∀ v, ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (-log s) * degG t (v / t) s =
      ENNReal.ofReal (1 / t) * (ENNReal.ofReal (1 / t ^ 2) *
        ∫⁻ u in Ioo (0 : ℝ) t, ENNReal.ofReal (log t - log u) * degK u v) := by
    intro v
    rw [lintegral_Ioo_one_eq_scale ht (hjoint.of_uncurry_left)]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo fun u hu ↦ ?_
    rw [degG_scale ht, Real.log_div hu.1.ne' ht.ne', neg_sub]
    ring
  simp_rw [hinner]
  unfold degJ
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

/-! ### The substitution `w = u v²` and the normalised form -/

/-- The inner integrand after `w = u v²`: `1_{w > v} e^{-w}`. -/
noncomputable def degM (v w : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ioi v).indicator (fun _ ↦ (1 : ℝ)) w * exp (-w))

theorem measurable_degM_uncurry : Measurable (Function.uncurry degM) := by
  unfold degM Function.uncurry
  refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_
    (Real.measurable_exp.comp measurable_snd.neg))
  have : (fun p : ℝ × ℝ ↦ (Ioi p.1).indicator (fun _ ↦ (1 : ℝ)) p.2) =
      {p : ℝ × ℝ | p.1 < p.2}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext p
    by_cases h : p.1 < p.2
    · rw [Set.indicator_of_mem (mem_Ioi.mpr h),
        Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 < p.2} from h)]
    · rw [Set.indicator_of_notMem (fun h' ↦ h (mem_Ioi.mp h')),
        Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 < p.2} from h)]
  rw [this]
  exact measurable_const.indicator (measurableSet_lt measurable_fst measurable_snd)

theorem measurable_degM (v : ℝ) : Measurable (degM v) :=
  measurable_degM_uncurry.of_uncurry_left

/-- `K(w/v², v) = v² · 1_{w > v} e^{-w}`. -/
theorem degK_eq {v : ℝ} (hv : 0 < v) (w : ℝ) :
    degK (w / v ^ 2) v = ENNReal.ofReal (v ^ 2) * degM v w := by
  unfold degK degM
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e : w / v ^ 2 * v = w / v := by field_simp
  have e2 : w / v ^ 2 * v ^ 2 = w := by field_simp
  rw [e, e2]
  have hind : (Ioi (1 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (w / v) =
      (Ioi v).indicator (fun _ ↦ (1 : ℝ)) w := by
    by_cases h : v < w
    · rw [Set.indicator_of_mem (mem_Ioi.mpr ((one_lt_div hv).mpr h)),
        Set.indicator_of_mem (mem_Ioi.mpr h)]
    · rw [Set.indicator_of_notMem (fun h' ↦ h ((one_lt_div hv).mp (mem_Ioi.mp h'))),
        Set.indicator_of_notMem (fun h' ↦ h (mem_Ioi.mp h'))]
  rw [hind]
  ring

/-- **The substitution `w = u v²`**:
`J(t) = ∫_0^t ∫_0^{v²t} (log t − log w + 2 log v) 1_{w>v} e^{-w} dw dv`. -/
theorem degJ_eq_subst (t : ℝ) :
    degJ t = ∫⁻ v in Ioo (0 : ℝ) t, ∫⁻ w in Ioo (0 : ℝ) (v ^ 2 * t),
      ENNReal.ofReal (log t - log w + 2 * log v) * degM v w := by
  unfold degJ
  refine setLIntegral_congr_fun measurableSet_Ioo fun v hv ↦ ?_
  have hv2 : 0 < v ^ 2 := pow_pos hv.1 2
  have hG : Measurable fun w ↦ ENNReal.ofReal (log t - log w + 2 * log v) * degM v w :=
    (ENNReal.measurable_ofReal.comp ((measurable_const.sub Real.measurable_log).add
      measurable_const)).mul (measurable_degM v)
  have key := lintegral_Ioo_comp_mul_left' hv2 (T := t)
    (G := fun w ↦ ENNReal.ofReal (log t - log w + 2 * log v) * degM v w) hG
  calc ∫⁻ u in Ioo (0 : ℝ) t, ENNReal.ofReal (log t - log u) * degK u v
      = ∫⁻ u in Ioo (0 : ℝ) t, ENNReal.ofReal (v ^ 2) *
          (ENNReal.ofReal (log t - log (v ^ 2 * u) + 2 * log v) * degM v (v ^ 2 * u)) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun u hu ↦ ?_
        have := degK_eq hv.1 (v ^ 2 * u)
        rw [mul_div_cancel_left₀ _ hv2.ne'] at this
        rw [this, Real.log_mul hv2.ne' hu.1.ne', Real.log_pow]
        push_cast
        rw [show log t - (2 * log v + log u) + 2 * log v = log t - log u by ring]
        ring
    _ = ENNReal.ofReal (v ^ 2) * ∫⁻ u in Ioo (0 : ℝ) t,
          ENNReal.ofReal (log t - log (v ^ 2 * u) + 2 * log v) * degM v (v ^ 2 * u) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (v ^ 2) * (ENNReal.ofReal (1 / v ^ 2) * ∫⁻ w in Ioo (0 : ℝ) (v ^ 2 * t),
          ENNReal.ofReal (log t - log w + 2 * log v) * degM v w) := by rw [key]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hv2.le, mul_one_div_cancel hv2.ne',
          ENNReal.ofReal_one, one_mul]

/-- The normalised scaled form `J(t)/log t`. -/
noncomputable def degN (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Ioo (0 : ℝ) t, ∫⁻ w in Ioo (0 : ℝ) (v ^ 2 * t),
    ENNReal.ofReal ((log t - log w + 2 * log v) / log t) * degM v w

theorem degJ_div_log {t : ℝ} (ht : 1 < t) : degJ t / ENNReal.ofReal (log t) = degN t := by
  have hlt : 0 < log t := Real.log_pos ht
  have hne : (ENNReal.ofReal (log t))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hlt).ne'
  rw [degJ_eq_subst, ENNReal.div_eq_inv_mul, ← lintegral_const_mul' _ _ hne]
  unfold degN
  refine setLIntegral_congr_fun measurableSet_Ioo fun v _ ↦ ?_
  rw [← lintegral_const_mul' _ _ hne]
  refine setLIntegral_congr_fun measurableSet_Ioo fun w _ ↦ ?_
  rw [← mul_assoc, ← ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_div_of_pos hlt]

/-! ### Dominated convergence: the elementary bounds and the limit integral -/

/-- `|log v| ≤ v + 2/√v` for `v > 0`. -/
theorem abs_log_le_add_two_div_sqrt {v : ℝ} (hv : 0 < v) : |log v| ≤ v + 2 / √v := by
  have hsq : 0 < √v := Real.sqrt_pos.mpr hv
  have h1 : log v ≤ v - 1 := Real.log_le_sub_one_of_pos hv
  have h2 : log (1 / √v) ≤ 1 / √v - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : log v = 2 * log √v := by rw [Real.log_sqrt hv.le]; ring
  have h4 : log (1 / √v) = -log √v := by rw [one_div, Real.log_inv]
  have h5 : 2 / √v = 2 * (1 / √v) := by ring
  rw [h4] at h2
  rw [abs_le]
  constructor
  · linarith [h3, h2, h5, hv]
  · linarith [h1, show (0 : ℝ) ≤ 2 / √v by positivity]

/-- The log moment on `(0, w)`: `∫_0^w |log v| dv ≤ w²/2 + 4√w`. -/
theorem lintegral_abs_log_Ioo_le {w : ℝ} (hw : 0 < w) :
    ∫⁻ v in Ioo (0 : ℝ) w, ENNReal.ofReal |log v| ≤ ENNReal.ofReal (w ^ 2 / 2 + 4 * √w) := by
  calc ∫⁻ v in Ioo (0 : ℝ) w, ENNReal.ofReal |log v|
      ≤ ∫⁻ v in Ioo (0 : ℝ) w, ENNReal.ofReal (v + 2 * v ^ (-(1 / 2 : ℝ))) := by
        refine setLIntegral_mono' measurableSet_Ioo fun v hv ↦ ENNReal.ofReal_le_ofReal ?_
        calc |log v| ≤ v + 2 / √v := abs_log_le_add_two_div_sqrt hv.1
          _ = v + 2 * v ^ (-(1 / 2 : ℝ)) := by
            rw [Real.rpow_neg hv.1.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    _ = ENNReal.ofReal (w ^ 2 / 2 + 4 * √w) := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · congr 1
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hw.le,
            intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
              ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 2),
            intervalIntegral.integral_const_mul, integral_id, integral_rpow (Or.inl (by norm_num))]
          rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num, Real.zero_rpow (by norm_num),
            Real.sqrt_eq_rpow]
          ring
        · refine (intervalIntegral.intervalIntegrable_id.add
            ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 2) (a := 0)
            (b := w)).1.mono_set Ioo_subset_Ioc_self
        · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun v hv ↦ ?_)
          have := hv.1
          positivity

/-- The limit integral `∫_0^∞ ∫_v^∞ e^{-w} dw dv = 1`. -/
theorem lintegral_degM_eq_one :
    ∫⁻ v in Ioi (0 : ℝ), ∫⁻ w in Ioi (0 : ℝ), degM v w = 1 := by
  have hinner : ∀ v ∈ Ioi (0 : ℝ), ∫⁻ w in Ioi (0 : ℝ), degM v w = ENNReal.ofReal (exp (-v)) := by
    intro v hv
    unfold degM
    have e : ∀ w, ENNReal.ofReal ((Ioi v).indicator (fun _ ↦ (1 : ℝ)) w * exp (-w)) =
        (Ioi v).indicator (fun w ↦ ENNReal.ofReal (exp (-w))) w := by
      intro w
      by_cases h : w ∈ Ioi v
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul, ENNReal.ofReal_zero]
    simp_rw [e]
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Set.Ioi_inter_Ioi, sup_of_le_left (le_of_lt hv), ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_exp_neg_Ioi v) (Eventually.of_forall fun _ ↦ (exp_pos _).le),
      integral_exp_neg_Ioi]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_neg_Ioi 0) (Eventually.of_forall fun _ ↦ (exp_pos _).le),
    integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

/-! ### Dominated convergence on the plane -/

/-- The domain of the normalised integrand at time `t`: `0 < v < t`, `0 < w < v² t`. -/
def degDom (t : ℝ) : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < t ∧ 0 < p.2 ∧ p.2 < p.1 ^ 2 * t}

theorem measurableSet_degDom (t : ℝ) : MeasurableSet (degDom t) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd ((measurable_fst.pow_const 2).mul_const t))))

/-- The normalised integrand on the plane. -/
noncomputable def degΦ (t : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  (degDom t).indicator
    (fun p ↦ ENNReal.ofReal ((log t - log p.2 + 2 * log p.1) / log t) * degM p.1 p.2) p

theorem measurable_degΦ (t : ℝ) : Measurable (degΦ t) := by
  unfold degΦ
  refine Measurable.indicator ?_ (measurableSet_degDom t)
  refine (ENNReal.measurable_ofReal.comp ?_).mul
    (measurable_degM_uncurry : Measurable fun p : ℝ × ℝ ↦ degM p.1 p.2)
  exact ((measurable_const.sub (Real.measurable_log.comp measurable_snd)).add
    (measurable_const.mul (Real.measurable_log.comp measurable_fst))).div_const _

/-- The normalised form is the planar integral. -/
theorem degN_eq_lintegral_prod (t : ℝ) : degN t = ∫⁻ p, degΦ t p ∂(volume.prod volume) := by
  rw [lintegral_prod _ (measurable_degΦ t).aemeasurable]
  unfold degN
  rw [← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr fun v ↦ ?_
  by_cases hv : v ∈ Ioo (0 : ℝ) t
  · rw [Set.indicator_of_mem hv, ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun w ↦ ?_
    unfold degΦ
    by_cases hw : w ∈ Ioo (0 : ℝ) (v ^ 2 * t)
    · rw [Set.indicator_of_mem hw,
        Set.indicator_of_mem (show (v, w) ∈ degDom t from ⟨hv.1, hv.2, hw.1, hw.2⟩)]
    · rw [Set.indicator_of_notMem hw,
        Set.indicator_of_notMem (show (v, w) ∉ degDom t from fun h ↦ hw ⟨h.2.2.1, h.2.2.2⟩)]
  · rw [Set.indicator_of_notMem hv]
    symm
    refine (lintegral_congr fun w ↦ ?_).trans lintegral_zero
    unfold degΦ
    exact Set.indicator_of_notMem (fun h : (v, w) ∈ degDom t ↦ hv ⟨h.1, h.2.1⟩) _

/-- The open quadrant. -/
def degQuad : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}

theorem measurableSet_degQuad : MeasurableSet degQuad :=
  (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)

/-- The dominating function `1_{0<v<w} (1 + 3w + 2w^{-1/2} + 4v^{-1/2}) e^{-w}`. -/
noncomputable def degΨ (p : ℝ × ℝ) : ℝ≥0∞ :=
  degQuad.indicator (fun p ↦ ENNReal.ofReal
    ((1 + 3 * p.2 + 2 * p.2 ^ (-(1 / 2 : ℝ)) + 4 * p.1 ^ (-(1 / 2 : ℝ))) * exp (-p.2))) p

theorem measurable_degΨ : Measurable degΨ := by
  unfold degΨ
  refine Measurable.indicator (ENNReal.measurable_ofReal.comp (Measurable.mul ?_
    (Real.measurable_exp.comp measurable_snd.neg))) measurableSet_degQuad
  exact ((measurable_const.add (measurable_const.mul measurable_snd)).add
    (measurable_const.mul (measurable_snd.pow_const _))).add
    (measurable_const.mul (measurable_fst.pow_const _))

/-- Domination for `t ≥ e`. -/
theorem degΦ_le_degΨ {t : ℝ} (ht : exp 1 ≤ t) (p : ℝ × ℝ) : degΦ t p ≤ degΨ p := by
  have hlt : 1 ≤ log t := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (exp_pos 1) ht
  have ht0 : 0 < t := (exp_pos 1).trans_le ht
  unfold degΦ
  by_cases hp : p ∈ degDom t
  · rw [Set.indicator_of_mem hp]
    obtain ⟨hv, -, hw, hwv⟩ := hp
    by_cases hvw : p.1 < p.2
    · unfold degΨ
      rw [Set.indicator_of_mem (show p ∈ degQuad from ⟨hv, hvw⟩)]
      unfold degM
      rw [Set.indicator_of_mem (mem_Ioi.mpr hvw), one_mul]
      have hN0 : 0 ≤ log t - log p.2 + 2 * log p.1 := by
        have := Real.log_lt_log hw hwv
        rw [Real.log_mul (pow_pos hv 2).ne' ht0.ne', Real.log_pow] at this
        push_cast at this
        linarith
      rw [← ENNReal.ofReal_mul (div_nonneg hN0 (zero_le_one.trans hlt))]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
      have hw' := abs_log_le_add_two_div_sqrt hw
      have hv' := abs_log_le_add_two_div_sqrt hv
      have hN : log t - log p.2 + 2 * log p.1 ≤ log t * (1 + |log p.2| + 2 * |log p.1|) := by
        nlinarith [neg_abs_le (log p.2), le_abs_self (log p.1), abs_nonneg (log p.2),
          abs_nonneg (log p.1), hlt]
      rw [div_le_iff₀ (zero_lt_one.trans_le hlt)]
      calc log t - log p.2 + 2 * log p.1 ≤ log t * (1 + |log p.2| + 2 * |log p.1|) := hN
        _ ≤ log t * (1 + (p.2 + 2 / √p.2) + 2 * (p.1 + 2 / √p.1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans hlt)
            linarith
        _ ≤ (1 + 3 * p.2 + 2 * p.2 ^ (-(1 / 2 : ℝ)) + 4 * p.1 ^ (-(1 / 2 : ℝ))) * log t := by
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ (zero_le_one.trans hlt)
            rw [Real.rpow_neg hw.le, Real.rpow_neg hv.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
              div_eq_mul_inv, div_eq_mul_inv]
            linarith [hvw.le]
    · unfold degM
      rw [Set.indicator_of_notMem (fun h ↦ hvw (mem_Ioi.mp h)), zero_mul, ENNReal.ofReal_zero,
        mul_zero]
      exact zero_le
  · rw [Set.indicator_of_notMem hp]
    exact zero_le

/-- The inner integral of the dominating function. -/
theorem lintegral_degΨ_inner {w : ℝ} (hw : 0 < w) :
    ∫⁻ v, degΨ (v, w) = ENNReal.ofReal ((w + 3 * w ^ 2 + 10 * √w) * exp (-w)) := by
  have e : ∀ v, degΨ (v, w) = (Ioo (0 : ℝ) w).indicator (fun v ↦ ENNReal.ofReal
      ((1 + 3 * w + 2 * w ^ (-(1 / 2 : ℝ)) + 4 * v ^ (-(1 / 2 : ℝ))) * exp (-w))) v := by
    intro v
    unfold degΨ
    by_cases hv : v ∈ Ioo (0 : ℝ) w
    · rw [Set.indicator_of_mem (show (v, w) ∈ degQuad from ⟨hv.1, hv.2⟩), Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem (show (v, w) ∉ degQuad from fun h ↦ hv ⟨h.1, h.2⟩),
        Set.indicator_of_notMem hv]
  have hint : IntervalIntegrable (fun v : ℝ ↦ 4 * v ^ (-(1 / 2 : ℝ))) volume 0 w :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 4
  have e2 : ∀ v : ℝ, (1 + 3 * w + 2 * w ^ (-(1 / 2 : ℝ)) + 4 * v ^ (-(1 / 2 : ℝ))) * exp (-w) =
      (1 + 3 * w + 2 * w ^ (-(1 / 2 : ℝ))) * exp (-w) + exp (-w) * (4 * v ^ (-(1 / 2 : ℝ))) := by
    intro v
    ring
  simp_rw [e, e2]
  rw [lintegral_indicator measurableSet_Ioo, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hw.le,
      intervalIntegral.integral_add intervalIntegrable_const (hint.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num, Real.zero_rpow (by norm_num),
      Real.rpow_neg hw.le, ← Real.sqrt_eq_rpow, sub_zero, sub_zero, smul_eq_mul]
    have hsq : √w * √w = w := Real.mul_self_sqrt hw.le
    have hsq0 : 0 < √w := Real.sqrt_pos.mpr hw
    have hinv : w * (√w)⁻¹ = √w := by
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hsq0.ne', hsq]
    linear_combination (2 * exp (-w)) * hinv
  · exact ((intervalIntegrable_const.add (hint.const_mul _)).1).mono_set Ioo_subset_Ioc_self
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun v hv ↦ ?_)
    have := hv.1
    positivity

/-- The dominating function has finite integral. -/
theorem lintegral_degΨ_ne_top : ∫⁻ p, degΨ p ∂(volume.prod volume) ≠ ⊤ := by
  rw [lintegral_prod_symm _ measurable_degΨ.aemeasurable]
  have e : ∀ w, ∫⁻ v, degΨ (v, w) = (Ioi (0 : ℝ)).indicator
      (fun w ↦ ENNReal.ofReal ((w + 3 * w ^ 2 + 10 * √w) * exp (-w))) w := by
    intro w
    by_cases hw : w ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hw, lintegral_degΨ_inner hw]
    · rw [Set.indicator_of_notMem hw]
      refine (lintegral_congr fun v ↦ ?_).trans lintegral_zero
      unfold degΨ
      exact Set.indicator_of_notMem
        (fun h : (v, w) ∈ degQuad ↦ hw (mem_Ioi.mpr (h.1.trans h.2))) _
  simp_rw [e]
  rw [lintegral_indicator measurableSet_Ioi]
  have hint : IntegrableOn (fun w : ℝ ↦ (w + 3 * w ^ 2 + 10 * √w) * exp (-w)) (Ioi 0) := by
    have h1 := Real.GammaIntegral_convergent (s := 2) (by norm_num)
    have h2 := Real.GammaIntegral_convergent (s := 3) (by norm_num)
    have h3 := Real.GammaIntegral_convergent (s := 3 / 2) (by norm_num)
    refine ((h1.add (h2.const_mul 3)).add (h3.const_mul 10)).congr_fun (fun w _ ↦ ?_)
      measurableSet_Ioi
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num,
      show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, Real.rpow_one, Real.rpow_two, ← Real.sqrt_eq_rpow,
      Pi.add_apply]
    ring
  exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hint.hasFiniteIntegral).ne

/-- The limit integrand `1_{0<v<w} e^{-w}` on the open quadrant. -/
noncomputable def degΦlim (p : ℝ × ℝ) : ℝ≥0∞ :=
  {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2}.indicator (fun p ↦ degM p.1 p.2) p

theorem lintegral_degΦlim : ∫⁻ p, degΦlim p ∂(volume.prod volume) = 1 := by
  have hmeas : Measurable degΦlim :=
    (measurable_degM_uncurry : Measurable fun p : ℝ × ℝ ↦ degM p.1 p.2).indicator
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_const measurable_snd))
  rw [lintegral_prod _ hmeas.aemeasurable, ← lintegral_degM_eq_one,
    ← lintegral_indicator measurableSet_Ioi (f := fun v ↦ ∫⁻ w in Ioi (0 : ℝ), degM v w)]
  refine lintegral_congr fun v ↦ ?_
  by_cases hv : v ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hv, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun w ↦ ?_
    unfold degΦlim
    by_cases hw : w ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hw,
        Set.indicator_of_mem (show (v, w) ∈ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} from ⟨hv, hw⟩)]
    · rw [Set.indicator_of_notMem hw,
        Set.indicator_of_notMem (show (v, w) ∉ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} from
          fun h ↦ hw h.2)]
  · rw [Set.indicator_of_notMem hv]
    refine (lintegral_congr fun w ↦ ?_).trans lintegral_zero
    unfold degΦlim
    exact Set.indicator_of_notMem
      (fun h : (v, w) ∈ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} ↦ hv h.1) _

/-- **The normalised form converges to `1`** (dominated convergence on the plane). -/
theorem tendsto_degN : Tendsto degN atTop (𝓝 1) := by
  have key := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.prod volume)
    (l := atTop) (F := degΦ) (f := degΦlim) degΨ
    (Eventually.of_forall fun t ↦ measurable_degΦ t)
    (by
      filter_upwards [eventually_ge_atTop (exp 1)] with t ht
      exact Eventually.of_forall (degΦ_le_degΨ ht))
    lintegral_degΨ_ne_top (Eventually.of_forall fun p ↦ ?_)
  · rw [lintegral_degΦlim] at key
    exact key.congr' (Eventually.of_forall fun t ↦ (degN_eq_lintegral_prod t).symm)
  · by_cases hp : 0 < p.1 ∧ 0 < p.2
    · obtain ⟨hv, hw⟩ := hp
      unfold degΦlim
      rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} from ⟨hv, hw⟩)]
      have h1 : Tendsto (fun t ↦ (log t - log p.2 + 2 * log p.1) / log t) atTop (𝓝 1) := by
        have h0 : Tendsto (fun t ↦ (2 * log p.1 - log p.2) / log t + 1) atTop (𝓝 (0 + 1)) :=
          (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add tendsto_const_nhds
        rw [zero_add] at h0
        refine h0.congr' ?_
        filter_upwards [eventually_gt_atTop 1] with t ht
        have := (Real.log_pos ht).ne'
        field_simp
        ring
      have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (b := degM p.1 p.2)
        (Or.inl (by rw [ENNReal.ofReal_one]; exact one_ne_zero))
      rw [ENNReal.ofReal_one, one_mul] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop p.1, eventually_gt_atTop (p.2 / p.1 ^ 2)] with t ht1 ht2
      unfold degΦ
      rw [div_lt_iff₀ (pow_pos hv 2)] at ht2
      rw [Set.indicator_of_mem (show p ∈ degDom t from ⟨hv, ht1, hw, by rwa [mul_comm]⟩)]
    · have h0 : ∀ t, degΦ t p = 0 := fun t ↦ by
        unfold degΦ
        exact Set.indicator_of_notMem (fun h ↦ hp ⟨h.1, h.2.2.1⟩) _
      unfold degΦlim
      rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} from hp)]
      simp only [h0]
      exact tendsto_const_nhds

/-- **The degenerate face.** For the three-coordinate model integral
`I(t) = ∫_{(0,1)³} 1_{xyz > t^{-2}} z² e^{-t³xyz²}`, whose LP has both the truth and the loss
constraint active with a one-dimensional optimal face, `t⁴ I(t)/log t → 1`. -/
theorem tendsto_degI : Tendsto (fun t ↦ t ^ 4 / log t * (degI t).toReal) atTop (𝓝 1) := by
  have h := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp tendsto_degN
  rw [ENNReal.toReal_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1, tendsto_degN.eventually (gt_mem_nhds ENNReal.one_lt_top)]
    with t ht hN
  have hlt : 0 < log t := Real.log_pos ht
  have ht0 : 0 < t := one_pos.trans ht
  have hJ : degJ t = ENNReal.ofReal (log t) * degN t :=
    ((ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr hlt).ne' ENNReal.ofReal_ne_top).mp
      (degJ_div_log ht).symm).symm
  simp only [Function.comp_apply]
  rw [degI_eq_scale ht0, hJ, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hlt.le]
  field_simp

end Laplace.Multi
