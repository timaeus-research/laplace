/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NewtonEdge
import Laplace.Multi.ToyCrossover

/-!
# A wall with two layers

`F(x, s) = x⁶ + x⁴s² + x²s⁶` has a Newton polygon with TWO lower edges, `(6,0)–(4,2)` with weights
`(1/6, 1/6)` and `(4,2)–(2,6)` with weights `(1/5, 1/10)`. The Newton-edge theorem applies to each
edge with the remaining monomial as the higher-weight remainder, so the wall at `s = 0` has two
layers: along `s = σ t^{-1/6}` the energy statistic converges to the edge-1 crossover, which is the
wall model `G_{2,1,0}(σ²)` running from the wall type `1/6` to the intermediate type `1/4`
(`twoLayer_layer1`, `twoLayer_layer1_zero`, `twoLayer_layer1_atTop`); along `s = σ t^{-1/10}` it
converges to the edge-2 crossover, which is the toy crossover `G(σ⁵)` running from `1/4` to the
chamber type `1/2` (`twoLayer_layer2`, `twoLayer_layer2_zero`, `twoLayer_layer2_atTop`). Between
the layers the posterior sits on an intermediate plateau, the type of the shared vertex `x⁴s²`, a
geometry that is neither chamber's. The layers are the exceptional divisors over the wall point,
one per edge (germbij_slop S13).
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The two-layer family. -/
noncomputable def twoLayerF (x s : ℝ) : ℝ := x ^ 6 + x ^ 4 * s ^ 2 + x ^ 2 * s ^ 6

/-! ### Edge 1: `x⁶ + x⁴s²`, remainder `x²s⁶`, weights `(1/6, 1/6)` -/

theorem quasiHomog_edge1 : QuasiHomog (fun x s ↦ x ^ 6 + x ^ 4 * s ^ 2) (1 / 6) (1 / 6) := by
  intro l hl x s
  have h6 : (l ^ (1 / 6 : ℝ)) ^ 6 = l := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
    norm_num
  simp only
  have : (l ^ (1 / 6 : ℝ) * x) ^ 6 + (l ^ (1 / 6 : ℝ) * x) ^ 4 * (l ^ (1 / 6 : ℝ) * s) ^ 2 =
      (l ^ (1 / 6 : ℝ)) ^ 6 * (x ^ 6 + x ^ 4 * s ^ 2) := by ring
  rw [this, h6]

theorem twoLayer_edge1_data (σ : ℝ) :
    EdgeData (fun x s ↦ x ^ 6 + x ^ 4 * s ^ 2) (fun x s ↦ x ^ 2 * s ^ 6) (1 / 6) (1 / 6) σ where
  hα := by norm_num
  quasi := quasiHomog_edge1
  E_cont := by unfold Function.uncurry; fun_prop
  R_cont := by unfold Function.uncurry; fun_prop
  E_nonneg := fun u s ↦ by positivity
  R_nonneg := fun x s ↦ by positivity
  R_lim := fun u ↦ by
    have h : Tendsto (fun t : ℝ ↦ σ ^ 6 * u ^ 2 * t ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (σ ^ 6 * u ^ 2)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have h8 : (t ^ (-(1 / 6 : ℝ))) ^ 8 = t ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      norm_num
    have h1 : t * t ^ (-(4 / 3 : ℝ)) = t ^ (-(1 / 3 : ℝ)) := by
      have := Real.rpow_add ht 1 (-(4 / 3 : ℝ))
      rw [Real.rpow_one] at this
      rw [← this]
      norm_num
    calc σ ^ 6 * u ^ 2 * t ^ (-(1 / 3 : ℝ)) = σ ^ 6 * u ^ 2 * (t * t ^ (-(4 / 3 : ℝ))) := by rw [h1]
      _ = σ ^ 6 * u ^ 2 * (t * (t ^ (-(1 / 6 : ℝ))) ^ 8) := by rw [h8]
      _ = t * ((t ^ (-(1 / 6 : ℝ)) * u) ^ 2 * (σ * t ^ (-(1 / 6 : ℝ))) ^ 6) := by ring
  E_int := by
    have := integrable_abs_pow_mul_exp_neg_mul_pow one_pos 3 (by norm_num) 0
    simp only [pow_zero, one_mul] at this
    refine this.mono' (by fun_prop) (Filter.Eventually.of_forall fun u ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ u ^ 4 * σ ^ 2 := by positivity
    norm_num
    linarith
  EE_int := by
    have h6 := integrable_abs_pow_mul_exp_neg_mul_pow one_pos 3 (by norm_num) 6
    have h4 := (integrable_abs_pow_mul_exp_neg_mul_pow one_pos 3 (by norm_num) 4).const_mul (σ ^ 2)
    simp only [one_mul] at h6 h4
    refine (h6.add h4).mono' (by fun_prop) (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [Pi.add_apply]
    have hE : 0 ≤ u ^ 6 + u ^ 4 * σ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hE (Real.exp_pos _).le)]
    have hexp : Real.exp (-(u ^ 6 + u ^ 4 * σ ^ 2)) ≤ Real.exp (-u ^ (2 * 3)) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ u ^ 4 * σ ^ 2 := by positivity
      norm_num
      linarith
    have h6' : |u| ^ 6 = u ^ 6 := by rw [show (6 : ℕ) = 2 * 3 by rfl, abs_pow_even]
    have h4' : |u| ^ 4 = u ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, abs_pow_even]
    rw [h6', h4']
    calc (u ^ 6 + u ^ 4 * σ ^ 2) * Real.exp (-(u ^ 6 + u ^ 4 * σ ^ 2))
        ≤ (u ^ 6 + u ^ 4 * σ ^ 2) * Real.exp (-u ^ (2 * 3)) :=
          mul_le_mul_of_nonneg_left hexp hE
      _ = u ^ 6 * Real.exp (-u ^ (2 * 3)) + σ ^ 2 * (u ^ 4 * Real.exp (-u ^ (2 * 3))) := by ring

/-- The edge-1 crossover is the wall model `G_{2,1,0}` in the variable `σ²`. -/
theorem edge1_limit_eq (σ : ℝ) :
    (∫ u, (u ^ 6 + u ^ 4 * σ ^ 2) * Real.exp (-(u ^ 6 + u ^ 4 * σ ^ 2))) /
      (∫ u, Real.exp (-(u ^ 6 + u ^ 4 * σ ^ 2))) = wallCross 2 1 0 (σ ^ 2) := by
  unfold wallCross wallW
  congr 1 <;> refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_) <;> simp only <;>
    norm_num <;> ring_nf

/-- **Layer 1**: along `s = σ t^{-1/6}` the energy statistic converges to `G_{2,1,0}(σ²)`. -/
theorem twoLayer_layer1 {χ : ℝ → ℝ} (hχ : Cutoff χ) (σ : ℝ) :
    Tendsto (fun t ↦ edgeEnergy χ twoLayerF (σ * t ^ (-(1 / 6 : ℝ))) t) atTop
      (𝓝 (wallCross 2 1 0 (σ ^ 2))) := by
  have h := (twoLayer_edge1_data σ).tendsto_energy hχ
  rw [edge1_limit_eq] at h
  refine h.congr' (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [edgeEnergy, twoLayerF]

theorem twoLayer_layer1_zero : wallCross 2 1 0 ((0 : ℝ) ^ 2) = 1 / 6 := by
  rw [zero_pow (by norm_num), wallCross_zero 2 1 0 (by norm_num)]
  norm_num

theorem twoLayer_layer1_atTop :
    Tendsto (fun σ : ℝ ↦ wallCross 2 1 0 (σ ^ 2)) atTop (𝓝 (1 / 4)) := by
  have := (tendsto_wallCross_atTop 2 1 0 (by norm_num)).comp
    (tendsto_pow_atTop (n := 2) (by norm_num))
  norm_num at this
  exact this

/-! ### Edge 2: `x⁴s² + x²s⁶`, remainder `x⁶`, weights `(1/5, 1/10)` -/

theorem quasiHomog_edge2 :
    QuasiHomog (fun x s ↦ x ^ 4 * s ^ 2 + x ^ 2 * s ^ 6) (1 / 5) (1 / 10) := by
  intro l hl x s
  have h1 : (l ^ (1 / 5 : ℝ)) ^ 4 * (l ^ (1 / 10 : ℝ)) ^ 2 = l := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hl.le, ← Real.rpow_mul hl.le,
      ← Real.rpow_add hl]
    norm_num
  have h2 : (l ^ (1 / 5 : ℝ)) ^ 2 * (l ^ (1 / 10 : ℝ)) ^ 6 = l := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hl.le, ← Real.rpow_mul hl.le,
      ← Real.rpow_add hl]
    norm_num
  simp only
  calc (l ^ (1 / 5 : ℝ) * x) ^ 4 * (l ^ (1 / 10 : ℝ) * s) ^ 2 +
        (l ^ (1 / 5 : ℝ) * x) ^ 2 * (l ^ (1 / 10 : ℝ) * s) ^ 6
      = ((l ^ (1 / 5 : ℝ)) ^ 4 * (l ^ (1 / 10 : ℝ)) ^ 2) * (x ^ 4 * s ^ 2) +
        ((l ^ (1 / 5 : ℝ)) ^ 2 * (l ^ (1 / 10 : ℝ)) ^ 6) * (x ^ 2 * s ^ 6) := by ring
    _ = l * (x ^ 4 * s ^ 2 + x ^ 2 * s ^ 6) := by rw [h1, h2]; ring

theorem twoLayer_edge2_data {σ : ℝ} (hσ : σ ≠ 0) :
    EdgeData (fun x s ↦ x ^ 4 * s ^ 2 + x ^ 2 * s ^ 6) (fun x _ ↦ x ^ 6) (1 / 5) (1 / 10) σ where
  hα := by norm_num
  quasi := quasiHomog_edge2
  E_cont := by unfold Function.uncurry; fun_prop
  R_cont := by unfold Function.uncurry; fun_prop
  E_nonneg := fun u s ↦ by positivity
  R_nonneg := fun x _ ↦ by positivity
  R_lim := fun u ↦ by
    have h : Tendsto (fun t : ℝ ↦ u ^ 6 * t ^ (-(1 / 5 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)).const_mul (u ^ 6)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have h6 : (t ^ (-(1 / 5 : ℝ))) ^ 6 = t ^ (-(6 / 5 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      norm_num
    have h1 : t * t ^ (-(6 / 5 : ℝ)) = t ^ (-(1 / 5 : ℝ)) := by
      have := Real.rpow_add ht 1 (-(6 / 5 : ℝ))
      rw [Real.rpow_one] at this
      rw [← this]
      norm_num
    calc u ^ 6 * t ^ (-(1 / 5 : ℝ)) = u ^ 6 * (t * t ^ (-(6 / 5 : ℝ))) := by rw [h1]
      _ = u ^ 6 * (t * (t ^ (-(1 / 5 : ℝ))) ^ 6) := by rw [h6]
      _ = t * (t ^ (-(1 / 5 : ℝ)) * u) ^ 6 := by ring
  E_int := by
    have hσ2 : 0 < σ ^ 2 := by positivity
    have := integrable_abs_pow_mul_exp_neg_mul_pow hσ2 2 (by norm_num) 0
    simp only [pow_zero, one_mul] at this
    refine this.mono' (by fun_prop) (Filter.Eventually.of_forall fun u ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ u ^ 2 * σ ^ 6 := by positivity
    norm_num
    linarith
  EE_int := by
    have hσ2 : 0 < σ ^ 2 := by positivity
    have h4 := (integrable_abs_pow_mul_exp_neg_mul_pow hσ2 2 (by norm_num) 4).const_mul (σ ^ 2)
    have h2 := (integrable_abs_pow_mul_exp_neg_mul_pow hσ2 2 (by norm_num) 2).const_mul (σ ^ 6)
    refine (h4.add h2).mono' (by fun_prop) (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [Pi.add_apply]
    have hE : 0 ≤ u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hE (Real.exp_pos _).le)]
    have hexp : Real.exp (-(u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6)) ≤
        Real.exp (-(σ ^ 2 * u ^ (2 * 2))) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ u ^ 2 * σ ^ 6 := by positivity
      norm_num
      linarith
    have h4' : |u| ^ 4 = u ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, abs_pow_even]
    have h2' : |u| ^ 2 = u ^ 2 := sq_abs u
    rw [h4', h2']
    calc (u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6) * Real.exp (-(u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6))
        ≤ (u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6) * Real.exp (-(σ ^ 2 * u ^ (2 * 2))) :=
          mul_le_mul_of_nonneg_left hexp hE
      _ = σ ^ 2 * (u ^ 4 * Real.exp (-(σ ^ 2 * u ^ (2 * 2)))) +
          σ ^ 6 * (u ^ 2 * Real.exp (-(σ ^ 2 * u ^ (2 * 2)))) := by ring

/-- The edge-2 crossover is the toy crossover in the variable `σ⁵`: `u = σ^{-1/2} y` turns
`σ²u⁴ + σ⁶u²` into `y⁴ + σ⁵y²`. -/
theorem edge2_limit_eq {σ : ℝ} (hσ : 0 < σ) :
    (∫ u, (u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6) * Real.exp (-(u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6))) /
      (∫ u, Real.exp (-(u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6))) = crossover (σ ^ 5) := by
  set c : ℝ := σ ^ (-(1 / 2 : ℝ)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hσ _
  have hc2 : c ^ 2 * σ = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hσ.le]
    norm_num
    rw [Real.rpow_neg_one, inv_mul_cancel₀ hσ.ne']
  have hpt : ∀ y : ℝ, (c * y) ^ 4 * σ ^ 2 + (c * y) ^ 2 * σ ^ 6 = y ^ 4 + σ ^ 5 * y ^ 2 := by
    intro y
    have : (c * y) ^ 4 * σ ^ 2 + (c * y) ^ 2 * σ ^ 6 =
        (c ^ 2 * σ) ^ 2 * y ^ 4 + (c ^ 2 * σ) * (σ ^ 5 * y ^ 2) := by ring
    rw [this, hc2]
    ring
  have hn := Measure.integral_comp_mul_left (fun u : ℝ ↦ (u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6) *
    Real.exp (-(u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6))) c
  have hd := Measure.integral_comp_mul_left
    (fun u : ℝ ↦ Real.exp (-(u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6))) c
  rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at hn hd
  simp only [hpt] at hn hd
  unfold crossover
  have hn' : (∫ u, (u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6) * Real.exp (-(u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6))) =
      c * ∫ y, (y ^ 4 + σ ^ 5 * y ^ 2) * Real.exp (-(y ^ 4 + σ ^ 5 * y ^ 2)) := by
    rw [hn, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  have hd' : (∫ u, Real.exp (-(u ^ 4 * σ ^ 2 + u ^ 2 * σ ^ 6))) =
      c * ∫ y, Real.exp (-(y ^ 4 + σ ^ 5 * y ^ 2)) := by
    rw [hd, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  rw [hn', hd', mul_div_mul_left _ _ hcpos.ne']

/-- **Layer 2**: along `s = σ t^{-1/10}` the energy statistic converges to the toy crossover
`G(σ⁵)`. -/
theorem twoLayer_layer2 {χ : ℝ → ℝ} (hχ : Cutoff χ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t ↦ edgeEnergy χ twoLayerF (σ * t ^ (-(1 / 10 : ℝ))) t) atTop
      (𝓝 (crossover (σ ^ 5))) := by
  have h := (twoLayer_edge2_data hσ.ne').tendsto_energy hχ
  rw [edge2_limit_eq hσ] at h
  refine h.congr' (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [edgeEnergy, twoLayerF]
  congr 1
  congr 1 <;> refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_) <;> simp only <;>
    ring_nf

theorem twoLayer_layer2_zero : crossover ((0 : ℝ) ^ 5) = 1 / 4 := by
  rw [zero_pow (by norm_num), crossover_zero]

theorem twoLayer_layer2_atTop : Tendsto (fun σ : ℝ ↦ crossover (σ ^ 5)) atTop (𝓝 (1 / 2)) :=
  tendsto_crossover_atTop.comp (tendsto_pow_atTop (n := 5) (by norm_num))

end Laplace.Multi
