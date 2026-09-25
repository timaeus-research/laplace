/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MixedTruthWeighted

/-!
# The weighted mixed truth: a negative exponent moves the mass to the other axis

The third case of the trichotomy for the weight `x^{h−1} dx` on the fibre `xy = s` of the square
`(0, b)²` (Astra, round 5): for `h < 0` the fibre integral, scaled by `t^h`, converges to the
finite measure `σ^h u^{−h−1} du` on the axis `x = 0` (`tendsto_weightedMixed_neg`). The proof is
the change of variables `x ↦ σ/(tx)`, an involution of the fibre interval `(σ/(bt), b)`
(`image_fibreInv`, `weightedMixed_change_of_variables`), which turns the weight `x^{h−1} dx` into
`(σ/t)^h u^{−h−1} du` and reduces the statement to the positive-exponent theorem with the roles of
the two coordinates exchanged.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

/-- The involution `x ↦ σ/(tx)` of the fibre interval `(σ/(bt), b)`. -/
theorem image_fibreInv {b σ t : ℝ} (hb : 0 < b) (hσ : 0 < σ) (ht : 0 < t) :
    (fun u : ℝ ↦ σ / (t * u)) '' Ioo (σ / (b * t)) b = Ioo (σ / (b * t)) b := by
  have hA : 0 < σ / (b * t) := div_pos hσ (mul_pos hb ht)
  have hmem : ∀ u ∈ Ioo (σ / (b * t)) b, σ / (t * u) ∈ Ioo (σ / (b * t)) b := by
    intro u hu
    have hu0 : 0 < u := hA.trans hu.1
    constructor
    · rw [div_lt_div_iff_of_pos_left hσ (mul_pos hb ht) (mul_pos ht hu0)]
      nlinarith [hu.2]
    · rw [div_lt_iff₀ (mul_pos ht hu0)]
      have := hu.1
      rw [div_lt_iff₀ (mul_pos hb ht)] at this
      nlinarith
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hmem u hu
  · intro hx
    have hx0 : 0 < x := hA.trans hx.1
    refine ⟨σ / (t * x), hmem x hx, ?_⟩
    field_simp

/-- The change of variables `x ↦ σ/(tx)` on the fibre interval. -/
theorem weightedMixed_change_of_variables {b σ h t : ℝ} (hb : 0 < b) (hσ : 0 < σ) (ht : 0 < t)
    (f : ℝ → ℝ → ℝ) :
    ∫ x in Ioo (σ / (b * t)) b, x ^ (h - 1) * f x (σ / (t * x)) =
      (σ / t) ^ h * ∫ u in Ioo (σ / (b * t)) b, u ^ (-h - 1) * f (σ / (t * u)) u := by
  have hA : 0 < σ / (b * t) := div_pos hσ (mul_pos hb ht)
  have hst : 0 < σ / t := div_pos hσ ht
  have hderiv : ∀ u ∈ Ioo (σ / (b * t)) b,
      HasDerivWithinAt (fun u : ℝ ↦ σ / (t * u)) (σ / t * -(u ^ 2)⁻¹) (Ioo (σ / (b * t)) b) u := by
    intro u hu
    have hu0 : 0 < u := hA.trans hu.1
    have hd := (hasDerivAt_inv hu0.ne').const_mul (σ / t)
    refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)).hasDerivWithinAt
    change σ / (t * y) = σ / t * y⁻¹
    rw [← div_div, div_eq_mul_inv]
  have hinj : InjOn (fun u : ℝ ↦ σ / (t * u)) (Ioo (σ / (b * t)) b) := by
    intro u hu v hv huv
    have hu0 : 0 < u := hA.trans hu.1
    have hv0 : 0 < v := hA.trans hv.1
    have this : σ / (t * u) = σ / (t * v) := huv
    rw [div_eq_div_iff (mul_pos ht hu0).ne' (mul_pos ht hv0).ne'] at this
    exact mul_left_cancel₀ (mul_pos hσ ht).ne' (by linear_combination -this)
  rw [← integral_const_mul]
  conv_lhs => rw [← image_fibreInv hb hσ ht]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun x ↦ x ^ (h - 1) * f x (σ / (t * x)))]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu ↦ ?_
  have hu0 : 0 < u := hA.trans hu.1
  have e1 : σ / (t * (σ / (t * u))) = u := by field_simp
  rw [smul_eq_mul, e1, abs_mul, abs_neg, abs_inv, abs_of_pos hst, abs_of_pos (pow_pos hu0 2)]
  have e2 : σ / (t * u) = σ / t * u⁻¹ := by rw [← div_div, div_eq_mul_inv]
  rw [e2, Real.mul_rpow hst.le (inv_nonneg.mpr hu0.le), Real.inv_rpow hu0.le,
    ← Real.rpow_neg hu0.le]
  have h1 : (σ / t) ^ h = σ / t * (σ / t) ^ (h - 1) := by
    conv_lhs => rw [show h = 1 + (h - 1) by ring]
    rw [Real.rpow_add hst, Real.rpow_one]
  have h2 : u ^ (-h - 1) = (u ^ 2)⁻¹ * u ^ (-(h - 1)) := by
    rw [show -h - 1 = (-2 : ℝ) + -(h - 1) by ring, Real.rpow_add hu0, Real.rpow_neg hu0.le,
      Real.rpow_two]
  rw [h1, h2]
  ring

/-- **The weighted mixed truth with a negative exponent.** For `h < 0` and `f` continuous,
`t^h ∫_{σ/(bt)}^{b} x^{h−1} f(x, σ/(tx)) dx → σ^h ∫_0^b u^{−h−1} f(0, u) du`: the mass moves to
the other axis with the finite density `σ^h u^{−h−1}`. -/
theorem tendsto_weightedMixed_neg {b σ h : ℝ} (hb : 0 < b) (hσ : 0 < σ) (hh : h < 0)
    {f : ℝ → ℝ → ℝ} (hf : Continuous (fun p : ℝ × ℝ ↦ f p.1 p.2)) :
    Tendsto (fun t ↦ t ^ h * ∫ x in Ioo (σ / (b * t)) b, x ^ (h - 1) * f x (σ / (t * x))) atTop
      (𝓝 (σ ^ h * ∫ u in Ioo 0 b, u ^ (-h - 1) * f 0 u)) := by
  have hpos := tendsto_weightedMixed hb hσ (neg_pos.mpr hh) (f := fun u x ↦ f x u)
    (hf.comp continuous_swap)
  refine (hpos.const_mul (σ ^ h)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hne : t ^ h ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  rw [weightedMixed_change_of_variables hb hσ ht f, Real.div_rpow hσ.le ht.le]
  field_simp

end Laplace.Multi
