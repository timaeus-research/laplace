/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Laplace.Grammar.HeadlinePosteriorRates

/-!
# Weighted one-dimensional power substitution (general-`d` monomial model, step 1)

For the monomial model `∫_{(0,1]} u^h g(u^{2k}) du` the substitution `t = u^{2k}` gives
`∫_{(0,1]} u^h g(u^{2k}) du = (1/2k) ∫_{(0,1]} t^{λ−1} g(t) dt` with `λ = (h+1)/(2k)`
(`lintegral_weighted_power_subst`), in Lebesgue-integral form for an arbitrary measurable
`ℝ≥0∞`-valued `g` (no integrability needed). Built on Mathlib's one-dimensional change of variables
`lintegral_image_eq_lintegral_abs_deriv_mul` with `(0,1]` mapped onto itself by `u ↦ u^p`
(`image_rpow_Ioc`, `lintegral_Ioc_rpow_subst`). Astra #14 unit. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real

namespace Laplace.Grammar

/-- `u ↦ u^p` maps `(0,1]` onto itself for `p > 0`. -/
theorem image_rpow_Ioc (p : ℝ) (hp : 0 < p) : (fun x : ℝ => x ^ p) '' Ioc 0 1 = Ioc 0 1 := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    exact ⟨Real.rpow_pos_of_pos hx0 p, Real.rpow_le_one hx0.le hx1 hp.le⟩
  · rintro ⟨hy0, hy1⟩
    refine ⟨y ^ (1 / p), ⟨Real.rpow_pos_of_pos hy0 _, Real.rpow_le_one hy0.le hy1 (by positivity)⟩,
      ?_⟩
    show (y ^ (1 / p)) ^ p = y
    rw [← Real.rpow_mul hy0.le, one_div_mul_cancel hp.ne', Real.rpow_one]

/-- **Change of variables `t = u^p` on `(0,1]`** for Lebesgue integrals. -/
theorem lintegral_Ioc_rpow_subst (p : ℝ) (hp : 0 < p) (g : ℝ → ENNReal) :
    ∫⁻ t in Ioc (0 : ℝ) 1, g t
      = ∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (p * u ^ (p - 1)) * g (u ^ p) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioc (0 : ℝ) 1)
    (f := fun x : ℝ => x ^ p) (f' := fun x : ℝ => p * x ^ (p - 1)) measurableSet_Ioc
    (fun x hx => (Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')).hasDerivWithinAt)
    ((Real.rpow_left_injOn hp.ne').mono fun x hx => le_of_lt hx.1) g
  rw [image_rpow_Ioc p hp] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have : 0 < p * u ^ (p - 1) := by
    have := Real.rpow_pos_of_pos hu.1 (p - 1)
    positivity
  rw [abs_of_pos this]

/-- **Weighted power substitution**:
`∫_{(0,1]} u^h g(u^{2k}) du = (1/2k) ∫_{(0,1]} t^{(h+1)/(2k) − 1} g(t) dt`. -/
theorem lintegral_weighted_power_subst (h k : ℕ) (hk : 0 < k) (G : ℝ → ENNReal) :
    ∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ h) * G (u ^ (2 * k))
      = ENNReal.ofReal (1 / (2 * (k : ℝ)))
        * ∫⁻ t in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (t ^ (((h : ℝ) + 1) / (2 * (k : ℝ)) - 1)) * G t := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set p : ℝ := 2 * (k : ℝ) with hpdef
  have hp : 0 < p := by positivity
  conv_rhs => rw [lintegral_Ioc_rpow_subst p hp, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have hu0 : 0 < u := hu.1
  have hup : u ^ p = u ^ (2 * k) := by
    rw [hpdef, show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hkey : 1 / p * (p * u ^ (p - 1)) * (u ^ p) ^ (((h : ℝ) + 1) / p - 1) = u ^ h := by
    rw [← Real.rpow_mul hu0.le, ← Real.rpow_natCast u h]
    have h1 : 1 / p * (p * u ^ (p - 1)) = u ^ (p - 1) := by field_simp
    rw [h1, ← Real.rpow_add hu0]
    congr 1
    field_simp
    ring
  have hnn1 : 0 ≤ 1 / p * (p * u ^ (p - 1)) := by
    have := Real.rpow_pos_of_pos hu0 (p - 1); positivity
  have hnn2 : 0 ≤ (u ^ p) ^ (((h : ℝ) + 1) / p - 1) :=
    Real.rpow_nonneg (Real.rpow_nonneg hu0.le _) _
  symm
  calc ENNReal.ofReal (1 / p) * (ENNReal.ofReal (p * u ^ (p - 1))
          * (ENNReal.ofReal ((u ^ p) ^ (((h : ℝ) + 1) / p - 1)) * G (u ^ p)))
      = ENNReal.ofReal (1 / p * (p * u ^ (p - 1)) * (u ^ p) ^ (((h : ℝ) + 1) / p - 1))
          * G (u ^ p) := by
        rw [ENNReal.ofReal_mul hnn1, @ENNReal.ofReal_mul (1 / p) (p * u ^ (p - 1))
          (one_div_nonneg.2 hp.le)]
        ring
    _ = ENNReal.ofReal (u ^ h) * G (u ^ (2 * k)) := by rw [hkey, hup]

end Laplace.Grammar
