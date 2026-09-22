/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.FourGonGibbs

/-!
# The Gibbs law of a homogeneous loss of degree `p` on `ℝ²`

For `K(z) = a ‖z‖^p` with `a > 0` and `p > 0` on `ℝ²`, under the Gibbs measure `∝ e^{-tK}`:

* `Z(t) = 2π (ta)^{-2/p} Γ(2/p)/p` (`partitionFunction_homogeneous`);
* `E_t[‖z‖^k] = (ta)^{-k/p} Γ((k+2)/p)/Γ(2/p)` for `k > -2` (`homogeneous_gibbs_moment`);
* `t E_t[K] = 2/p` and `t² Var_t[K] = 2/p`, for every `t > 0` (`homogeneous_gibbs_excess`,
  `homogeneous_gibbs_variance`).

The last two are the `d_s/p` law of the working note *Patterning flow* (Prop. "Gibbs law of a
homogeneous loss") in dimension `d_s = 2`: `tK` has the `Gamma(2/p, 1)` law, whose mean and
variance are both `2/p`, so the learning coefficient of the germ is both the mean and the variance
of the tempered excess loss. At `a = 1/15`, `p = 4` this is the dead component of the 4-gon
(`deadQuartic_gibbs_excess`, `deadQuartic_gibbs_variance`, both `1/2`); at `p = 2` it is the
Gaussian value `1` for two quadratic directions. Positivity of `a` (confinement of `K` on the unit
circle) is what makes the radial integrals finite; the route is `integral_radial` (polar
coordinates) followed by the Gamma integral `integral_rpow_mul_exp_neg_mul_rpow`.
-/

namespace Laplace.Patterning

open Real MeasureTheory Set

/-- The homogeneous loss `a ‖z‖^p` on `ℝ²`. -/
noncomputable def homogeneousLoss (a p : ℝ) (z : ℝ × ℝ) : ℝ := a * (√(z.1 ^ 2 + z.2 ^ 2)) ^ p

theorem sqrt_rpow_eq_rpow_half (s : ℝ) (hs : 0 ≤ s) (k : ℝ) : (√s) ^ k = s ^ (k / 2) := by
  rw [sqrt_eq_rpow, ← rpow_mul hs, show 1 / (2 : ℝ) * k = k / 2 by ring]

theorem homogeneousLoss_eq (a p : ℝ) (z : ℝ × ℝ) :
    homogeneousLoss a p z = a * (z.1 ^ 2 + z.2 ^ 2) ^ (p / 2) := by
  rw [homogeneousLoss, sqrt_rpow_eq_rpow_half _ (by positivity)]

theorem sq_rpow_half (r : ℝ) (hr : 0 ≤ r) (k : ℝ) : (r ^ 2) ^ (k / 2) = r ^ k := by
  rw [← rpow_two, ← rpow_mul hr, show (2 : ℝ) * (k / 2) = k by ring]

/-- `∫ ‖z‖^k e^{-tK} dz = 2π (ta)^{-(k+2)/p} Γ((k+2)/p)/p` for `k > -2`. -/
theorem integral_radial_moment (a p t k : ℝ) (ha : 0 < a) (hp : 0 < p) (ht : 0 < t) (hk : -2 < k) :
    ∫ z : ℝ × ℝ, (√(z.1 ^ 2 + z.2 ^ 2)) ^ k * exp (-(t * homogeneousLoss a p z))
      = (2 * π) * ((t * a) ^ (-(k + 2) / p) * (1 / p) * Gamma ((k + 2) / p)) := by
  have hta : 0 < t * a := mul_pos ht ha
  have hfun : (fun z : ℝ × ℝ => (√(z.1 ^ 2 + z.2 ^ 2)) ^ k * exp (-(t * homogeneousLoss a p z)))
      = fun z => (fun s : ℝ => s ^ (k / 2) * exp (-(t * a) * s ^ (p / 2))) (z.1 ^ 2 + z.2 ^ 2) := by
    funext z
    have hs : (0 : ℝ) ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
    simp only [homogeneousLoss_eq, sqrt_rpow_eq_rpow_half _ hs]
    rw [show -(t * (a * (z.1 ^ 2 + z.2 ^ 2) ^ (p / 2)))
        = -(t * a) * (z.1 ^ 2 + z.2 ^ 2) ^ (p / 2) by ring]
  rw [hfun, integral_radial (fun s : ℝ => s ^ (k / 2) * exp (-(t * a) * s ^ (p / 2)))]
  beta_reduce
  have hrad : ∫ r in Ioi (0 : ℝ), r * ((r ^ 2) ^ (k / 2) * exp (-(t * a) * (r ^ 2) ^ (p / 2)))
      = ∫ r in Ioi (0 : ℝ), r ^ (k + 1) * exp (-(t * a) * r ^ p) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr' : 0 < r := hr
    rw [sq_rpow_half r hr'.le, sq_rpow_half r hr'.le, rpow_add_one hr'.ne']
    ring
  rw [hrad, integral_rpow_mul_exp_neg_mul_rpow hp (by linarith) hta,
    show k + 1 + 1 = k + 2 by ring]

/-- **The partition function** `Z(t) = 2π (ta)^{-2/p} Γ(2/p)/p`. -/
theorem partitionFunction_homogeneous (a p t : ℝ) (ha : 0 < a) (hp : 0 < p) (ht : 0 < t) :
    Laplace.TwoD.partitionFunction (homogeneousLoss a p) t
      = (2 * π) * ((t * a) ^ (-(2 : ℝ) / p) * (1 / p) * Gamma (2 / p)) := by
  have h := integral_radial_moment a p t 0 ha hp ht (by norm_num)
  simp only [rpow_zero, one_mul, zero_add] at h
  unfold Laplace.TwoD.partitionFunction
  rw [h]

/-- **The radial moments** `E_t[‖z‖^k] = (ta)^{-k/p} Γ((k+2)/p)/Γ(2/p)` for `k > -2`. -/
theorem homogeneous_gibbs_moment (a p t k : ℝ) (ha : 0 < a) (hp : 0 < p) (ht : 0 < t)
    (hk : -2 < k) :
    Laplace.TwoD.gibbsExpectation (homogeneousLoss a p) t (fun z => (√(z.1 ^ 2 + z.2 ^ 2)) ^ k)
      = (t * a) ^ (-k / p) * Gamma ((k + 2) / p) / Gamma (2 / p) := by
  have hta : 0 < t * a := mul_pos ht ha
  unfold Laplace.TwoD.gibbsExpectation
  rw [integral_radial_moment a p t k ha hp ht hk, partitionFunction_homogeneous a p t ha hp ht]
  have hsplit : (t * a) ^ (-(k + 2) / p) = (t * a) ^ (-k / p) * (t * a) ^ (-(2 : ℝ) / p) := by
    rw [← rpow_add hta]
    congr 1
    ring
  have hG : 0 < Gamma (2 / p) := Gamma_pos_of_pos (by positivity)
  have hr : 0 < (t * a) ^ (-(2 : ℝ) / p) := rpow_pos_of_pos hta _
  rw [hsplit]
  field_simp

theorem gibbsExpectation_const_mul (L : ℝ × ℝ → ℝ) (t c : ℝ) (f : ℝ × ℝ → ℝ) :
    Laplace.TwoD.gibbsExpectation L t (fun z => c * f z)
      = c * Laplace.TwoD.gibbsExpectation L t f := by
  unfold Laplace.TwoD.gibbsExpectation
  simp_rw [mul_assoc]
  rw [integral_const_mul, mul_div_assoc]

/-- **`t E_t[K] = 2/p` for every `t > 0`**: the equipartition value of a confining homogeneous
loss of degree `p` in two variables (the `d_s/p` law with `d_s = 2`). -/
theorem homogeneous_gibbs_excess (a p t : ℝ) (ha : 0 < a) (hp : 0 < p) (ht : 0 < t) :
    t * Laplace.TwoD.gibbsExpectation (homogeneousLoss a p) t (homogeneousLoss a p) = 2 / p := by
  have hta : 0 < t * a := mul_pos ht ha
  have hp0 : p ≠ 0 := hp.ne'
  have h : Laplace.TwoD.gibbsExpectation (homogeneousLoss a p) t (homogeneousLoss a p)
      = a * Laplace.TwoD.gibbsExpectation (homogeneousLoss a p) t
          (fun z => (√(z.1 ^ 2 + z.2 ^ 2)) ^ p) := by
    rw [← gibbsExpectation_const_mul]
    rfl
  rw [h, homogeneous_gibbs_moment a p t p ha hp ht (by linarith),
    show -p / p = -1 by rw [neg_div, div_self hp0], rpow_neg_one,
    show (p + 2) / p = 2 / p + 1 by rw [add_div, div_self hp0, add_comm],
    Gamma_add_one (by positivity : (2 / p) ≠ 0)]
  have hG : 0 < Gamma (2 / p) := Gamma_pos_of_pos (by positivity)
  field_simp

/-- **`t² Var_t[K] = 2/p` for every `t > 0`**: `tK` has the `Gamma(2/p, 1)` law, so its variance
equals its mean; the learning coefficient of the germ is both the mean and the variance of the
tempered excess loss. -/
theorem homogeneous_gibbs_variance (a p t : ℝ) (ha : 0 < a) (hp : 0 < p) (ht : 0 < t) :
    t ^ 2 * Laplace.TwoD.gibbsCov (homogeneousLoss a p) t (homogeneousLoss a p)
      (homogeneousLoss a p) = 2 / p := by
  have hta : 0 < t * a := mul_pos ht ha
  have hp0 : p ≠ 0 := hp.ne'
  set E := Laplace.TwoD.gibbsExpectation (homogeneousLoss a p) t (homogeneousLoss a p) with hE
  have hK : E = 2 / (p * t) := by
    have h := homogeneous_gibbs_excess a p t ha hp ht
    rw [← hE] at h
    rw [eq_div_iff (by positivity), show E * (p * t) = p * (t * E) by ring, h]
    field_simp
  have hsq : Laplace.TwoD.gibbsExpectation (homogeneousLoss a p) t
      (fun z => homogeneousLoss a p z * homogeneousLoss a p z)
      = a ^ 2 * ((t * a) ^ (-(2 * p) / p) * Gamma ((2 * p + 2) / p) / Gamma (2 / p)) := by
    rw [← homogeneous_gibbs_moment a p t (2 * p) ha hp ht (by linarith),
      ← gibbsExpectation_const_mul]
    congr 1
    funext z
    simp only [homogeneousLoss]
    rw [two_mul, rpow_add_of_nonneg (sqrt_nonneg _) hp.le hp.le]
    ring
  unfold Laplace.TwoD.gibbsCov
  rw [hsq, ← hE, hK, show -(2 * p) / p = -2 by rw [neg_div, mul_div_assoc, div_self hp0, mul_one],
    show (2 * p + 2) / p = 2 / p + 1 + 1 by
      rw [add_div, mul_div_assoc, div_self hp0, mul_one]; ring,
    Gamma_add_one (by positivity : (2 / p + 1) ≠ 0), Gamma_add_one (by positivity : (2 / p) ≠ 0),
    rpow_neg hta.le, rpow_two]
  have hG : 0 < Gamma (2 / p) := Gamma_pos_of_pos (by positivity)
  field_simp
  ring

end Laplace.Patterning
