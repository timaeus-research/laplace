/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.CoupledPhaseDiagram

/-!
# The general two-monomial wall

The quartic phase diagram of `CoupledPhaseDiagram` is the case `p = 4`, `q = 2` of the
two-monomial wall: for real `p > q > 0` and

  `Z(t, s) = ∫₀^∞ e^{-t (w^p + s w^q)} dw`   (`twoZ`)

the coupled limit `s = t^{-σ}` has the exponent `λ(σ) = max (1/p, (1 − σ)/q)` (`twoExponent`), a
convex piecewise affine function with a single wall at `σ* = 1 − q/p`, and

* the **wall profile is exact** in the crossover variable `c = s t^{1 − q/p}`:
  `t^{1/p} Z(t, c t^{-(1 − q/p)}) = ∫₀^∞ e^{-(y^p + c y^q)} dy` (`twoZ_wall_variable`);
* for `σ > σ*` (the `x^p` regime) `t^{1/p} Z → ∫ e^{-y^p}` (`two_p_regime`);
* for `σ < σ*` (the `x^q` regime) `t^{(1−σ)/q} Z → ∫ e^{-y^q}` (`two_q_regime`).

Both regimes are dominated convergence in the small coefficient after the scaling that makes
the dominant monomial `O(1)`; the profile at the wall interpolates them. This is the
one-dimensional, one-wall instance of the fixed-wall rescaling theorem of the valuation fan.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The two-monomial partition function `Z(t, s) = ∫₀^∞ e^{-t (w^p + s w^q)} dw`. -/
noncomputable def twoZ (p q t s : ℝ) : ℝ :=
  ∫ w in Ioi (0 : ℝ), Real.exp (-(t * (w ^ p + s * w ^ q)))

/-- The profile `∫₀^∞ e^{-(y^p + c y^q)} dy`. -/
noncomputable def twoProfile (p q c : ℝ) : ℝ := ∫ y in Ioi (0 : ℝ), Real.exp (-(y ^ p + c * y ^ q))

/-- The coupled-limit exponent `λ(σ) = max (1/p, (1 − σ)/q)`. -/
noncomputable def twoExponent (p q σ : ℝ) : ℝ := max (1 / p) ((1 - σ) / q)

theorem integrableOn_exp_neg_rpow {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun y : ℝ ↦ Real.exp (-(y ^ p))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := p) (s := 0) (b := 1) (by norm_num) hp
    one_pos
  refine this.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi
  simp [Real.rpow_zero]

/-- `∫ e^{-(y^p + c y^q)} → ∫ e^{-y^p}` as `c → 0⁺`. -/
theorem tendsto_twoProfile {p q : ℝ} (hp : 0 < p) {c : ℝ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) (hc0 : ∀ᶠ t in atTop, 0 ≤ c t) :
    Tendsto (fun t ↦ twoProfile p q (c t)) atTop (𝓝 (twoProfile p q 0)) := by
  unfold twoProfile
  refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ Real.exp (-(y ^ p)))
    (Filter.Eventually.of_forall fun t ↦ (Measurable.aestronglyMeasurable (by fun_prop)))
    ?_ (integrableOn_exp_neg_rpow hp) ?_
  · filter_upwards [hc0] with t ht
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
    have := Real.rpow_nonneg (le_of_lt hy) q
    nlinarith [mul_nonneg ht this]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y _ ↦ ?_)
    have h1 : Tendsto (fun t ↦ -(y ^ p + c t * y ^ q)) atTop (𝓝 (-(y ^ p + 0 * y ^ q))) :=
      ((hc.mul_const _).const_add _).neg
    exact (Real.continuous_exp.tendsto _).comp h1

/-- The scaling of `Z` by the dominant monomial `w^p`:
`Z(t, s) = t^{-1/p} ∫₀^∞ e^{-(y^p + t^{1 − q/p} s y^q)} dy`. -/
theorem twoZ_eq_twoProfile {p q : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (s : ℝ) :
    twoZ p q t s = t ^ (-(1 / p)) * twoProfile p q (t ^ (1 - q / p) * s) := by
  unfold twoZ twoProfile
  have ha : 0 < t ^ (1 / p) := Real.rpow_pos_of_pos ht _
  have key := integral_comp_mul_left_Ioi
    (fun y ↦ Real.exp (-(y ^ p + (t ^ (1 - q / p) * s) * y ^ q))) (0 : ℝ) ha
  rw [mul_zero, smul_eq_mul, ← Real.rpow_neg ht.le] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
  have hw0 : (0 : ℝ) < w := hw
  have hp' : (t ^ (1 / p) * w) ^ p = t * w ^ p := by
    rw [Real.mul_rpow ha.le hw0.le, ← Real.rpow_mul ht.le, one_div_mul_cancel hp.ne',
      Real.rpow_one]
  have hq' : (t ^ (1 / p) * w) ^ q = t ^ (q / p) * w ^ q := by
    rw [Real.mul_rpow ha.le hw0.le, ← Real.rpow_mul ht.le]
    congr 2
    ring
  have hh : t ^ (1 - q / p) * t ^ (q / p) = t := by
    rw [← Real.rpow_add ht]
    norm_num
  rw [hp', hq']
  congr 1
  linear_combination (s * w ^ q) * hh

/-- **The wall profile is exact in the crossover variable** `c = s t^{1 − q/p}`. -/
theorem twoZ_wall_variable {p q : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    t ^ (1 / p) * twoZ p q t (c * t ^ (-(1 - q / p))) = twoProfile p q c := by
  rw [twoZ_eq_twoProfile hp ht, ← mul_assoc, ← Real.rpow_add ht]
  norm_num
  congr 1
  rw [← mul_assoc, mul_comm (t ^ (1 - q / p)) c, mul_assoc, ← Real.rpow_add ht]
  norm_num

/-- **The `x^p` regime** `σ > 1 − q/p`: `t^{1/p} Z(t, t^{-σ}) → ∫ e^{-y^p}`. -/
theorem two_p_regime {p q σ : ℝ} (hp : 0 < p) (hσ : 1 - q / p < σ) :
    Tendsto (fun t ↦ t ^ (1 / p) * twoZ p q t (t ^ (-σ))) atTop (𝓝 (twoProfile p q 0)) := by
  have hc : Tendsto (fun t : ℝ ↦ t ^ (1 - q / p - σ)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < σ - (1 - q / p))
    simpa only [neg_sub] using this
  refine (tendsto_twoProfile hp hc ?_).congr' ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (Real.rpow_pos_of_pos ht _).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [twoZ_eq_twoProfile hp ht, ← mul_assoc, ← Real.rpow_add ht, ← Real.rpow_add ht]
    norm_num
    rw [sub_eq_add_neg]

/-- The profile of the `x^q` regime, `∫₀^∞ e^{-(y^q + c y^p)} dy`. -/
noncomputable def twoProfileQ (p q c : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), Real.exp (-(y ^ q + c * y ^ p))

theorem tendsto_twoProfileQ {p q : ℝ} (hq : 0 < q) {c : ℝ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) (hc0 : ∀ᶠ t in atTop, 0 ≤ c t) :
    Tendsto (fun t ↦ twoProfileQ p q (c t)) atTop (𝓝 (twoProfileQ p q 0)) := by
  unfold twoProfileQ
  refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ Real.exp (-(y ^ q)))
    (Filter.Eventually.of_forall fun t ↦ (Measurable.aestronglyMeasurable (by fun_prop)))
    ?_ (integrableOn_exp_neg_rpow hq) ?_
  · filter_upwards [hc0] with t ht
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
    have := Real.rpow_nonneg (le_of_lt hy) p
    nlinarith [mul_nonneg ht this]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y _ ↦ ?_)
    have h1 : Tendsto (fun t ↦ -(y ^ q + c t * y ^ p)) atTop (𝓝 (-(y ^ q + 0 * y ^ p))) :=
      ((hc.mul_const _).const_add _).neg
    exact (Real.continuous_exp.tendsto _).comp h1

/-- The scaling of `Z` by the monomial `s w^q` (`s > 0`):
`Z(t, s) = (ts)^{-1/q} ∫₀^∞ e^{-(y^q + t (ts)^{-p/q} y^p)} dy`. -/
theorem twoZ_eq_twoProfileQ {p q : ℝ} (hq : 0 < q) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    twoZ p q t s = (t * s) ^ (-(1 / q)) * twoProfileQ p q (t * (t * s) ^ (-(p / q))) := by
  unfold twoZ twoProfileQ
  have hts : 0 < t * s := mul_pos ht hs
  have ha : 0 < (t * s) ^ (1 / q) := Real.rpow_pos_of_pos hts _
  have key := integral_comp_mul_left_Ioi
    (fun y ↦ Real.exp (-(y ^ q + (t * (t * s) ^ (-(p / q))) * y ^ p))) (0 : ℝ) ha
  rw [mul_zero, smul_eq_mul, ← Real.rpow_neg hts.le] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
  have hw0 : (0 : ℝ) < w := hw
  have hq' : ((t * s) ^ (1 / q) * w) ^ q = t * s * w ^ q := by
    rw [Real.mul_rpow ha.le hw0.le, ← Real.rpow_mul hts.le, one_div_mul_cancel hq.ne',
      Real.rpow_one]
  have hp' : ((t * s) ^ (1 / q) * w) ^ p = (t * s) ^ (p / q) * w ^ p := by
    rw [Real.mul_rpow ha.le hw0.le, ← Real.rpow_mul hts.le]
    congr 2
    ring
  have hh : (t * s) ^ (-(p / q)) * (t * s) ^ (p / q) = 1 := by
    rw [← Real.rpow_add hts]
    norm_num
  rw [hq', hp']
  congr 1
  linear_combination (t * w ^ p) * hh

/-- **The `x^q` regime** `σ < 1 − q/p`: `t^{(1−σ)/q} Z(t, t^{-σ}) → ∫ e^{-y^q}`. -/
theorem two_q_regime {p q σ : ℝ} (hp : 0 < p) (hq : 0 < q) (hσ : σ < 1 - q / p) :
    Tendsto (fun t ↦ t ^ ((1 - σ) / q) * twoZ p q t (t ^ (-σ))) atTop (𝓝 (twoProfileQ p q 0)) := by
  have hexp : 0 < (1 - σ) * p / q - 1 := by
    have : q / p < 1 - σ := by linarith
    have h1 : q < (1 - σ) * p := by rwa [div_lt_iff₀ hp] at this
    have h2 : 1 < (1 - σ) * p / q := by rwa [lt_div_iff₀ hq, one_mul]
    linarith
  have hc : Tendsto (fun t : ℝ ↦ t ^ (1 - (1 - σ) * p / q)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop hexp
    simpa only [neg_sub] using this
  refine (tendsto_twoProfileQ hq hc ?_).congr' ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (Real.rpow_pos_of_pos ht _).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hs : 0 < t ^ (-σ) := Real.rpow_pos_of_pos ht _
    rw [twoZ_eq_twoProfileQ hq ht hs]
    have hts : t * t ^ (-σ) = t ^ (1 - σ) := by
      rw [show (1 - σ) = 1 + -σ by ring, Real.rpow_add ht, Real.rpow_one]
    rw [hts, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le, ← mul_assoc, ← Real.rpow_add ht]
    have e1 : (1 - σ) / q + (1 - σ) * -(1 / q) = 0 := by ring
    have e2 : (1 - σ) * -(p / q) = -((1 - σ) * p / q) := by ring
    rw [e1, Real.rpow_zero, one_mul, e2]
    congr 1
    rw [show 1 - (1 - σ) * p / q = 1 + -((1 - σ) * p / q) by ring, Real.rpow_add ht,
      Real.rpow_one]

end Laplace.Multi
