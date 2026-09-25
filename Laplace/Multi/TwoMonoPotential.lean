/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.HalfLineLaplace

/-!
# The rescaled two-monomial potential `ψ(z) = z^p − (p/q) z^q`

On the negative side of the wall, `y^p − b y^q` rescales (`y = y_b z`, `y_b = (qb/p)^{1/(p−q)}`,
`B = y_b^p`) to `B ψ(z)` with `ψ(z) = z^p − (p/q) z^q`, minimised at `z = 1` with
`ψ''(1) = p(p − q)`. This module verifies the hypotheses of the half-line Laplace lemma for the
centred potential `φ = ψ − ψ(1)`:

* the second-order limit `φ(1 + h)/h² → p(p−q)/2` (`twoMonoPhi_div_sq_tendsto`, by L'Hôpital);
* the quadratic lower bound `φ(z) ≥ c₁ (z − 1)²` on `(0, z₁]` (`twoMonoPhi_quad_bound`);
* the coercivity `φ(z) ≥ ½ (z − 1)^{min p 1}` beyond `z₁ = max 2 (2p/q)^{1/(p−q)}`
  (`twoMonoPhi_coercive`);

and the observable facts for `z^q`: `|z^q − 1| ≤ max q 1 · |z − 1| (1 + z)ⁿ` (`abs_rpow_sub_one_le`)
and `√B ((1 + w/√B)^q − 1) → q w` (`tendsto_sqrt_mul_rpow_sub_one`). Everything is elementary:
Bernoulli's inequalities for real powers and the fundamental theorem of calculus.
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

/-- The rescaled two-monomial potential. -/
noncomputable def twoMonoPsi (p q : ℝ) (z : ℝ) : ℝ := z ^ p - p / q * z ^ q

/-- Its derivative `ψ'(z) = p z^{p−1} − p z^{q−1}`. -/
noncomputable def twoMonoPsi' (p q : ℝ) (z : ℝ) : ℝ := p * z ^ (p - 1) - p * z ^ (q - 1)

/-- The centred potential `φ = ψ − ψ(1)`. -/
noncomputable def twoMonoPhi (p q : ℝ) (z : ℝ) : ℝ := twoMonoPsi p q z - twoMonoPsi p q 1

theorem twoMonoPhi_one (p q : ℝ) : twoMonoPhi p q 1 = 0 := sub_self _

theorem twoMonoPsi'_one (p q : ℝ) : twoMonoPsi' p q 1 = 0 := by
  simp [twoMonoPsi']

theorem measurable_twoMonoPhi (p q : ℝ) : Measurable (twoMonoPhi p q) := by
  unfold twoMonoPhi twoMonoPsi
  fun_prop

theorem hasDerivAt_twoMonoPsi {p q : ℝ} (hq : 0 < q) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (twoMonoPsi p q) (twoMonoPsi' p q z) z := by
  have h1 := Real.hasDerivAt_rpow_const (x := z) (p := p) (Or.inl hz.ne')
  have h2 := (Real.hasDerivAt_rpow_const (x := z) (p := q) (Or.inl hz.ne')).const_mul (p / q)
  refine (h1.sub h2).congr_deriv ?_
  unfold twoMonoPsi'
  field_simp

theorem hasDerivAt_twoMonoPhi {p q : ℝ} (hq : 0 < q) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (twoMonoPhi p q) (twoMonoPsi' p q z) z :=
  (hasDerivAt_twoMonoPsi hq hz).sub_const _

theorem hasDerivAt_twoMonoPsi' (p q : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (twoMonoPsi' p q) (p * ((p - 1) * z ^ (p - 2)) - p * ((q - 1) * z ^ (q - 2))) z := by
  have h1 := (Real.hasDerivAt_rpow_const (x := z) (p := p - 1) (Or.inl hz.ne')).const_mul p
  have h2 := (Real.hasDerivAt_rpow_const (x := z) (p := q - 1) (Or.inl hz.ne')).const_mul p
  refine (h1.sub h2).congr_deriv ?_
  rw [show p - 1 - 1 = p - 2 by ring, show q - 1 - 1 = q - 2 by ring]

theorem continuousOn_twoMonoPsi' (p q : ℝ) : ContinuousOn (twoMonoPsi' p q) (Ioi 0) :=
  fun _ hz ↦ (hasDerivAt_twoMonoPsi' p q hz).continuousAt.continuousWithinAt

/-- **The second-order limit** `φ(1 + h)/h² → p(p − q)/2`. -/
theorem twoMonoPhi_div_sq_tendsto {p q : ℝ} (hq : 0 < q) :
    Tendsto (fun h ↦ twoMonoPhi p q (1 + h) / h ^ 2) (𝓝[≠] 0) (𝓝 (p * (p - q) / 2)) := by
  have hnhds : ∀ᶠ h in 𝓝 (0 : ℝ), 0 < 1 + h := by
    have : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with h hh
    linarith [hh.1]
  refine HasDerivAt.lhopital_zero_nhdsNE (f' := fun h ↦ twoMonoPsi' p q (1 + h))
    (g' := fun h ↦ 2 * h) ?_ ?_ ?_ ?_ ?_ ?_
  · refine eventually_nhdsWithin_of_eventually_nhds (hnhds.mono fun h hh ↦ ?_)
    have := (hasDerivAt_twoMonoPhi (p := p) hq hh).comp h ((hasDerivAt_id h).const_add 1)
    exact this.congr_deriv (mul_one _)
  · exact Filter.Eventually.of_forall fun h ↦ by
      have := hasDerivAt_pow 2 h
      simpa using this
  · exact eventually_nhdsWithin_of_forall fun h (hh : h ≠ 0) ↦ by positivity
  · have hc := (hasDerivAt_twoMonoPhi (p := p) hq one_pos).continuousAt
    have : Tendsto (fun h : ℝ ↦ twoMonoPhi p q (1 + h)) (𝓝 0) (𝓝 (twoMonoPhi p q 1)) :=
      hc.tendsto.comp (by
        have : Tendsto (fun h : ℝ ↦ 1 + h) (𝓝 0) (𝓝 (1 + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rwa [add_zero] at this)
    rw [twoMonoPhi_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have : Tendsto (fun h : ℝ ↦ h ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (continuous_pow 2).tendsto 0
    rw [zero_pow two_ne_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · -- the slope of `ψ'` at `1`
    have hd := hasDerivAt_twoMonoPsi' p q one_pos
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have hmap : Tendsto (fun h : ℝ ↦ 1 + h) (𝓝[≠] 0) (𝓝[≠] 1) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun h : ℝ ↦ 1 + h) (𝓝 0) (𝓝 (1 + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun h (hh : h ≠ 0) ↦ by
          simp [hh]
    have := (hd.comp hmap).div_const 2
    simp only [Real.one_rpow, mul_one] at this
    refine (this.congr' ?_).trans (by
      rw [show p * (p - 1) - p * (q - 1) = p * (p - q) by ring])
    refine eventually_nhdsWithin_of_forall fun h (hh : h ≠ 0) ↦ ?_
    simp only [Function.comp_apply, slope_def_field, twoMonoPsi'_one, sub_zero, add_sub_cancel_left]
    field_simp

/-! ### One-variable inequalities for real powers -/

/-- `r (v − 1)/v ≤ v^r − 1` for `v ≥ 1`, `r > 0`. -/
theorem rpow_sub_one_ge {r : ℝ} (hr : 0 < r) {v : ℝ} (hv : 1 ≤ v) :
    r * (v - 1) / v ≤ v ^ r - 1 := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  rcases le_or_gt 1 r with hr1 | hr1
  · have := one_add_mul_self_le_rpow_one_add (s := v - 1) (by linarith) hr1
    rw [add_sub_cancel] at this
    calc r * (v - 1) / v ≤ r * (v - 1) := div_le_self (by nlinarith) hv
      _ ≤ v ^ r - 1 := by linarith
  · have hB := rpow_one_add_le_one_add_mul_self (s := 1 / v - 1) (by
      have : 0 < 1 / v := by positivity
      linarith) hr.le hr1.le
    rw [add_sub_cancel, one_div, Real.inv_rpow hv0.le] at hB
    have hvr : 0 < v ^ r := Real.rpow_pos_of_pos hv0 r
    have h1 : 1 ≤ v ^ r := Real.one_le_rpow hv hr.le
    -- `(v^r)⁻¹ ≤ 1 + r (v⁻¹ − 1)`; multiply by `v^r`
    have h2 : 1 ≤ v ^ r * (1 + r * (v⁻¹ - 1)) := by
      calc (1 : ℝ) = v ^ r * (v ^ r)⁻¹ := (mul_inv_cancel₀ hvr.ne').symm
        _ ≤ v ^ r * (1 + r * (v⁻¹ - 1)) := mul_le_mul_of_nonneg_left hB hvr.le
    have h3 : r * (v - 1) / v = r * (1 - v⁻¹) := by field_simp
    rw [h3]
    nlinarith

/-- `min 1 r · (1 − v) ≤ 1 − v^r` for `0 < v ≤ 1`, `r > 0`. -/
theorem one_sub_rpow_ge {r : ℝ} (hr : 0 < r) {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) :
    min 1 r * (1 - v) ≤ 1 - v ^ r := by
  rcases le_or_gt 1 r with hr1 | hr1
  · have := Real.rpow_le_rpow_of_exponent_ge hv0 hv1 hr1
    rw [Real.rpow_one] at this
    have hm : min 1 r ≤ 1 := min_le_left _ _
    nlinarith [min_le_left 1 r, sub_nonneg.mpr hv1]
  · have := rpow_one_add_le_one_add_mul_self (s := v - 1) (by linarith) hr.le hr1.le
    rw [add_sub_cancel] at this
    rw [min_eq_right hr1.le]
    linarith

/-- Antitonicity of `x ↦ x^z` for `z ≤ 0`. -/
theorem rpow_antitone_of_nonpos {x y z : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [show z = -(-z) by ring, Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy (by linarith))

/-! ### The quadratic lower bound -/

/-- The fundamental theorem of calculus for `φ` on `(0, ∞)`. -/
theorem twoMonoPhi_sub_eq_integral {p q : ℝ} (hq : 0 < q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    twoMonoPhi p q b - twoMonoPhi p q a = ∫ v in a..b, twoMonoPsi' p q v := by
  refine (integral_eq_sub_of_hasDerivAt (fun v hv ↦ hasDerivAt_twoMonoPhi hq ?_) ?_).symm
  · rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hv; exact lt_of_lt_of_le ha hv.1
    · rw [uIcc_of_ge h] at hv; exact lt_of_lt_of_le hb hv.1
  · refine ((continuousOn_twoMonoPsi' p q).mono ?_).intervalIntegrable
    rcases le_total a b with h | h
    · rw [uIcc_of_le h]; exact fun v hv ↦ lt_of_lt_of_le ha hv.1
    · rw [uIcc_of_ge h]; exact fun v hv ↦ lt_of_lt_of_le hb hv.1

/-- `ψ' ≤ 0` on `(0, 1]`. -/
theorem twoMonoPsi'_nonpos {p q : ℝ} (hq : 0 < q) (hqp : q < p) {v : ℝ} (hv0 : 0 < v)
    (hv1 : v ≤ 1) : twoMonoPsi' p q v ≤ 0 := by
  unfold twoMonoPsi'
  have := Real.rpow_le_rpow_of_exponent_ge hv0 hv1 (show q - 1 ≤ p - 1 by linarith)
  have hp : 0 < p := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this hp.le]

/-- `∫_1^z (v − 1) dv = (z − 1)²/2`. -/
theorem integral_sub_one (z : ℝ) : ∫ v in (1 : ℝ)..z, (v - 1) = (z - 1) ^ 2 / 2 := by
  rw [intervalIntegral.integral_comp_sub_right (fun v ↦ v) 1, integral_id]
  ring

/-- The lower bound on `[1, z₁]`: `φ(z) ≥ c (z − 1)²` with `c = p (p−q) min 1 (z₁^{q−2}) / 2`. -/
theorem twoMonoPhi_quad_right {p q : ℝ} (hq : 0 < q) (hqp : q < p) {z₁ : ℝ} (hz₁ : 1 ≤ z₁)
    {z : ℝ} (hz1 : 1 ≤ z) (hzz : z ≤ z₁) :
    p * (p - q) * min 1 (z₁ ^ (q - 2)) / 2 * (z - 1) ^ 2 ≤ twoMonoPhi p q z := by
  have hp : 0 < p := by linarith
  have hr : 0 < p - q := by linarith
  set m := min 1 (z₁ ^ (q - 2)) with hm
  have hm0 : 0 ≤ m := le_min zero_le_one (Real.rpow_nonneg (by linarith) _)
  -- pointwise bound on `ψ'`
  have hpt : ∀ v ∈ Icc (1 : ℝ) z, p * (p - q) * m * (v - 1) ≤ twoMonoPsi' p q v := fun v hv ↦ by
    have hv0 : 0 < v := lt_of_lt_of_le one_pos hv.1
    have hvz : v ≤ z₁ := hv.2.trans hzz
    have e : twoMonoPsi' p q v = p * v ^ (q - 1) * (v ^ (p - q) - 1) := by
      unfold twoMonoPsi'
      rw [show p - 1 = (q - 1) + (p - q) by ring, Real.rpow_add hv0]
      ring
    have h1 := rpow_sub_one_ge hr hv.1
    have hvq : v ^ (q - 1) / v = v ^ (q - 2) := by
      rw [show q - 2 = (q - 1) - 1 by ring, Real.rpow_sub_one hv0.ne' (q - 1)]
    have hvm : m ≤ v ^ (q - 2) := by
      rcases le_or_gt 0 (q - 2) with h | h
      · exact (min_le_left _ _).trans (Real.one_le_rpow hv.1 h)
      · exact (min_le_right _ _).trans (rpow_antitone_of_nonpos hv0 hvz h.le)
    rw [e]
    calc p * (p - q) * m * (v - 1) ≤ p * (p - q) * v ^ (q - 2) * (v - 1) := by
          gcongr
          linarith [hv.1]
      _ = p * v ^ (q - 1) * ((p - q) * (v - 1) / v) := by
          rw [← hvq]
          field_simp
      _ ≤ p * v ^ (q - 1) * (v ^ (p - q) - 1) := by
          refine mul_le_mul_of_nonneg_left h1 ?_
          exact mul_nonneg hp.le (Real.rpow_nonneg hv0.le _)
  have hint : IntervalIntegrable (twoMonoPsi' p q) volume 1 z :=
    ((continuousOn_twoMonoPsi' p q).mono (by
      rw [uIcc_of_le hz1]; exact fun v hv ↦ lt_of_lt_of_le one_pos hv.1)).intervalIntegrable
  have hint' : IntervalIntegrable (fun v ↦ p * (p - q) * m * (v - 1)) volume 1 z :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable (μ := volume) _ _
  calc p * (p - q) * m / 2 * (z - 1) ^ 2 = ∫ v in (1 : ℝ)..z, p * (p - q) * m * (v - 1) := by
        rw [intervalIntegral.integral_const_mul, integral_sub_one]
        ring
    _ ≤ ∫ v in (1 : ℝ)..z, twoMonoPsi' p q v := integral_mono_on hz1 hint' hint hpt
    _ = twoMonoPhi p q z := by
        rw [← twoMonoPhi_sub_eq_integral hq one_pos (lt_of_lt_of_le one_pos hz1), twoMonoPhi_one,
          sub_zero]

/-- The lower bound on `[1/2, 1]`: `φ(z) ≥ c (1 − z)²` with `c = p m₂ min 1 (p−q) / 2`,
`m₂ = min 1 ((1/2)^{q−1})`. -/
theorem twoMonoPhi_quad_left {p q : ℝ} (hq : 0 < q) (hqp : q < p) {z : ℝ} (hz : 1 / 2 ≤ z)
    (hz1 : z ≤ 1) :
    p * min 1 ((1 / 2 : ℝ) ^ (q - 1)) * min 1 (p - q) / 2 * (z - 1) ^ 2 ≤ twoMonoPhi p q z := by
  have hp : 0 < p := by linarith
  have hr : 0 < p - q := by linarith
  have hz0 : 0 < z := by linarith
  set m := min 1 ((1 / 2 : ℝ) ^ (q - 1)) with hm
  have hm0 : 0 ≤ m := le_min zero_le_one (Real.rpow_nonneg (by norm_num) _)
  have hpt : ∀ v ∈ Icc z 1, p * m * min 1 (p - q) * (1 - v) ≤ -twoMonoPsi' p q v := fun v hv ↦ by
    have hv0 : 0 < v := lt_of_lt_of_le hz0 hv.1
    have hv1 : v ≤ 1 := hv.2
    have e : -twoMonoPsi' p q v = p * v ^ (q - 1) * (1 - v ^ (p - q)) := by
      unfold twoMonoPsi'
      rw [show p - 1 = (q - 1) + (p - q) by ring, Real.rpow_add hv0]
      ring
    have h1 := one_sub_rpow_ge hr hv0 hv1
    have hvm : m ≤ v ^ (q - 1) := by
      rcases le_or_gt 0 (q - 1) with h | h
      · exact (min_le_right _ _).trans (Real.rpow_le_rpow (by norm_num) (hz.trans hv.1) h)
      · exact (min_le_left _ _).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv0 hv1 h.le)
    rw [e]
    calc p * m * min 1 (p - q) * (1 - v) ≤ p * v ^ (q - 1) * (min 1 (p - q) * (1 - v)) := by
          have : 0 ≤ min 1 (p - q) * (1 - v) := mul_nonneg (le_min zero_le_one hr.le) (by linarith)
          calc p * m * min 1 (p - q) * (1 - v) = p * m * (min 1 (p - q) * (1 - v)) := by ring
            _ ≤ p * v ^ (q - 1) * (min 1 (p - q) * (1 - v)) := by gcongr
      _ ≤ p * v ^ (q - 1) * (1 - v ^ (p - q)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hp.le (Real.rpow_nonneg hv0.le _))
  have hint : IntervalIntegrable (fun v ↦ -twoMonoPsi' p q v) volume z 1 :=
    ((continuousOn_twoMonoPsi' p q).mono (by
      rw [uIcc_of_le hz1]; exact fun v hv ↦ lt_of_lt_of_le hz0 hv.1)).neg.intervalIntegrable
  have hint' : IntervalIntegrable (fun v ↦ p * m * min 1 (p - q) * (1 - v)) volume z 1 :=
    (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable (μ := volume) _ _
  have e : (∫ v in z..(1 : ℝ), (1 - v)) = (z - 1) ^ 2 / 2 := by
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    simp only [neg_sub]
    exact integral_sub_one z
  calc p * m * min 1 (p - q) / 2 * (z - 1) ^ 2
      = ∫ v in z..(1 : ℝ), p * m * min 1 (p - q) * (1 - v) := by
        rw [intervalIntegral.integral_const_mul, e]
        ring
    _ ≤ ∫ v in z..(1 : ℝ), -twoMonoPsi' p q v := integral_mono_on hz1 hint' hint hpt
    _ = twoMonoPhi p q z := by
        rw [intervalIntegral.integral_neg, ← twoMonoPhi_sub_eq_integral hq hz0 one_pos,
          twoMonoPhi_one]
        ring

/-- `φ` is antitone on `(0, 1]`: `φ(z) ≥ φ(1/2)` for `z ≤ 1/2`. -/
theorem twoMonoPhi_half_le {p q : ℝ} (hq : 0 < q) (hqp : q < p) {z : ℝ} (hz0 : 0 < z)
    (hz : z ≤ 1 / 2) : twoMonoPhi p q (1 / 2) ≤ twoMonoPhi p q z := by
  have h := twoMonoPhi_sub_eq_integral hq (p := p) hz0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hint : IntervalIntegrable (twoMonoPsi' p q) volume z (1 / 2) :=
    ((continuousOn_twoMonoPsi' p q).mono (by
      rw [uIcc_of_le hz]; exact fun v hv ↦ lt_of_lt_of_le hz0 hv.1)).intervalIntegrable
  have : (∫ v in z..(1 / 2 : ℝ), twoMonoPsi' p q v) ≤ ∫ v in z..(1 / 2 : ℝ), (0 : ℝ) :=
    integral_mono_on hz hint (continuous_const.intervalIntegrable (μ := volume) _ _)
      fun v hv ↦ twoMonoPsi'_nonpos hq hqp (lt_of_lt_of_le hz0 hv.1) (by linarith [hv.2])
  simp only [intervalIntegral.integral_const, smul_zero] at this
  linarith

/-- **The quadratic lower bound on `(0, z₁]`.** -/
theorem twoMonoPhi_quad_bound {p q : ℝ} (hq : 0 < q) (hqp : q < p) {z₁ : ℝ} (hz₁ : 1 ≤ z₁) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ z, 0 < z → z ≤ z₁ → c₁ * (z - 1) ^ 2 ≤ twoMonoPhi p q z := by
  have hp : 0 < p := by linarith
  have hr : 0 < p - q := by linarith
  set cR := p * (p - q) * min 1 (z₁ ^ (q - 2)) / 2 with hcR
  set cL := p * min 1 ((1 / 2 : ℝ) ^ (q - 1)) * min 1 (p - q) / 2 with hcL
  have hcR0 : 0 < cR := by
    rw [hcR]
    have : 0 < min 1 (z₁ ^ (q - 2)) := lt_min one_pos (Real.rpow_pos_of_pos (by linarith) _)
    positivity
  have hcL0 : 0 < cL := by
    rw [hcL]
    have h1 : 0 < min 1 ((1 / 2 : ℝ) ^ (q - 1)) :=
      lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _)
    have h2 : 0 < min 1 (p - q) := lt_min one_pos hr
    positivity
  refine ⟨min cR (cL / 4), lt_min hcR0 (by positivity), fun z hz0 hzz ↦ ?_⟩
  rcases le_or_gt 1 z with h1 | h1
  · calc min cR (cL / 4) * (z - 1) ^ 2 ≤ cR * (z - 1) ^ 2 := by gcongr; exact min_le_left _ _
      _ ≤ _ := twoMonoPhi_quad_right hq hqp hz₁ h1 hzz
  rcases le_or_gt (1 / 2) z with h2 | h2
  · calc min cR (cL / 4) * (z - 1) ^ 2 ≤ cL * (z - 1) ^ 2 := by
          gcongr
          exact (min_le_right _ _).trans (by linarith)
      _ ≤ _ := twoMonoPhi_quad_left hq hqp h2 h1.le
  · have hhalf := twoMonoPhi_quad_left hq hqp (p := p) (le_refl (1 / 2 : ℝ)) (by norm_num)
    have hφ := twoMonoPhi_half_le hq hqp hz0 h2.le
    have hsq : (z - 1) ^ 2 ≤ 1 := by nlinarith
    calc min cR (cL / 4) * (z - 1) ^ 2 ≤ cL / 4 * 1 := by
          gcongr
          exact min_le_right _ _
      _ = cL * (1 / 2 - 1) ^ 2 := by ring
      _ ≤ twoMonoPhi p q (1 / 2) := hhalf
      _ ≤ twoMonoPhi p q z := hφ

/-! ### Coercivity -/

/-- **Coercivity**: for `z ≥ max 2 ((2p/q)^{1/(p−q)})`, `φ(z) ≥ ½ (z − 1)^{min p 1}`. -/
theorem twoMonoPhi_coercive {p q : ℝ} (hq : 0 < q) (hqp : q < p) {z : ℝ}
    (hz : max 2 ((2 * p / q) ^ (1 / (p - q))) ≤ z) :
    1 / 2 * (z - 1) ^ min p 1 ≤ twoMonoPhi p q z := by
  have hp : 0 < p := by linarith
  have hr : 0 < p - q := by linarith
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hzc : (2 * p / q) ^ (1 / (p - q)) ≤ z := (le_max_right _ _).trans hz
  have hz0 : 0 < z := by linarith
  -- `(2p/q) ≤ z^{p−q}`
  have hpow : 2 * p / q ≤ z ^ (p - q) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hzc hr.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hr.ne', Real.rpow_one] at h
  -- `(p/q) z^q ≤ ½ z^p`
  have hqp' : p / q * z ^ q ≤ 1 / 2 * z ^ p := by
    have e : z ^ p = z ^ q * z ^ (p - q) := by
      rw [← Real.rpow_add hz0]; congr 1; ring
    rw [e]
    have hzq : 0 < z ^ q := Real.rpow_pos_of_pos hz0 _
    calc p / q * z ^ q = z ^ q * (p / q) := by ring
      _ ≤ z ^ q * (1 / 2 * z ^ (p - q)) := by
          refine mul_le_mul_of_nonneg_left ?_ hzq.le
          have : 2 * p / q = 2 * (p / q) := by ring
          linarith
      _ = 1 / 2 * (z ^ q * z ^ (p - q)) := by ring
  -- `(z − 1)^{min p 1} ≤ z^p`
  have hmin : (z - 1) ^ min p 1 ≤ z ^ p := by
    have hz1 : 1 ≤ z - 1 := by linarith
    calc (z - 1) ^ min p 1 ≤ z ^ min p 1 :=
          Real.rpow_le_rpow (by linarith) (by linarith) (le_min hp.le zero_le_one)
      _ ≤ z ^ p := Real.rpow_le_rpow_of_exponent_le (by linarith) (min_le_left _ _)
  have hψ1 : twoMonoPsi p q 1 = 1 - p / q := by simp [twoMonoPsi]
  have hpq1 : 1 ≤ p / q := by rw [le_div_iff₀ hq]; linarith
  unfold twoMonoPhi
  rw [hψ1]
  unfold twoMonoPsi
  nlinarith

/-! ### The observable `z^q` -/

/-- `|z^q − 1| ≤ max q 1 · |z − 1| · (1 + z)ⁿ` for `z > 0` and `q ≤ n`. -/
theorem abs_rpow_sub_one_le {q : ℝ} (hq : 0 < q) {n : ℕ} (hn : q ≤ n) {z : ℝ} (hz : 0 < z) :
    |z ^ q - 1| ≤ max q 1 * |z - 1| * (1 + z) ^ n := by
  have hz1n : 1 ≤ (1 + z) ^ n := one_le_pow₀ (by linarith)
  have hmq : q ≤ max q 1 := le_max_left _ _
  have hm1 : 1 ≤ max q 1 := le_max_right _ _
  rcases le_or_gt z 1 with hz1 | hz1
  · -- `z ≤ 1`: `1 − z^q ≤ max q 1 (1 − z)`
    have hzq : z ^ q ≤ 1 := Real.rpow_le_one hz.le hz1 hq.le
    have key : 1 - z ^ q ≤ max q 1 * (1 - z) := by
      rcases le_or_gt 1 q with hq1 | hq1
      · have := one_add_mul_self_le_rpow_one_add (s := z - 1) (by linarith) hq1
        rw [add_sub_cancel] at this
        nlinarith
      · have := Real.rpow_le_rpow_of_exponent_ge hz hz1 hq1.le
        rw [Real.rpow_one] at this
        nlinarith
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    calc -(z ^ q - 1) = 1 - z ^ q := by ring
      _ ≤ max q 1 * (1 - z) := key
      _ = max q 1 * -(z - 1) * 1 := by ring
      _ ≤ max q 1 * -(z - 1) * (1 + z) ^ n :=
          mul_le_mul_of_nonneg_left hz1n (mul_nonneg (by linarith) (by linarith))
  · -- `z > 1`
    have hzq : 1 ≤ z ^ q := Real.one_le_rpow hz1.le hq.le
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    rcases le_or_gt q 1 with hq1 | hq1
    · have := rpow_one_add_le_one_add_mul_self (s := z - 1) (by linarith) hq.le hq1
      rw [add_sub_cancel] at this
      calc z ^ q - 1 ≤ q * (z - 1) := by linarith
        _ ≤ max q 1 * (z - 1) * 1 := by rw [mul_one]; gcongr
        _ ≤ max q 1 * (z - 1) * (1 + z) ^ n := by gcongr
    · -- tangent bound at `z`: `z^q − 1 ≤ q z^{q−1} (z − 1)`
      have hB := one_add_mul_self_le_rpow_one_add (s := 1 / z - 1) (by
        have : 0 < 1 / z := by positivity
        linarith) hq1.le
      rw [add_sub_cancel, one_div, Real.inv_rpow hz.le] at hB
      have hzq0 : 0 < z ^ q := Real.rpow_pos_of_pos hz _
      have h2 : z ^ q * (1 + q * (z⁻¹ - 1)) ≤ 1 := by
        calc z ^ q * (1 + q * (z⁻¹ - 1)) ≤ z ^ q * (z ^ q)⁻¹ := mul_le_mul_of_nonneg_left hB hzq0.le
          _ = 1 := mul_inv_cancel₀ hzq0.ne'
      have hzq1 : z ^ q / z = z ^ (q - 1) := (Real.rpow_sub_one hz.ne' q).symm
      have htan : z ^ q - 1 ≤ q * z ^ (q - 1) * (z - 1) := by
        rw [← hzq1]
        have : z ^ q * (1 + q * (z⁻¹ - 1)) = z ^ q - q * (z ^ q / z) * (z - 1) := by
          field_simp
          ring
        linarith
      have hpow : z ^ (q - 1) ≤ (1 + z) ^ n := by
        calc z ^ (q - 1) ≤ (1 + z) ^ (q - 1) :=
              Real.rpow_le_rpow hz.le (by linarith) (by linarith)
          _ ≤ (1 + z) ^ (n : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = (1 + z) ^ n := Real.rpow_natCast _ _
      calc z ^ q - 1 ≤ q * z ^ (q - 1) * (z - 1) := htan
        _ ≤ max q 1 * (1 + z) ^ n * (z - 1) := by
            gcongr
        _ = max q 1 * (z - 1) * (1 + z) ^ n := by ring

/-- `√B ((1 + w/√B)^q − 1) → q w` as `B → ∞`. -/
theorem tendsto_sqrt_mul_rpow_sub_one (q w : ℝ) :
    Tendsto (fun B ↦ Real.sqrt B * ((1 + w / Real.sqrt B) ^ q - 1)) atTop (𝓝 (q * w)) := by
  by_cases hw : w = 0
  · subst hw
    simp only [zero_div, add_zero, Real.one_rpow, sub_self, mul_zero]
    exact tendsto_const_nhds
  have hd := Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := q) (Or.inl one_ne_zero)
  rw [hasDerivAt_iff_tendsto_slope] at hd
  simp only [Real.one_rpow, mul_one] at hd
  have hmap : Tendsto (fun B ↦ 1 + w / Real.sqrt B) atTop (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul w
      have h' : Tendsto (fun B ↦ 1 + w / Real.sqrt B) atTop (𝓝 (1 + w * 0)) :=
        (tendsto_const_nhds (x := (1 : ℝ))).add (by
          simpa [div_eq_mul_inv, Function.comp_def] using this)
      simpa using h'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
      have : w / Real.sqrt B ≠ 0 := div_ne_zero hw (Real.sqrt_pos.mpr hB).ne'
      simp [this]
  have := (hd.comp hmap).const_mul w
  rw [mul_comm q w]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  simp only [Function.comp_apply, slope_def_field, Real.one_rpow, add_sub_cancel_left]
  field_simp

end Laplace.Multi
