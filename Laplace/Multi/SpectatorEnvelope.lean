/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthUniform

/-!
# The spectator envelope

One-variable integrability facts for the spectator coordinates of an active-truth face:
`x^{d−1} (C + a|log x|)^k` is integrable on `(0, ρ)` for `d > 0`
(`integrableOn_rpow_mul_log_pow`, through the exponential substitution `x = e^v` and the envelope
`(|v|+1)^k ≤ C e^{d|v|/2}`), the elementary `C + ∑ aᵢ ≤ ∏ (C + aᵢ)` for `C ≥ 1` (`add_sum_le_prod`,
which turns the joint logarithmic loss into a product of one-variable losses), and
`∫_0^ρ x^{d−1} = ρ^d/d` (`integral_Ioo_rpow_sub_one`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

/-- `e^{cv}` is integrable on `(−∞, b)` for `c > 0`. -/
theorem integrable_indicator_Iio_exp {c : ℝ} (hc : 0 < c) (b : ℝ) :
    Integrable ((Iio b).indicator fun v ↦ exp (c * v)) := by
  have h := ((integrableOn_exp_neg_mul_Ioi' hc (-b)).integrable_indicator
    measurableSet_Ioi).comp_neg
  refine h.congr (Eventually.of_forall fun v ↦ ?_)
  simp only [Set.indicator_apply, mem_Ioi, mem_Iio, neg_lt_neg_iff, mul_neg, neg_neg]

/-- `e^{dv} (C + a|v|)^k` is integrable on `(−∞, b)` for `d > 0`. -/
theorem integrable_indicator_Iio_exp_mul_pow {d C a : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (b : ℝ) (k : ℕ) :
    Integrable ((Iio b).indicator fun v ↦ exp (d * v) * (C + a * |v|) ^ k) := by
  set K : ℝ := (C + a) ^ k * (k / (d / 2) + 1) ^ k with hK
  have hK0 : 0 ≤ K := by positivity
  have hint := ((integrable_indicator_Iio_exp (by linarith : 0 < 3 * d / 2) b).add
    (integrable_indicator_Iio_exp (half_pos hd) b)).const_mul K
  refine hint.mono' ?_ (Eventually.of_forall fun v ↦ ?_)
  · exact ((Continuous.measurable (by fun_prop)).indicator measurableSet_Iio).aestronglyMeasurable
  · simp only [Pi.add_apply]
    by_cases hv : v ∈ Iio b
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Set.indicator_of_mem hv,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : C + a * |v| ≤ (C + a) * (|v| + 1) := by nlinarith [abs_nonneg v]
      have h2 : (C + a * |v|) ^ k ≤ (C + a) ^ k * (|v| + 1) ^ k := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) h1 k
      have h3 := pow_abs_add_le_exp (half_pos hd) zero_le_one k v
      have h4 := exp_abs_le_add (d / 2) v
      have e1 : exp (d * v) * exp (d / 2 * v) = exp (3 * d / 2 * v) := by
        rw [← Real.exp_add]; congr 1; ring
      have e2 : exp (d * v) * exp (-(d / 2 * v)) = exp (d / 2 * v) := by
        rw [← Real.exp_add]; congr 1; ring
      calc exp (d * v) * (C + a * |v|) ^ k
          ≤ exp (d * v) * ((C + a) ^ k * ((k / (d / 2) + 1) ^ k * exp (d / 2 * |v|))) :=
            mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
              (exp_pos _).le
        _ ≤ exp (d * v) * ((C + a) ^ k * ((k / (d / 2) + 1) ^ k *
              (exp (d / 2 * v) + exp (-(d / 2 * v))))) := by
            gcongr
        _ = K * (exp (d * v) * exp (d / 2 * v) + exp (d * v) * exp (-(d / 2 * v))) := by
            rw [hK]; ring
        _ = K * (exp (3 * d / 2 * v) + exp (d / 2 * v)) := by rw [e1, e2]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, Set.indicator_of_notMem hv,
        norm_zero, add_zero, mul_zero]

/-- `x^{d−1} (C + a|log x|)^k` is integrable on `(0, ρ)` for `d > 0`. -/
theorem integrableOn_rpow_mul_log_pow {d C a ρ : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hρ : 0 < ρ) (k : ℕ) :
    IntegrableOn (fun x ↦ x ^ (d - 1) * (C + a * |log x|) ^ k) (Ioo 0 ρ) := by
  have key : IntegrableOn ((Iio ρ).indicator fun x ↦ x ^ (d - 1) * (C + a * |log x|) ^ k)
      (Ioi 0) := by
    rw [← integrable_comp_exp_univ_iff]
    refine (integrable_indicator_Iio_exp_mul_pow hd hC ha (log ρ) k).congr
      (Eventually.of_forall fun v ↦ ?_)
    beta_reduce
    by_cases hv : v < log ρ
    · have hv' : exp v ∈ Iio ρ := by rwa [mem_Iio, ← Real.lt_log_iff_exp_lt hρ]
      rw [Set.indicator_of_mem (mem_Iio.mpr hv), Set.indicator_of_mem hv', Real.log_exp,
        ← Real.exp_mul, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · have hv' : exp v ∉ Iio ρ := by rwa [mem_Iio, ← Real.lt_log_iff_exp_lt hρ]
      rw [Set.indicator_of_notMem (fun h ↦ hv (mem_Iio.mp h)), Set.indicator_of_notMem hv',
        mul_zero]
  have := (integrable_indicator_iff measurableSet_Iio).mp key
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iio, Set.inter_comm,
    Ioi_inter_Iio] at this
  exact this

/-- `C + ∑ aᵢ ≤ C ∏ (1 + aᵢ)` for `C ≥ 1` and `aᵢ ≥ 0`. -/
theorem add_sum_le_prod {ι : Type*} (s : Finset ι) {C : ℝ} (hC : 1 ≤ C) {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) : C + ∑ i ∈ s, a i ≤ C * ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ ↦ ha i
    have hP : 1 ≤ ∏ i ∈ s, (1 + a i) := by
      calc (1 : ℝ) = ∏ i ∈ s, (1 : ℝ) := by simp
        _ ≤ ∏ i ∈ s, (1 + a i) :=
          Finset.prod_le_prod (fun i _ ↦ zero_le_one) fun i _ ↦ by linarith [ha i]
    have h1 := mul_le_mul_of_nonneg_left ih (by linarith [ha j] : 0 ≤ 1 + a j)
    nlinarith [mul_nonneg (ha j) hS, mul_nonneg (sub_nonneg.mpr hC) (ha j),
      mul_le_mul_of_nonneg_left hP (mul_nonneg (by linarith : (0 : ℝ) ≤ C) (ha j))]

/-- `∫_0^ρ x^{d−1} dx = ρ^d / d` for `d > 0`. -/
theorem integral_Ioo_rpow_sub_one {d ρ : ℝ} (hd : 0 < d) (hρ : 0 < ρ) :
    ∫ x in Ioo (0 : ℝ) ρ, x ^ (d - 1) = ρ ^ d / d := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le,
    integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.zero_rpow hd.ne', sub_zero]

end Laplace.Multi
