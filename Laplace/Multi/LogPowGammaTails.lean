/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.LogGammaTails

/-!
# Truncated log-power Gamma integrals

The integrals `Λ_{j,r}(u) = ∫₀ᵘ s^j e^{-s} (log s)^r ds` and their full versions
`M_{j,r} = ∫₀^∞ s^j e^{-s} (log s)^r ds`, for all `j, r : ℕ`, with the tail bound
`|M_{j,r} − Λ_{j,r}(u)| ≤ (j+r+2)!/u²` for `u ≥ 1` (`abs_logPowGammaTrunc_sub_le`). These are the
coefficients of the binomial expansion of the moments of the state density `(−log ℓ)^k dℓ`
(`MultiplicityModelK`). Near `0` the integrand is dominated by `(2r)^r s^{-1/2}` (from
`|log s| ≤ 2r s^{-1/(2r)}`), beyond `1` by `s^{j+r} e^{-s}` (from `log s ≤ s`).
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

/-- `Λ_{j,r}(u) = ∫₀ᵘ s^j e^{-s} (log s)^r ds`. -/
noncomputable def logPowGammaTrunc (j r : ℕ) (u : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..u, s ^ j * Real.exp (-s) * Real.log s ^ r

/-- `M_{j,r} = ∫₀^∞ s^j e^{-s} (log s)^r ds`. -/
noncomputable def logPowGammaFull (j r : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ j * Real.exp (-s) * Real.log s ^ r

/-- `log y ≤ y^a / a` for `y ≥ 1`, `a > 0`. -/
theorem log_le_rpow_div' {y a : ℝ} (hy : 1 ≤ y) (ha : 0 < a) : Real.log y ≤ y ^ a / a := by
  have hy0 : 0 < y := by linarith
  have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 a)
  rw [Real.log_rpow hy0] at h1
  rw [le_div_iff₀ ha]
  linarith [Real.rpow_nonneg hy0.le a]

/-- `|log s|^r ≤ (2r)^r s^{-1/2}` on `(0, 1]` for `r ≥ 1`. -/
theorem abs_log_pow_le_rpow {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    |Real.log s| ^ r ≤ (2 * r : ℝ) ^ r * s ^ (-(1 / 2 : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hinv : 1 ≤ s⁻¹ := one_le_inv_iff₀.mpr ⟨hs0, hs1⟩
  have h1 : |Real.log s| = Real.log s⁻¹ := by
    rw [Real.log_inv, abs_of_nonpos (Real.log_nonpos hs0.le hs1)]
  have h2 : Real.log s⁻¹ ≤ (s⁻¹) ^ (1 / (2 * r : ℝ)) / (1 / (2 * r : ℝ)) :=
    log_le_rpow_div' hinv (by positivity)
  have h3 : (s⁻¹) ^ (1 / (2 * r : ℝ)) / (1 / (2 * r : ℝ)) =
      (2 * r : ℝ) * s ^ (-(1 / (2 * r : ℝ))) := by
    rw [Real.inv_rpow hs0.le, ← Real.rpow_neg hs0.le]
    field_simp
  rw [h1]
  have h4 : 0 ≤ Real.log s⁻¹ := Real.log_nonneg hinv
  calc Real.log s⁻¹ ^ r ≤ ((2 * r : ℝ) * s ^ (-(1 / (2 * r : ℝ)))) ^ r :=
        pow_le_pow_left₀ h4 (h2.trans_eq h3) r
    _ = (2 * r : ℝ) ^ r * s ^ (-(1 / 2 : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast (s ^ _) r, ← Real.rpow_mul hs0.le]
        congr 2
        field_simp

/-- `s^j e^{-s} (log s)^r` is integrable on `(0, 1]`. -/
theorem integrableOn_pow_mul_exp_neg_mul_log_pow_Ioc (j r : ℕ) :
    IntegrableOn (fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s ^ r) (Ioc 0 1) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    refine (integrableOn_const (C := (1 : ℝ)) (by simp)).mono' (Measurable.aestronglyMeasurable
      (by fun_prop : Measurable fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s ^ 0)) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs ↦ ?_)
    simp only [pow_zero, mul_one, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hs.1.le _), Real.abs_exp]
    have h1 : s ^ j ≤ 1 := pow_le_one₀ hs.1.le hs.2
    have h2 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
    calc s ^ j * Real.exp (-s) ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  · have hint : IntegrableOn (fun s : ℝ ↦ (2 * r : ℝ) ^ r * s ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
      refine ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))).const_mul _
    refine hint.mono' (by fun_prop : Measurable fun s : ℝ ↦ s ^ j * Real.exp (-s) *
      Real.log s ^ r).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs ↦ ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs.1.le _), Real.abs_exp, abs_pow]
    have h1 : s ^ j ≤ 1 := pow_le_one₀ hs.1.le hs.2
    have h2 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
    calc s ^ j * Real.exp (-s) * |Real.log s| ^ r ≤ 1 * 1 * |Real.log s| ^ r := by gcongr
      _ = |Real.log s| ^ r := by ring
      _ ≤ (2 * r : ℝ) ^ r * s ^ (-(1 / 2 : ℝ)) := abs_log_pow_le_rpow hr hs.1 hs.2

/-- `s^j e^{-s} (log s)^r` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg_mul_log_pow_Ioi (j r : ℕ) :
    IntegrableOn (fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s ^ r) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  refine ⟨integrableOn_pow_mul_exp_neg_mul_log_pow_Ioc j r, ?_⟩
  refine ((integrableOn_pow_mul_exp_neg_Ioi (j + r)).mono_set (Ioi_subset_Ioi zero_le_one)).mono'
    (Measurable.aestronglyMeasurable
      (by fun_prop : Measurable fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s ^ r)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs ↦ ?_)
  have hs1 : 1 < s := hs
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  simp only [Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs0.le _), Real.abs_exp, abs_pow,
    abs_of_nonneg (Real.log_nonneg hs1.le), pow_add]
  have hlog : Real.log s ≤ s := by linarith [Real.log_le_sub_one_of_pos hs0]
  calc s ^ j * Real.exp (-s) * Real.log s ^ r ≤ s ^ j * Real.exp (-s) * s ^ r := by
        gcongr
        exact Real.log_nonneg hs1.le
    _ = s ^ j * s ^ r * Real.exp (-s) := by ring

/-- `(log s)^r` is interval integrable on every interval. -/
theorem intervalIntegrable_log_pow' (r : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun s : ℝ ↦ Real.log s ^ r) volume a b := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp only [pow_zero]
    exact intervalIntegrable_const
  refine intervalIntegrable_of_even (fun x ↦ by simp [Real.log_neg_eq_log]) (fun x hx ↦ ?_)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
  have h1 : IntegrableOn (fun s : ℝ ↦ (2 * r : ℝ) ^ r * s ^ (-(1 / 2 : ℝ)) + x ^ r) (Ioc 0 x) :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))).const_mul _).add
      (integrableOn_const measure_Ioc_lt_top.ne)
  refine h1.mono' (by fun_prop : Measurable fun s : ℝ ↦ Real.log s ^ r).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow]
  rcases le_or_gt s 1 with hs1 | hs1
  · calc |Real.log s| ^ r ≤ (2 * r : ℝ) ^ r * s ^ (-(1 / 2 : ℝ)) :=
          abs_log_pow_le_rpow hr hs.1 hs1
      _ ≤ (2 * r : ℝ) ^ r * s ^ (-(1 / 2 : ℝ)) + x ^ r :=
          le_add_of_nonneg_right (pow_nonneg hx.le _)
  · have hls : |Real.log s| ≤ s := by
      rw [abs_of_nonneg (Real.log_nonneg hs1.le)]
      linarith [Real.log_le_sub_one_of_pos hs.1]
    calc |Real.log s| ^ r ≤ s ^ r := pow_le_pow_left₀ (abs_nonneg _) hls r
      _ ≤ x ^ r := pow_le_pow_left₀ hs.1.le hs.2 r
      _ ≤ (2 * r : ℝ) ^ r * s ^ (-(1 / 2 : ℝ)) + x ^ r :=
          le_add_of_nonneg_left (by positivity)

theorem intervalIntegrable_pow_mul_exp_neg_mul_log_pow (j r : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s ^ r) volume a b :=
  (intervalIntegrable_log_pow' r).continuousOn_mul
    (by fun_prop : Continuous fun s : ℝ ↦ s ^ j * Real.exp (-s)).continuousOn

/-- **Tail bound**: `|∫_u^∞ s^j e^{-s} (log s)^r| ≤ (j+r+2)!/u²` for `u ≥ 1`. -/
theorem logPowGammaTail_abs_le (j r : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |∫ s in Ioi u, s ^ j * Real.exp (-s) * Real.log s ^ r| ≤
      ((j + r + 2).factorial : ℝ) / u ^ 2 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hI : IntegrableOn (fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s ^ r) (Ioi u) :=
    (integrableOn_pow_mul_exp_neg_mul_log_pow_Ioi j r).mono_set (Ioi_subset_Ioi hu0.le)
  have hI1 : IntegrableOn (fun s : ℝ ↦ s ^ (j + r) * Real.exp (-s)) (Ioi u) :=
    (integrableOn_pow_mul_exp_neg_Ioi (j + r)).mono_set (Ioi_subset_Ioi hu0.le)
  calc |∫ s in Ioi u, s ^ j * Real.exp (-s) * Real.log s ^ r|
      ≤ ∫ s in Ioi u, |s ^ j * Real.exp (-s) * Real.log s ^ r| := abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioi u, s ^ (j + r) * Real.exp (-s) := by
        refine setIntegral_mono_on hI.abs hI1 measurableSet_Ioi fun s hs ↦ ?_
        have hs1 : u < s := hs
        have hs0 : 0 < s := lt_trans hu0 hs1
        have hs1' : 1 ≤ s := hu.trans hs1.le
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs0.le _), Real.abs_exp, abs_pow,
          abs_of_nonneg (Real.log_nonneg hs1'), pow_add]
        have hlog : Real.log s ≤ s := by linarith [Real.log_le_sub_one_of_pos hs0]
        calc s ^ j * Real.exp (-s) * Real.log s ^ r ≤ s ^ j * Real.exp (-s) * s ^ r := by
              gcongr
              exact Real.log_nonneg hs1'
          _ = s ^ j * s ^ r * Real.exp (-s) := by ring
    _ ≤ ((j + r + 2).factorial : ℝ) / u ^ 2 := gammaTail_le (j + r) hu

/-- `Λ_{j,r}(u) = M_{j,r} − ∫_u^∞`. -/
theorem logPowGammaTrunc_eq (j r : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    logPowGammaTrunc j r u =
      logPowGammaFull j r - ∫ s in Ioi u, s ^ j * Real.exp (-s) * Real.log s ^ r := by
  unfold logPowGammaTrunc logPowGammaFull
  rw [intervalIntegral.integral_of_le hu, eq_sub_iff_add_eq,
    ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_pow_mul_exp_neg_mul_log_pow_Ioi j r).mono_set (Ioc_subset_Ioi_self))
      ((integrableOn_pow_mul_exp_neg_mul_log_pow_Ioi j r).mono_set (Ioi_subset_Ioi hu)),
    Ioc_union_Ioi_eq_Ioi hu]

/-- **The truncated log-power Gamma integrals converge with an `O(1/u²)` tail.** -/
theorem abs_logPowGammaTrunc_sub_le (j r : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |logPowGammaTrunc j r u - logPowGammaFull j r| ≤ ((j + r + 2).factorial : ℝ) / u ^ 2 := by
  rw [logPowGammaTrunc_eq j r (by linarith), sub_sub_cancel_left, abs_neg]
  exact logPowGammaTail_abs_le j r hu

/-- `M_{j,0} = j!`. -/
theorem logPowGammaFull_zero (j : ℕ) : logPowGammaFull j 0 = (j.factorial : ℝ) := by
  unfold logPowGammaFull
  simp only [pow_zero, mul_one]
  exact integral_pow_mul_exp_neg_Ioi j

/-- `M_{j,1} = logGammaFull j`. -/
theorem logPowGammaFull_one (j : ℕ) : logPowGammaFull j 1 = logGammaFull j := by
  unfold logPowGammaFull logGammaFull
  simp only [pow_one]

theorem continuous_logPowGammaTrunc (j r : ℕ) : Continuous (logPowGammaTrunc j r) :=
  continuous_primitive (intervalIntegrable_pow_mul_exp_neg_mul_log_pow j r) 0

end Laplace.Multi
