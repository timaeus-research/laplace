/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogTwoDSecondOrder

/-!
# The full polynomial-in-`log n` expansion at `d = 3` (grammar §4.2)

Unit 38 gave `Z₃(n) ~ (A/8) n^{-1/2} (log n)²`. Iterating unit 41's mechanism once more identifies
every term down to the constant. With `θ(x) = H(x) − A log x − C₀ ∈ [0, M/x]` for `x ≥ 1`,

  `H₂(L) = A log² L / 2 + C₀ log L + C₁ + θ₂(L)`,  `−M/L ≤ θ₂(L) ≤ 0`,

where `C₁ = ∫₀¹ H(x)/x dx + ∫₁^∞ θ(x)/x dx` (`logConst2`). Hence

  `Z₃(n) = n^{-1/2} P(log n) + O(n^{-1})`,
  `P(ℓ) = (A/8) ℓ² + (3A log b / 2 + C₀ / 2) ℓ + (9A log² b / 2 + 3 C₀ log b + C₁)`.

Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The remainder of the logarithmic primitive after its first two terms. -/
noncomputable def logRemainder (β a x : ℝ) : ℝ :=
  logPrimitive β a x - quadMass β a * Real.log x - logConst β a

theorem logRemainder_bounds (β a x : ℝ) (hβ : 0 < β) (hx : 1 ≤ x) :
    0 ≤ logRemainder β a x ∧ logRemainder β a x ≤ quadMoment β a / x :=
  logPrimitive_sub_log_sub_const_bounds β a x hβ hx

theorem logRemainder_div_bounds (β a x : ℝ) (hβ : 0 < β) (hx : 1 ≤ x) :
    0 ≤ logRemainder β a x / x ∧ logRemainder β a x / x ≤ quadMoment β a * x ^ (-2 : ℝ) := by
  have hx0 : (0 : ℝ) < x := one_pos.trans_le hx
  obtain ⟨h0, h1⟩ := logRemainder_bounds β a x hβ hx
  refine ⟨div_nonneg h0 hx0.le, ?_⟩
  rw [Real.rpow_neg hx0.le, Real.rpow_two, div_le_iff₀ hx0]
  calc logRemainder β a x ≤ quadMoment β a / x := h1
    _ = quadMoment β a * (x ^ 2)⁻¹ * x := by field_simp

theorem logPrimitive_continuousOn_Ioi (β a : ℝ) (hβ : 0 < β) :
    ContinuousOn (logPrimitive β a) (Ioi 0) :=
  ((logPrimitive_primitive_continuous β a hβ).continuousOn).congr fun x hx =>
    logPrimitive_eq_intervalIntegral β a x (le_of_lt hx)

theorem logRemainder_div_continuousOn (β a : ℝ) (hβ : 0 < β) :
    ContinuousOn (fun x => logRemainder β a x / x) (Ioi 1) := by
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  have hne : ∀ x ∈ Ioi (1 : ℝ), x ≠ 0 := fun x hx => (zero_lt_one.trans hx).ne'
  unfold logRemainder
  exact ((((logPrimitive_continuousOn_Ioi β a hβ).mono hsub).sub
    ((Real.continuousOn_log.mono hne).const_smul (quadMass β a))).sub continuousOn_const).div
    continuousOn_id hne

theorem logRemainder_div_integrableOn (β a c : ℝ) (hβ : 0 < β) (hc : 1 ≤ c) :
    IntegrableOn (fun x => logRemainder β a x / x) (Ioi c) := by
  have hc0 : (0 : ℝ) < c := one_pos.trans_le hc
  refine Integrable.mono' (g := fun x => quadMoment β a * x ^ (-2 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hc0).const_mul _)
    (((logRemainder_div_continuousOn β a hβ).mono (Ioi_subset_Ioi hc)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun x hx => ?_
  obtain ⟨h0, h1⟩ := logRemainder_div_bounds β a x hβ (hc.trans (le_of_lt hx))
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

theorem logRemainder_tail_bounds (β a L : ℝ) (hβ : 0 < β) (hL : 1 ≤ L) :
    0 ≤ (∫ x in Ioi L, logRemainder β a x / x)
      ∧ (∫ x in Ioi L, logRemainder β a x / x) ≤ quadMoment β a / L := by
  have hL0 : (0 : ℝ) < L := one_pos.trans_le hL
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun x hx =>
    (logRemainder_div_bounds β a x hβ (hL.trans (le_of_lt hx))).1, ?_⟩
  have hint : (∫ x in Ioi L, quadMoment β a * x ^ (-2 : ℝ)) = quadMoment β a / L := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hL0]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg hL0.le, Real.rpow_one]
    field_simp
  rw [← hint]
  exact setIntegral_mono_on (logRemainder_div_integrableOn β a L hβ hL)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hL0).const_mul _) measurableSet_Ioi
    fun x hx => (logRemainder_div_bounds β a x hβ (hL.trans (le_of_lt hx))).2

theorem integrableOn_log_div_Ioc (L : ℝ) :
    IntegrableOn (fun x : ℝ => Real.log x / x) (Ioc 1 L) := by
  have : ContinuousOn (fun x : ℝ => Real.log x / x) (Icc 1 L) :=
    (Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne').div
      continuousOn_id fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
  exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem integrableOn_inv_Ioc (L : ℝ) : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc 1 L) := by
  have : ContinuousOn (fun x : ℝ => x⁻¹) (Icc 1 L) :=
    continuousOn_inv₀.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
  exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The constant term of `H₂`: `C₁ = ∫₀¹ H/x + ∫₁^∞ θ/x`. -/
noncomputable def logConst2 (β a : ℝ) : ℝ :=
  (∫ x in Ioc (0 : ℝ) 1, logPrimitive β a x / x) + ∫ x in Ioi (1 : ℝ), logRemainder β a x / x

/-- **Exact constant-term identity for `H₂`**: for `L ≥ 1`,
`H₂(L) − (A log² L / 2 + C₀ log L + C₁) = −∫_L^∞ θ/x`. -/
theorem logLogPrimitive_sub_poly (β a L : ℝ) (hβ : 0 < β) (hL : 1 ≤ L) :
    logLogPrimitive β a L
      - (quadMass β a * Real.log L ^ 2 / 2 + logConst β a * Real.log L + logConst2 β a)
      = -∫ x in Ioi L, logRemainder β a x / x := by
  have hint := logPrimitive_div_integrableOn β a L hβ
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 L) :=
    Set.disjoint_left.2 fun x h1 h2 => (not_lt.2 h1.2) h2.1
  have hsplit := setIntegral_union hdisj measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hL))
    (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
    (f := fun x => logPrimitive β a x / x)
  rw [Ioc_union_Ioc_eq_Ioc zero_le_one hL] at hsplit
  have hθint := logRemainder_div_integrableOn β a 1 hβ le_rfl
  have hθsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl L)) measurableSet_Ioi
    (hθint.mono_set Ioc_subset_Ioi_self) (hθint.mono_set (Ioi_subset_Ioi hL))
    (f := fun x => logRemainder β a x / x)
  rw [Ioc_union_Ioi_eq_Ioi hL] at hθsplit
  have hpt : ∀ x ∈ Ioc (1 : ℝ) L, logPrimitive β a x / x
      = quadMass β a * (Real.log x / x) + logConst β a * x⁻¹ + logRemainder β a x / x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := one_pos.trans hx.1
    rw [logRemainder]
    field_simp
    ring
  have hlog : IntegrableOn (fun x : ℝ => quadMass β a * (Real.log x / x)) (Ioc 1 L) :=
    (integrableOn_log_div_Ioc L).const_mul _
  have hinv : IntegrableOn (fun x : ℝ => logConst β a * x⁻¹) (Ioc 1 L) :=
    (integrableOn_inv_Ioc L).const_mul _
  have h12 : IntegrableOn (fun x : ℝ => quadMass β a * (Real.log x / x) + logConst β a * x⁻¹)
      (Ioc 1 L) := hlog.add hinv
  have hθ' : IntegrableOn (fun x => logRemainder β a x / x) (Ioc 1 L) :=
    hθint.mono_set Ioc_subset_Ioi_self
  have hmid : (∫ x in Ioc (1 : ℝ) L, logPrimitive β a x / x)
      = quadMass β a * Real.log L ^ 2 / 2 + logConst β a * Real.log L
        + ∫ x in Ioc (1 : ℝ) L, logRemainder β a x / x := by
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, MeasureTheory.integral_add h12 hθ',
      MeasureTheory.integral_add hlog hinv, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul,
      integral_Ioc_log_div L hL, integral_Ioc_inv L hL]
    ring
  rw [logLogPrimitive, hsplit, hmid, logConst2, hθsplit]; ring

theorem logLogPrimitive_sub_poly_bounds (β a L : ℝ) (hβ : 0 < β) (hL : 1 ≤ L) :
    -(quadMoment β a / L) ≤ logLogPrimitive β a L
        - (quadMass β a * Real.log L ^ 2 / 2 + logConst β a * Real.log L + logConst2 β a)
      ∧ logLogPrimitive β a L
        - (quadMass β a * Real.log L ^ 2 / 2 + logConst β a * Real.log L + logConst2 β a) ≤ 0 := by
  rw [logLogPrimitive_sub_poly β a L hβ hL]
  obtain ⟨h0, h1⟩ := logRemainder_tail_bounds β a L hβ hL
  constructor <;> linarith

/-- The full polynomial coefficient of `Z₃`, as a function of `log n`. -/
noncomputable def threeDSecondOrderCoeff (β a b n : ℝ) : ℝ :=
  quadMass β a * (Real.log n / 2 + 3 * Real.log b) ^ 2 / 2
    + logConst β a * (Real.log n / 2 + 3 * Real.log b) + logConst2 β a

theorem threeDSecondOrderCoeff_eq (β a b n : ℝ) :
    threeDSecondOrderCoeff β a b n
      = quadMass β a / 8 * Real.log n ^ 2
        + (3 * quadMass β a * Real.log b / 2 + logConst β a / 2) * Real.log n
        + (9 * quadMass β a * Real.log b ^ 2 / 2 + 3 * logConst β a * Real.log b
          + logConst2 β a) := by
  unfold threeDSecondOrderCoeff; ring

/-- Explicit remainder: for `n ≥ max 1 b^{-6}`,
`−M/(b³ √n) ≤ √n Z₃(n) − P(log n) ≤ 0`. -/
theorem threeDIntegral_second_order_bounds (β a b n : ℝ) (hβ : 0 < β) (hb : 0 < b) (hn : 1 ≤ n)
    (hnb : 1 / b ^ 6 ≤ n) :
    -(quadMoment β a / b ^ 3 * (1 / Real.sqrt n))
        ≤ Real.sqrt n * threeDIntegral β a b n - threeDSecondOrderCoeff β a b n
      ∧ Real.sqrt n * threeDIntegral β a b n - threeDSecondOrderCoeff β a b n ≤ 0 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hL : 1 ≤ Real.sqrt n * b ^ 3 := by
    have h1 : (1 / b ^ 3) ^ 2 ≤ n := by rw [div_pow, one_pow, ← pow_mul]; exact hnb
    have h2 : 1 / b ^ 3 ≤ Real.sqrt n := by rw [Real.le_sqrt (by positivity) hn0.le]; exact h1
    calc (1 : ℝ) = 1 / b ^ 3 * b ^ 3 := by field_simp
      _ ≤ Real.sqrt n * b ^ 3 := by gcongr
  have hlogL : Real.log (Real.sqrt n * b ^ 3) = Real.log n / 2 + 3 * Real.log b := by
    rw [Real.log_mul hsn.ne' (by positivity), Real.log_sqrt hn0.le, Real.log_pow]
    push_cast; ring
  obtain ⟨h0, h1⟩ := logLogPrimitive_sub_poly_bounds β a (Real.sqrt n * b ^ 3) hβ hL
  rw [hlogL] at h0 h1
  have heq : Real.sqrt n * threeDIntegral β a b n - threeDSecondOrderCoeff β a b n
      = logLogPrimitive β a (Real.sqrt n * b ^ 3)
        - (quadMass β a * (Real.log n / 2 + 3 * Real.log b) ^ 2 / 2
          + logConst β a * (Real.log n / 2 + 3 * Real.log b) + logConst2 β a) := by
    rw [threeDIntegral_eq β a b n hn0 hb, threeDSecondOrderCoeff, ← mul_assoc,
      mul_inv_cancel₀ hsn.ne', one_mul]
  rw [heq]
  refine ⟨le_trans (le_of_eq ?_) h0, h1⟩
  field_simp

/-- **Full expansion of the `d = 3` log-squared integral**:
`Z₃(n) = n^{-1/2} P(log n) + O(n^{-1})`. -/
theorem threeDIntegral_second_order_isBigO (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) :
    (fun n : ℝ => threeDIntegral β a b n - n ^ (-(1 / 2 : ℝ)) * threeDSecondOrderCoeff β a b n)
      =O[atTop] fun n : ℝ => n⁻¹ := by
  apply IsBigO.of_bound (quadMoment β a / b ^ 3)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ 6)] with n hn hnb
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  obtain ⟨h0, h1⟩ := threeDIntegral_second_order_bounds β a b n hβ hb hn hnb
  have hpow : n ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hn0.le]
  have heq : threeDIntegral β a b n - n ^ (-(1 / 2 : ℝ)) * threeDSecondOrderCoeff β a b n
      = (Real.sqrt n)⁻¹
        * (Real.sqrt n * threeDIntegral β a b n - threeDSecondOrderCoeff β a b n) := by
    rw [hpow]; field_simp
  have habs : |Real.sqrt n * threeDIntegral β a b n - threeDSecondOrderCoeff β a b n|
      ≤ quadMoment β a / b ^ 3 * (1 / Real.sqrt n) := by
    rw [abs_le]
    exact ⟨h0, h1.trans (mul_nonneg (div_nonneg (quadMoment_nonneg β a) (by positivity))
      (by positivity))⟩
  rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn0), abs_mul,
    abs_of_pos (inv_pos.2 hsn)]
  calc (Real.sqrt n)⁻¹ * |Real.sqrt n * threeDIntegral β a b n - threeDSecondOrderCoeff β a b n|
      ≤ (Real.sqrt n)⁻¹ * (quadMoment β a / b ^ 3 * (1 / Real.sqrt n)) := by gcongr
    _ = quadMoment β a / b ^ 3 * ((Real.sqrt n)⁻¹ * (1 / Real.sqrt n)) := by ring
    _ = quadMoment β a / b ^ 3 * n⁻¹ := by
        rw [one_div, ← mul_inv, Real.mul_self_sqrt hn0.le]

/-- **The constant below `(log n)²` and `log n`**:
`√n Z₃(n) − (A/8) log² n − (3A log b/2 + C₀/2) log n → 9A log² b/2 + 3 C₀ log b + C₁`. -/
theorem threeDIntegral_second_order_tendsto (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) :
    Tendsto (fun n : ℝ => Real.sqrt n * threeDIntegral β a b n
        - quadMass β a / 8 * Real.log n ^ 2
        - (3 * quadMass β a * Real.log b / 2 + logConst β a / 2) * Real.log n)
      atTop (𝓝 (9 * quadMass β a * Real.log b ^ 2 / 2 + 3 * logConst β a * Real.log b
        + logConst2 β a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun n => quadMoment β a / b ^ 3 * (1 / Real.sqrt n))
    (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ 6)] with n hn hnb
    obtain ⟨h0, h1⟩ := threeDIntegral_second_order_bounds β a b n hβ hb hn hnb
    rw [threeDSecondOrderCoeff_eq] at h0 h1
    rw [Real.norm_eq_abs, show Real.sqrt n * threeDIntegral β a b n
        - quadMass β a / 8 * Real.log n ^ 2
        - (3 * quadMass β a * Real.log b / 2 + logConst β a / 2) * Real.log n
        - (9 * quadMass β a * Real.log b ^ 2 / 2 + 3 * logConst β a * Real.log b + logConst2 β a)
      = Real.sqrt n * threeDIntegral β a b n
        - (quadMass β a / 8 * Real.log n ^ 2
          + (3 * quadMass β a * Real.log b / 2 + logConst β a / 2) * Real.log n
          + (9 * quadMass β a * Real.log b ^ 2 / 2 + 3 * logConst β a * Real.log b
            + logConst2 β a)) by ring, abs_le]
    exact ⟨h0, h1.trans (mul_nonneg (div_nonneg (quadMoment_nonneg β a) (by positivity))
      (by positivity))⟩
  · have h := (tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop).const_mul (quadMoment β a / b ^ 3)
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp [Function.comp, one_div]

end Laplace.Grammar
