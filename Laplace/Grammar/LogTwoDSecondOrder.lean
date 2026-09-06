/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MixedThreeD

/-!
# The next-order term in the `log n` case (grammar §4.2, `d = 2`)

Unit 35 gave `Z₂(n) ~ (A/2) n^{-1/2} log n` with `A = quadMass = S_{1/2}(a)/2`. Here the
`n^{-1/2}` term below the logarithm is identified exactly. The logarithmic primitive satisfies

  `H(L) = A log L + C₀ + θ(L)`,  `0 ≤ θ(L) ≤ M/L`  (`L ≥ 1`),

with the explicit constant `C₀ = ∫₀¹ F(x)/x dx − ∫₁^∞ (A − F(x))/x dx` (`logConst`), so that

  `Z₂(n) = n^{-1/2} ((A/2) log n + 2A log b + C₀) + O(n^{-1})`,

and `√n Z₂(n) − (A/2) log n → 2A log b + C₀`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- On `x > 0`, `0 ≤ (A − F(x))/x ≤ M x^{-2}`. -/
theorem tail_div_bounds (β a x : ℝ) (hβ : 0 < β) (hx : 0 < x) :
    0 ≤ (quadMass β a - quadPrimitive β a x) / x
      ∧ (quadMass β a - quadPrimitive β a x) / x ≤ quadMoment β a * x ^ (-2 : ℝ) := by
  refine ⟨div_nonneg (quadMass_sub_primitive_nonneg β a x hβ hx.le) hx.le, ?_⟩
  have h := quadMass_sub_primitive_le β a x hβ hx
  rw [Real.rpow_neg hx.le, Real.rpow_two, div_le_iff₀ hx]
  calc quadMass β a - quadPrimitive β a x ≤ quadMoment β a / x := h
    _ = quadMoment β a * (x ^ 2)⁻¹ * x := by field_simp

theorem tail_div_integrableOn (β a c : ℝ) (hβ : 0 < β) (hc : 0 < c) :
    IntegrableOn (fun x => (quadMass β a - quadPrimitive β a x) / x) (Ioi c) := by
  refine Integrable.mono' (g := fun x => quadMoment β a * x ^ (-2 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hc).const_mul _)
    ((continuous_const.sub (quadPrimitive_continuous β a)).measurable.div
      measurable_id).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx0 : (0 : ℝ) < c := hc
  obtain ⟨h0, h1⟩ := tail_div_bounds β a x hβ (hc.trans hx)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- `∫_L^∞ (A − F(x))/x dx ≤ M/L`. -/
theorem tail_integral_le (β a L : ℝ) (hβ : 0 < β) (hL : 0 < L) :
    (∫ x in Ioi L, (quadMass β a - quadPrimitive β a x) / x) ≤ quadMoment β a / L := by
  have hint : (∫ x in Ioi L, quadMoment β a * x ^ (-2 : ℝ)) = quadMoment β a / L := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hL]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg hL.le, Real.rpow_one]
    field_simp
  rw [← hint]
  refine setIntegral_mono_on (tail_div_integrableOn β a L hβ hL)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hL).const_mul _) measurableSet_Ioi
    fun x hx => (tail_div_bounds β a x hβ (hL.trans hx)).2

theorem tail_integral_nonneg (β a L : ℝ) (hβ : 0 < β) (hL : 0 < L) :
    0 ≤ ∫ x in Ioi L, (quadMass β a - quadPrimitive β a x) / x :=
  setIntegral_nonneg measurableSet_Ioi fun x hx => (tail_div_bounds β a x hβ (hL.trans hx)).1

/-- The constant term of the logarithmic primitive: `C₀ = ∫₀¹ F/x − ∫₁^∞ (A − F)/x`. -/
noncomputable def logConst (β a : ℝ) : ℝ :=
  (∫ x in Ioc (0 : ℝ) 1, quadPrimitive β a x / x)
    - ∫ x in Ioi (1 : ℝ), (quadMass β a - quadPrimitive β a x) / x

/-- **Sharp constant-term expansion**: for `L ≥ 1`,
`H(L) − A log L − C₀ = ∫_L^∞ (A − F)/x ∈ [0, M/L]`. -/
theorem logPrimitive_sub_log_sub_const (β a L : ℝ) (hβ : 0 < β) (hL : 1 ≤ L) :
    logPrimitive β a L - quadMass β a * Real.log L - logConst β a
      = ∫ x in Ioi L, (quadMass β a - quadPrimitive β a x) / x := by
  have hint := tail_div_integrableOn β a 1 hβ one_pos
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl L)) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hL))
    (f := fun x => (quadMass β a - quadPrimitive β a x) / x)
  rw [Ioc_union_Ioi_eq_Ioi hL] at hsplit
  rw [logPrimitive_split β a L hβ hL, logConst, hsplit]; ring

theorem logPrimitive_sub_log_sub_const_bounds (β a L : ℝ) (hβ : 0 < β) (hL : 1 ≤ L) :
    0 ≤ logPrimitive β a L - quadMass β a * Real.log L - logConst β a
      ∧ logPrimitive β a L - quadMass β a * Real.log L - logConst β a ≤ quadMoment β a / L := by
  have hL0 : (0 : ℝ) < L := one_pos.trans_le hL
  rw [logPrimitive_sub_log_sub_const β a L hβ hL]
  exact ⟨tail_integral_nonneg β a L hβ hL0, tail_integral_le β a L hβ hL0⟩

/-- The two-term coefficient of `Z₂`: `(A/2) log n + 2A log b + C₀`. -/
noncomputable def twoDSecondOrderCoeff (β a b n : ℝ) : ℝ :=
  quadMass β a / 2 * Real.log n + 2 * quadMass β a * Real.log b + logConst β a

/-- Explicit remainder: for `n ≥ max 1 b^{-4}`,
`0 ≤ √n Z₂(n) − ((A/2) log n + 2A log b + C₀) ≤ M/(b² √n)`. -/
theorem twoDIntegral_second_order_bounds (β a b n : ℝ) (hβ : 0 < β) (hb : 0 < b) (hn : 1 ≤ n)
    (hnb : 1 / b ^ 4 ≤ n) :
    0 ≤ Real.sqrt n * twoDIntegral β a b n - twoDSecondOrderCoeff β a b n
      ∧ Real.sqrt n * twoDIntegral β a b n - twoDSecondOrderCoeff β a b n
        ≤ quadMoment β a / b ^ 2 * (1 / Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hL : 1 ≤ Real.sqrt n * b ^ 2 := by
    have h1 : (1 / b ^ 2) ^ 2 ≤ n := by rw [div_pow, one_pow, ← pow_mul]; exact hnb
    have h2 : 1 / b ^ 2 ≤ Real.sqrt n := by rw [Real.le_sqrt (by positivity) hn0.le]; exact h1
    calc (1 : ℝ) = 1 / b ^ 2 * b ^ 2 := by field_simp
      _ ≤ Real.sqrt n * b ^ 2 := by gcongr
  have hlogL : Real.log (Real.sqrt n * b ^ 2) = Real.log n / 2 + 2 * Real.log b := by
    rw [Real.log_mul hsn.ne' (by positivity), Real.log_sqrt hn0.le, Real.log_pow]
    push_cast; ring
  obtain ⟨h0, h1⟩ := logPrimitive_sub_log_sub_const_bounds β a (Real.sqrt n * b ^ 2) hβ hL
  rw [hlogL] at h0 h1
  have heq : Real.sqrt n * twoDIntegral β a b n - twoDSecondOrderCoeff β a b n
      = logPrimitive β a (Real.sqrt n * b ^ 2)
        - quadMass β a * (Real.log n / 2 + 2 * Real.log b) - logConst β a := by
    rw [twoDIntegral_eq β a b n hn0 hb, twoDSecondOrderCoeff, ← mul_assoc,
      mul_inv_cancel₀ hsn.ne', one_mul]; ring
  rw [heq]
  refine ⟨h0, h1.trans (le_of_eq ?_)⟩
  field_simp

/-- **Two-term expansion of the `d = 2` log integral**:
`Z₂(n) = n^{-1/2} ((A/2) log n + 2A log b + C₀) + O(n^{-1})`. -/
theorem twoDIntegral_second_order_isBigO (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) :
    (fun n : ℝ => twoDIntegral β a b n - n ^ (-(1 / 2 : ℝ)) * twoDSecondOrderCoeff β a b n)
      =O[atTop] fun n : ℝ => n⁻¹ := by
  apply IsBigO.of_bound (quadMoment β a / b ^ 2)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ 4)] with n hn hnb
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  obtain ⟨h0, h1⟩ := twoDIntegral_second_order_bounds β a b n hβ hb hn hnb
  have hpow : n ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hn0.le]
  have heq : twoDIntegral β a b n - n ^ (-(1 / 2 : ℝ)) * twoDSecondOrderCoeff β a b n
      = (Real.sqrt n)⁻¹ * (Real.sqrt n * twoDIntegral β a b n - twoDSecondOrderCoeff β a b n) := by
    rw [hpow]; field_simp
  rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn0), abs_mul,
    abs_of_pos (inv_pos.2 hsn), abs_of_nonneg h0]
  calc (Real.sqrt n)⁻¹ * (Real.sqrt n * twoDIntegral β a b n - twoDSecondOrderCoeff β a b n)
      ≤ (Real.sqrt n)⁻¹ * (quadMoment β a / b ^ 2 * (1 / Real.sqrt n)) := by gcongr
    _ = quadMoment β a / b ^ 2 * ((Real.sqrt n)⁻¹ * (1 / Real.sqrt n)) := by ring
    _ = quadMoment β a / b ^ 2 * n⁻¹ := by
        rw [one_div, ← mul_inv, Real.mul_self_sqrt hn0.le]

/-- **The constant below the logarithm**: `√n Z₂(n) − (A/2) log n → 2A log b + C₀`. -/
theorem twoDIntegral_second_order_tendsto (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) :
    Tendsto (fun n : ℝ => Real.sqrt n * twoDIntegral β a b n - quadMass β a / 2 * Real.log n)
      atTop (𝓝 (2 * quadMass β a * Real.log b + logConst β a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun n => quadMoment β a / b ^ 2 * (1 / Real.sqrt n))
    (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ 4)] with n hn hnb
    obtain ⟨h0, h1⟩ := twoDIntegral_second_order_bounds β a b n hβ hb hn hnb
    rw [twoDSecondOrderCoeff] at h0 h1
    rw [Real.norm_eq_abs, show Real.sqrt n * twoDIntegral β a b n - quadMass β a / 2 * Real.log n
      - (2 * quadMass β a * Real.log b + logConst β a)
      = Real.sqrt n * twoDIntegral β a b n - (quadMass β a / 2 * Real.log n
        + 2 * quadMass β a * Real.log b + logConst β a) by ring, abs_of_nonneg h0]
    exact h1
  · have h := (tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop).const_mul (quadMoment β a / b ^ 2)
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp [Function.comp, one_div]

end Laplace.Grammar
