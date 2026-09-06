/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDGeneralSwap

/-!
# Next-order term in the general equal-exponent case (grammar §4.2)

Unit 41 identified the constant below `log n` for `k = (1,1)`, `h = (0,0)`. Here the same is done
for the general equal-exponent case `p₁ = p₂ = p` of unit 45. The weighted logarithmic primitive
satisfies

  `∫₀^L F_γ/x = A_γ log L + C₀(γ) + θ(L)`,  `0 ≤ θ(L) ≤ A_{γ+1}/L`  (`L ≥ 1`),

with `C₀(γ) = ∫₀¹ F_γ/x − ∫₁^∞ (A_γ − F_γ)/x` (`weightedLogConst`), so that

  `Z(n) = n^{-p/2}/(k₁k₂) · (A_{p−1} (log n / 2 + (k₁+k₂) log b) + C₀(p−1)) + O(n^{-(p+1)/2})`,

and `n^{p/2} Z(n) − (A_{p−1}/(2k₁k₂)) log n → (A_{p−1}(k₁+k₂) log b + C₀(p−1))/(k₁k₂)`.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

theorem weighted_tail_div_bounds (β a γ x : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hx : 0 < x) :
    0 ≤ (weightedMass β a γ - weightedPrimitive β a γ x) / x
      ∧ (weightedMass β a γ - weightedPrimitive β a γ x) / x
        ≤ weightedMass β a (γ + 1) * x ^ (-2 : ℝ) := by
  refine ⟨div_nonneg (weightedMass_sub_primitive_nonneg β a γ x hβ hγ hx.le) hx.le, ?_⟩
  rw [Real.rpow_neg hx.le, Real.rpow_two, div_le_iff₀ hx]
  calc weightedMass β a γ - weightedPrimitive β a γ x ≤ weightedMass β a (γ + 1) / x :=
        weightedMass_sub_primitive_le β a γ x hβ hγ hx
    _ = weightedMass β a (γ + 1) * (x ^ 2)⁻¹ * x := by field_simp

theorem weighted_tail_div_integrableOn (β a γ c : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hc : 0 < c) :
    IntegrableOn (fun x => (weightedMass β a γ - weightedPrimitive β a γ x) / x) (Ioi c) := by
  refine Integrable.mono' (g := fun x => weightedMass β a (γ + 1) * x ^ (-2 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hc).const_mul _)
    ((measurable_const.sub (weightedPrimitive_measurable β a γ hβ hγ)).div
      measurable_id).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun x hx => ?_
  obtain ⟨h0, h1⟩ := weighted_tail_div_bounds β a γ x hβ hγ (hc.trans hx)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

theorem weighted_tail_integral_bounds (β a γ L : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hL : 0 < L) :
    0 ≤ (∫ x in Ioi L, (weightedMass β a γ - weightedPrimitive β a γ x) / x)
      ∧ (∫ x in Ioi L, (weightedMass β a γ - weightedPrimitive β a γ x) / x)
        ≤ weightedMass β a (γ + 1) / L := by
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun x hx =>
    (weighted_tail_div_bounds β a γ x hβ hγ (hL.trans hx)).1, ?_⟩
  have hint : (∫ x in Ioi L, weightedMass β a (γ + 1) * x ^ (-2 : ℝ))
      = weightedMass β a (γ + 1) / L := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hL]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg hL.le, Real.rpow_one]
    field_simp
  rw [← hint]
  exact setIntegral_mono_on (weighted_tail_div_integrableOn β a γ L hβ hγ hL)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hL).const_mul _) measurableSet_Ioi
    fun x hx => (weighted_tail_div_bounds β a γ x hβ hγ (hL.trans hx)).2

/-- The constant term of the weighted logarithmic primitive. -/
noncomputable def weightedLogConst (β a γ : ℝ) : ℝ :=
  (∫ x in Ioc (0 : ℝ) 1, weightedPrimitive β a γ x / x)
    - ∫ x in Ioi (1 : ℝ), (weightedMass β a γ - weightedPrimitive β a γ x) / x

/-- **Exact constant-term identity**: for `L ≥ 1`,
`∫₀^L F_γ/x − A_γ log L − C₀(γ) = ∫_L^∞ (A_γ − F_γ)/x`. -/
theorem weightedLogPrimitive_sub_log_sub_const (β a γ L : ℝ) (hβ : 0 < β) (hγ : -1 < γ)
    (hL : 1 ≤ L) :
    weightedLogPrimitive β a γ L - weightedMass β a γ * Real.log L - weightedLogConst β a γ
      = ∫ x in Ioi L, (weightedMass β a γ - weightedPrimitive β a γ x) / x := by
  have hint := weighted_tail_div_integrableOn β a γ 1 hβ hγ one_pos
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl L)) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hL))
    (f := fun x => (weightedMass β a γ - weightedPrimitive β a γ x) / x)
  rw [Ioc_union_Ioi_eq_Ioi hL] at hsplit
  rw [weightedLogPrimitive_split β a γ L hβ hγ hL, weightedLogConst, hsplit]
  ring

theorem weightedLogPrimitive_sub_log_sub_const_bounds (β a γ L : ℝ) (hβ : 0 < β) (hγ : -1 < γ)
    (hL : 1 ≤ L) :
    0 ≤ weightedLogPrimitive β a γ L - weightedMass β a γ * Real.log L - weightedLogConst β a γ
      ∧ weightedLogPrimitive β a γ L - weightedMass β a γ * Real.log L - weightedLogConst β a γ
        ≤ weightedMass β a (γ + 1) / L := by
  rw [weightedLogPrimitive_sub_log_sub_const β a γ L hβ hγ hL]
  exact weighted_tail_integral_bounds β a γ L hβ hγ (one_pos.trans_le hL)

/-- The two-term coefficient in the general equal case. -/
noncomputable def twoDGeneralSecondOrderCoeff (β a b p : ℝ) (k₁ k₂ : ℕ) (n : ℝ) : ℝ :=
  1 / ((k₁ : ℝ) * k₂) * (weightedMass β a (p - 1) * (Real.log n / 2 + ((k₁ : ℝ) + k₂) * Real.log b)
    + weightedLogConst β a (p - 1))

/-- Explicit remainder for `n ≥ max 1 b^{-2(k₁+k₂)}`:
`0 ≤ n^{p/2} Z(n) − coeff(n) ≤ A_p/(k₁k₂ b^{k₁+k₂}) · n^{-1/2}`. -/
theorem twoDGeneral_second_order_bounds (β a b n p : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : p = ((h₁ : ℝ) + 1) / k₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (hn : 1 ≤ n) (hnb : 1 / b ^ (2 * (k₁ + k₂)) ≤ n) :
    0 ≤ n ^ (p / 2) * twoDGeneral β a b n h₁ h₂ k₁ k₂ - twoDGeneralSecondOrderCoeff β a b p k₁ k₂ n
      ∧ n ^ (p / 2) * twoDGeneral β a b n h₁ h₂ k₁ k₂ - twoDGeneralSecondOrderCoeff β a b p k₁ k₂ n
        ≤ 1 / ((k₁ : ℝ) * k₂) * weightedMass β a p / b ^ (k₁ + k₂) * (1 / Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hp0 : 0 < p := by rw [hp₁]; positivity
  have hγ : -1 < p - 1 := by linarith
  have hL : 1 ≤ Real.sqrt n * b ^ (k₁ + k₂) := by
    have h1 : (1 / b ^ (k₁ + k₂)) ^ 2 ≤ n := by
      rw [div_pow, one_pow, ← pow_mul, mul_comm]; exact hnb
    have h2 : 1 / b ^ (k₁ + k₂) ≤ Real.sqrt n := by
      rw [Real.le_sqrt (by positivity) hn0.le]; exact h1
    calc (1 : ℝ) = 1 / b ^ (k₁ + k₂) * b ^ (k₁ + k₂) := by field_simp
      _ ≤ Real.sqrt n * b ^ (k₁ + k₂) := by gcongr
  have hlogL : Real.log (Real.sqrt n * b ^ (k₁ + k₂))
      = Real.log n / 2 + ((k₁ : ℝ) + k₂) * Real.log b := by
    rw [Real.log_mul hsn.ne' (by positivity), Real.log_sqrt hn0.le, Real.log_pow]
    push_cast; ring
  obtain ⟨h0, h1⟩ := weightedLogPrimitive_sub_log_sub_const_bounds β a (p - 1) _ hβ hγ hL
  rw [hlogL] at h0 h1
  rw [show p - 1 + 1 = p by ring] at h1
  have hpow : n ^ (p / 2) * n ^ (-(p / 2)) = 1 := by
    rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero]
  have heq : n ^ (p / 2) * twoDGeneral β a b n h₁ h₂ k₁ k₂
      - twoDGeneralSecondOrderCoeff β a b p k₁ k₂ n
      = 1 / ((k₁ : ℝ) * k₂) * (weightedLogPrimitive β a (p - 1) (Real.sqrt n * b ^ (k₁ + k₂))
        - weightedMass β a (p - 1) * (Real.log n / 2 + ((k₁ : ℝ) + k₂) * Real.log b)
        - weightedLogConst β a (p - 1)) := by
    rw [twoDGeneral_eq_of_eq β a b n p h₁ h₂ k₁ k₂ hn0 hb hk₁ hk₂ hp₁ hp₂,
      twoDGeneralSecondOrderCoeff,
      show n ^ (p / 2) * (1 / ((k₁ : ℝ) * k₂) * n ^ (-(p / 2))
          * weightedLogPrimitive β a (p - 1) (Real.sqrt n * b ^ (k₁ + k₂)))
        = 1 / ((k₁ : ℝ) * k₂) * (n ^ (p / 2) * n ^ (-(p / 2)))
          * weightedLogPrimitive β a (p - 1) (Real.sqrt n * b ^ (k₁ + k₂)) by ring,
      hpow]
    ring
  rw [heq]
  have hK : 0 < 1 / ((k₁ : ℝ) * k₂) := by positivity
  refine ⟨mul_nonneg hK.le h0, ?_⟩
  calc 1 / ((k₁ : ℝ) * k₂) * (weightedLogPrimitive β a (p - 1) (Real.sqrt n * b ^ (k₁ + k₂))
        - weightedMass β a (p - 1) * (Real.log n / 2 + ((k₁ : ℝ) + k₂) * Real.log b)
        - weightedLogConst β a (p - 1))
      ≤ 1 / ((k₁ : ℝ) * k₂) * (weightedMass β a p / (Real.sqrt n * b ^ (k₁ + k₂))) := by gcongr
    _ = 1 / ((k₁ : ℝ) * k₂) * weightedMass β a p / b ^ (k₁ + k₂) * (1 / Real.sqrt n) := by
        field_simp

/-- **Two-term expansion, general equal case**:
`Z(n) = n^{-p/2} · coeff(n) + O(n^{-(p+1)/2})`. -/
theorem twoDGeneral_second_order_isBigO (β a b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp : ((h₁ : ℝ) + 1) / k₁ = ((h₂ : ℝ) + 1) / k₂) :
    (fun n : ℝ => twoDGeneral β a b n h₁ h₂ k₁ k₂
        - n ^ (-(((h₁ : ℝ) + 1) / k₁ / 2))
          * twoDGeneralSecondOrderCoeff β a b (((h₁ : ℝ) + 1) / k₁) k₁ k₂ n)
      =O[atTop] fun n : ℝ => n ^ (-(((h₁ : ℝ) + 1) / k₁ / 2) - 1 / 2) := by
  obtain ⟨p, hp₁⟩ : ∃ p : ℝ, p = ((h₁ : ℝ) + 1) / k₁ := ⟨_, rfl⟩
  have hp₂ : ((h₂ : ℝ) + 1) / k₂ = p := by rw [hp₁, hp]
  rw [← hp₁]
  apply IsBigO.of_bound (1 / ((k₁ : ℝ) * k₂) * weightedMass β a p / b ^ (k₁ + k₂))
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ (2 * (k₁ + k₂)))]
    with n hn hnb
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  obtain ⟨h0, h1⟩ := twoDGeneral_second_order_bounds β a b n p h₁ h₂ k₁ k₂ hβ hb hk₁ hk₂ hp₁ hp₂
    hn hnb
  have hpow : n ^ (-(p / 2)) * n ^ (p / 2) = 1 := by
    rw [← Real.rpow_add hn0, neg_add_cancel, Real.rpow_zero]
  have heq : twoDGeneral β a b n h₁ h₂ k₁ k₂
      - n ^ (-(p / 2)) * twoDGeneralSecondOrderCoeff β a b p k₁ k₂ n
      = n ^ (-(p / 2)) * (n ^ (p / 2) * twoDGeneral β a b n h₁ h₂ k₁ k₂
        - twoDGeneralSecondOrderCoeff β a b p k₁ k₂ n) := by
    rw [mul_sub, ← mul_assoc, hpow, one_mul]
  have hsplit : n ^ (-(p / 2) - 1 / 2) = n ^ (-(p / 2)) * (1 / Real.sqrt n) := by
    rw [Real.rpow_sub hn0, Real.sqrt_eq_rpow, div_eq_mul_inv, ← one_div]
  rw [heq, hsplit, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hn0 _), abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt n),
    abs_of_nonneg h0]
  calc n ^ (-(p / 2)) * (n ^ (p / 2) * twoDGeneral β a b n h₁ h₂ k₁ k₂
        - twoDGeneralSecondOrderCoeff β a b p k₁ k₂ n)
      ≤ n ^ (-(p / 2)) * (1 / ((k₁ : ℝ) * k₂) * weightedMass β a p / b ^ (k₁ + k₂)
          * (1 / Real.sqrt n)) := by gcongr
    _ = 1 / ((k₁ : ℝ) * k₂) * weightedMass β a p / b ^ (k₁ + k₂)
          * (n ^ (-(p / 2)) * (1 / Real.sqrt n)) := by ring

/-- **The constant below the logarithm, general equal case**:
`n^{p/2} Z(n) − (A_{p−1}/(2k₁k₂)) log n → (A_{p−1}(k₁+k₂) log b + C₀(p−1))/(k₁k₂)`. -/
theorem twoDGeneral_second_order_tendsto (β a b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp : ((h₁ : ℝ) + 1) / k₁ = ((h₂ : ℝ) + 1) / k₂) :
    Tendsto (fun n : ℝ => n ^ (((h₁ : ℝ) + 1) / k₁ / 2) * twoDGeneral β a b n h₁ h₂ k₁ k₂
        - weightedMass β a (((h₁ : ℝ) + 1) / k₁ - 1) / (2 * ((k₁ : ℝ) * k₂)) * Real.log n)
      atTop (𝓝 (1 / ((k₁ : ℝ) * k₂) * (weightedMass β a (((h₁ : ℝ) + 1) / k₁ - 1)
        * (((k₁ : ℝ) + k₂) * Real.log b) + weightedLogConst β a (((h₁ : ℝ) + 1) / k₁ - 1)))) := by
  obtain ⟨p, hp₁⟩ : ∃ p : ℝ, p = ((h₁ : ℝ) + 1) / k₁ := ⟨_, rfl⟩
  have hp₂ : ((h₂ : ℝ) + 1) / k₂ = p := by rw [hp₁, hp]
  rw [← hp₁]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun n => 1 / ((k₁ : ℝ) * k₂) * weightedMass β a p / b ^ (k₁ + k₂)
      * (1 / Real.sqrt n))
    (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ (2 * (k₁ + k₂)))]
      with n hn hnb
    obtain ⟨h0, h1⟩ := twoDGeneral_second_order_bounds β a b n p h₁ h₂ k₁ k₂ hβ hb hk₁ hk₂ hp₁ hp₂
      hn hnb
    rw [twoDGeneralSecondOrderCoeff] at h0 h1
    rw [Real.norm_eq_abs, show n ^ (p / 2) * twoDGeneral β a b n h₁ h₂ k₁ k₂
        - weightedMass β a (p - 1) / (2 * ((k₁ : ℝ) * k₂)) * Real.log n
        - 1 / ((k₁ : ℝ) * k₂) * (weightedMass β a (p - 1) * (((k₁ : ℝ) + k₂) * Real.log b)
          + weightedLogConst β a (p - 1))
      = n ^ (p / 2) * twoDGeneral β a b n h₁ h₂ k₁ k₂
        - 1 / ((k₁ : ℝ) * k₂) * (weightedMass β a (p - 1)
          * (Real.log n / 2 + ((k₁ : ℝ) + k₂) * Real.log b) + weightedLogConst β a (p - 1))
        by ring, abs_of_nonneg h0]
    exact h1
  · have h := (tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop).const_mul
      (1 / ((k₁ : ℝ) * k₂) * weightedMass β a p / b ^ (k₁ + k₂))
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp [Function.comp, one_div]

end Laplace.Grammar
