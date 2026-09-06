/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.WeightedMass

/-!
# The general `(k, h)` two-dimensional integral: equal exponents give one logarithm (grammar §4.2)

For `p₁ = p₂ = p` (both candidate exponents equal to `p/2`, multiplicity two) the exact reduction
of unit 44 reads `Z(n) = 1/(k₁k₂) · n^{-p/2} · ∫₀^{√n b^{k₁+k₂}} F_{p−1}(x)/x dx`, and the weighted
logarithmic squeeze of `WeightedMass.lean` gives

  `Z(n) ~ (A_{p−1} / (2 k₁ k₂)) · n^{-p/2} · log n`,  `A_{p−1} = S_{p/2}(a)/2`.

For `k = (1,1)`, `h = (0,0)` this is unit 35's `(S_{1/2}(a)/4) n^{-1/2} log n`.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- `n^r = o(n^r log n)` as `n → ∞`. -/
theorem isLittleO_rpow_rpow_mul_log (r : ℝ) :
    (fun n : ℝ => n ^ r) =o[atTop] fun n : ℝ => n ^ r * Real.log n := by
  have h1 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] Real.log :=
    isLittleO_const_left.2 (Or.inr (by
      simpa [Function.comp_def, Real.norm_eq_abs] using
        tendsto_abs_atTop_atTop.comp Real.tendsto_log_atTop))
  have h2 := h1.mul_isBigO (isBigO_refl (fun n : ℝ => n ^ r) atTop)
  refine (h2.congr_left fun n => ?_).congr_right fun n => ?_
  · simp
  · ring

/-- The exact reduction in the equal-exponent case. -/
theorem twoDGeneral_eq_of_eq (β a b n p : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hn : 0 < n) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : p = ((h₁ : ℝ) + 1) / k₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) :
    twoDGeneral β a b n h₁ h₂ k₁ k₂
      = 1 / ((k₁ : ℝ) * k₂) * n ^ (-(p / 2))
        * weightedLogPrimitive β a (p - 1) (Real.sqrt n * b ^ (k₁ + k₂)) := by
  rw [twoDGeneral_eq β a b n h₁ h₂ k₁ k₂ hn hb hk₁ hk₂, ← hp₁, hp₂, sub_self, mul_zero,
    Real.rpow_zero, mul_one, zero_sub, weightedLogPrimitive]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [Real.rpow_neg hx.1.le, Real.rpow_one, inv_mul_eq_div]

/-- **Equal exponents ⇒ one logarithm, general `(k, h)`**:
`Z(n) ~ (A_{p−1}/(2k₁k₂)) n^{-p/2} log n` where `p = (h₁+1)/k₁ = (h₂+1)/k₂`. -/
theorem twoDGeneral_isEquivalent_of_eq (β a b : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp : ((h₁ : ℝ) + 1) / k₁ = ((h₂ : ℝ) + 1) / k₂) :
    (fun n : ℝ => twoDGeneral β a b n h₁ h₂ k₁ k₂) ~[atTop]
      fun n : ℝ => weightedMass β a (((h₁ : ℝ) + 1) / k₁ - 1) / (2 * ((k₁ : ℝ) * k₂))
        * (n ^ (-(((h₁ : ℝ) + 1) / k₁ / 2)) * Real.log n) := by
  obtain ⟨p, hp₁⟩ : ∃ p : ℝ, p = ((h₁ : ℝ) + 1) / k₁ := ⟨_, rfl⟩
  have hp₂ : ((h₂ : ℝ) + 1) / k₂ = p := by rw [hp₁, hp]
  rw [← hp₁]
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have hp0 : 0 < p := by rw [hp₁]; positivity
  have hγ : -1 < p - 1 := by linarith
  have hA0 : 0 < weightedMass β a (p - 1) := weightedMass_pos β a (p - 1) hβ hγ
  have hA1 : 0 ≤ weightedMass β a p := (weightedMass_pos β a p hβ (by linarith)).le
  have hE0 : 0 < Real.exp (β * a ^ 2 / 2) := Real.exp_pos _
  apply IsLittleO.isEquivalent
  have hbig : (fun n : ℝ => twoDGeneral β a b n h₁ h₂ k₁ k₂
        - weightedMass β a (p - 1) / (2 * ((k₁ : ℝ) * k₂)) * (n ^ (-(p / 2)) * Real.log n))
      =O[atTop] fun n : ℝ => n ^ (-(p / 2)) := by
    apply IsBigO.of_bound (1 / ((k₁ : ℝ) * k₂) * (weightedMass β a p
      + Real.exp (β * a ^ 2 / 2) / p ^ 2
      + weightedMass β a (p - 1) * ((k₁ : ℝ) + k₂) * |Real.log b|))
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ (2 * (k₁ + k₂)))]
      with n hn hnb
    have hn0 : (0 : ℝ) < n := by linarith
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
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
    obtain ⟨hlo, hhi⟩ := weightedLogPrimitive_bounds β a (p - 1) _ hβ hγ hL
    rw [hlogL, show p - 1 + 1 = p by ring] at hlo hhi
    rw [twoDGeneral_eq_of_eq β a b n p h₁ h₂ k₁ k₂ hn0 hb hk₁ hk₂ hp₁ hp₂, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    set W := weightedLogPrimitive β a (p - 1) (Real.sqrt n * b ^ (k₁ + k₂)) with hW
    set A := weightedMass β a (p - 1) with hA
    set A1 := weightedMass β a p with hA1def
    set E := Real.exp (β * a ^ 2 / 2) with hE
    set κ : ℝ := (k₁ : ℝ) + k₂ with hκ
    have hκ0 : 0 ≤ κ := by positivity
    have hlb := le_abs_self (Real.log b)
    have hlb' := neg_abs_le (Real.log b)
    have hdiff : |W - A * (Real.log n / 2)| ≤ A1 + E / p ^ 2 + A * κ * |Real.log b| := by
      have hAκ : 0 ≤ A * κ := mul_nonneg hA0.le hκ0
      have e1 := mul_le_mul_of_nonneg_left hlb hAκ
      have e2 := mul_le_mul_of_nonneg_left hlb' hAκ
      have hEp : 0 ≤ E / p ^ 2 := div_nonneg hE0.le (sq_nonneg p)
      rw [abs_le]
      constructor <;> linarith
    have hpow0 : 0 < n ^ (-(p / 2)) := Real.rpow_pos_of_pos hn0 _
    calc |1 / ((k₁ : ℝ) * k₂) * n ^ (-(p / 2)) * W
          - A / (2 * ((k₁ : ℝ) * k₂)) * (n ^ (-(p / 2)) * Real.log n)|
        = 1 / ((k₁ : ℝ) * k₂) * n ^ (-(p / 2)) * |W - A * (Real.log n / 2)| := by
          rw [show 1 / ((k₁ : ℝ) * k₂) * n ^ (-(p / 2)) * W
              - A / (2 * ((k₁ : ℝ) * k₂)) * (n ^ (-(p / 2)) * Real.log n)
              = 1 / ((k₁ : ℝ) * k₂) * n ^ (-(p / 2)) * (W - A * (Real.log n / 2)) by ring,
            abs_mul, abs_of_pos (by positivity)]
      _ ≤ 1 / ((k₁ : ℝ) * k₂) * n ^ (-(p / 2)) * (A1 + E / p ^ 2 + A * κ * |Real.log b|) := by
          gcongr
      _ = 1 / ((k₁ : ℝ) * k₂) * (A1 + E / p ^ 2 + A * κ * |Real.log b|) * n ^ (-(p / 2)) := by
          ring
  exact (hbig.trans_isLittleO (isLittleO_rpow_rpow_mul_log (-(p / 2)))).const_mul_right
    (by positivity)

end Laplace.Grammar
