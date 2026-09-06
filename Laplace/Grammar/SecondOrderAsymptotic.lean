/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.SecondOrder

/-!
# Two-term asymptotic expansion of the chart standard integral (grammar §4.2)

The `O`-form of `standardIntegral1D_second_order`: for `ξ(u) = ξ₀ + c u^m`,

  `Z_chart(n) = (2k)^{-1} S_{μ₁}(ξ₀) n^{-μ₁} + βc (2k)^{-1} S_{μ₂+1/2}(ξ₀) n^{-μ₂} + O(n^{-μ₃})`

as `n → ∞`, with `μ₁ = (h+1)/(2k)`, `μ₂ = (h+m+1)/(2k)`, `μ₃ = (h+2m+1)/(2k)` — three consecutive
points of the candidate exponent set `Λ(h,k)` (`eq:candidateexponents`), the first two carrying
fluctuation-function coefficients. The exponentially small boundary tails (including the
`√n e^{-εn}` one from the first-order insertion) are absorbed into the `O(n^{-μ₃})`. This is the
two-term instance of `cor:standardintegralexp` in one dimension. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

/-- **Two-term asymptotic expansion** of the chart standard integral for `ξ = ξ₀ + c u^m`:
`Z_chart(n) - (2k)^{-1} n^{-μ₁} S_{μ₁}(ξ₀) - βc (2k)^{-1} n^{-μ₂} S_{μ₂+1/2}(ξ₀) = O(n^{-μ₃})`,
`μ₁ = (h+1)/(2k)`, `μ₂ = (h+m+1)/(2k)`, `μ₃ = (h+2m+1)/(2k)`. -/
theorem standardIntegral1D_second_order_isBigO (β ξ₀ c b : ℝ) (h k m : ℕ)
    (hβ : 0 < β) (hb : 0 < b) (hk : 0 < k) :
    (fun n : ℝ => (∫ u in Ioc 0 b,
        u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m)))
      - (1 / (2 * (k : ℝ))) * n ^ (-(((h : ℝ) + 1) / (2 * k)))
          * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀
      - β * c * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + m : ℕ) : ℝ) + 1) / (2 * k) + (1 : ℝ) / 2) ξ₀))
      =O[atTop] fun n : ℝ => n ^ (-((((h + 2 * m : ℕ) : ℝ) + 1) / (2 * k))) := by
  set μ₃ : ℝ := (((h + 2 * m : ℕ) : ℝ) + 1) / (2 * k) with hμ₃
  set ε : ℝ := β / 4 * b ^ (2 * k) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨C₂, hC₂⟩ : ∃ C : ℝ, C = (β * c) ^ 2 / 2 * ((1 / (2 * (k : ℝ)))
    * fluctuation β ((((h + 2 * m + 2 * k : ℕ) : ℝ) + 1) / (2 * k)) (ξ₀ + |c| * b ^ m)) := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K : ℝ, K = Real.exp (β * ξ₀ ^ 2 / 2)
    * ((β / 4) ^ (-(((h : ℝ) + 1) / (2 * k))) * (1 / (2 * (k : ℝ)))
      * Real.Gamma (((h : ℝ) + 1) / (2 * k))) := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K : ℝ, K = Real.exp (β * ξ₀ ^ 2 / 2)
    * ((β / 4) ^ (-((((h + m + k : ℕ) : ℝ) + 1) / (2 * k))) * (1 / (2 * (k : ℝ)))
      * Real.Gamma ((((h + m + k : ℕ) : ℝ) + 1) / (2 * k))) := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]
    have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < ((h : ℝ) + 1) / (2 * k))
    positivity
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]
    have := Real.Gamma_pos_of_pos
      (by positivity : (0 : ℝ) < (((h + m + k : ℕ) : ℝ) + 1) / (2 * k))
    positivity
  -- the two exponentially small scales are `o(n^{-μ₃})`
  have hl₁ : (fun n : ℝ => Real.exp (-ε * n)) =o[atTop] fun n : ℝ => n ^ (-μ₃) :=
    isLittleO_exp_neg_mul_rpow_atTop hε0 (-μ₃)
  have hl₂ : (fun n : ℝ => Real.sqrt n * Real.exp (-ε * n)) =o[atTop] fun n : ℝ => n ^ (-μ₃) := by
    have h0 := (isBigO_refl (fun n : ℝ => Real.sqrt n) atTop).mul_isLittleO
      (isLittleO_exp_neg_mul_rpow_atTop hε0 (-μ₃ - 1 / 2))
    refine h0.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]; congr 1; ring
  apply IsBigO.of_bound (C₂ + K₀ + |β * c| * K₁)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hl₁.bound one_pos, hl₂.bound one_pos]
    with n hn hb₁ hb₂
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow_pos : 0 < n ^ (-μ₃) := Real.rpow_pos_of_pos hn0 _
  simp only [Real.norm_eq_abs] at hb₁ hb₂ ⊢
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos hpow_pos, one_mul] at hb₁
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg n) (Real.exp_pos _).le), abs_of_pos hpow_pos,
    one_mul] at hb₂
  rw [abs_of_pos hpow_pos]
  have hmain := standardIntegral1D_second_order β n ξ₀ c b h k m hβ hn hb hk
  rw [← hμ₃] at hmain
  have ht₀ := standardIntegral1D_tail_le β n ξ₀ b h k hβ hn hb hk
  have ht₁' := standardIntegral1D_tail_le β n ξ₀ b (h + m + k) k hβ hn hb hk
  have ht₁ : (∫ u in Ioi b, u ^ (h + m) * (Real.sqrt n * u ^ k)
      * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
      = Real.sqrt n * ∫ u in Ioi b, u ^ (h + m + k)
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
    rw [← integral_const_mul]
    congr 1; funext u; rw [pow_add u (h + m)]; ring
  rw [ht₁] at hmain
  rw [show -(β / 4) * n * b ^ (2 * k) = -ε * n by rw [hε]; ring] at ht₀ ht₁'
  set T₀ := ∫ u in Ioi b, u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
  set T₁ := ∫ u in Ioi b, u ^ (h + m + k)
    * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
  have e₀ : T₀ ≤ K₀ * n ^ (-μ₃) := by
    calc T₀ ≤ _ := ht₀
      _ = K₀ * Real.exp (-ε * n) := by rw [hK₀]; ring
      _ ≤ K₀ * n ^ (-μ₃) := mul_le_mul_of_nonneg_left hb₁ hK₀0
  have e₁ : Real.sqrt n * T₁ ≤ K₁ * n ^ (-μ₃) := by
    calc Real.sqrt n * T₁ ≤ Real.sqrt n * (K₁ * Real.exp (-ε * n)) :=
          mul_le_mul_of_nonneg_left (ht₁'.trans_eq (by rw [hK₁]; ring)) (Real.sqrt_nonneg n)
      _ = K₁ * (Real.sqrt n * Real.exp (-ε * n)) := by ring
      _ ≤ K₁ * n ^ (-μ₃) := mul_le_mul_of_nonneg_left hb₂ hK₁0
  calc _ ≤ _ := hmain
    _ = C₂ * n ^ (-μ₃) + T₀ + |β * c| * (Real.sqrt n * T₁) := by rw [hC₂]; ring
    _ ≤ C₂ * n ^ (-μ₃) + K₀ * n ^ (-μ₃) + |β * c| * (K₁ * n ^ (-μ₃)) := by gcongr
    _ = (C₂ + K₀ + |β * c| * K₁) * n ^ (-μ₃) := by ring

end Laplace.Grammar
