/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AllOrders

/-!
# The one-dimensional Taylor tree as an asymptotic expansion (grammar §4.2)

The `O`-form of `standardIntegral1D_taylor_tree`: for `ξ(u) = ξ₀ + c u^m` and every `N`,

  `Z_chart(n) = ∑_{p<N} (βc)^p/p! · (2k)^{-1} S_{μ_p + p/2}(ξ₀) · n^{-μ_p} + O(n^{-μ_N})`,
  `μ_p = (h+mp+1)/(2k)`,

as `n → ∞`. This is precisely the statement of `cor:standardintegralexp` in one dimension for a
monomial perturbation, with `Λ^* = (h+1)/(2k) + (m/(2k))ℕ` and every `P_μ` a constant (no `log n`
since `d = 1`) given by a fluctuation function. The `N` exponentially small boundary tails, each
`O(n^{p/2} e^{-εn})`, are absorbed into the `O(n^{-μ_N})`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

/-- **The 1D Taylor tree as an asymptotic expansion**: for `ξ = ξ₀ + c u^m` and any order `N`,
`Z_chart(n) - ∑_{p<N} (βc)^p/p! (2k)^{-1} n^{-μ_p} S_{μ_p+p/2}(ξ₀) = O(n^{-μ_N})`,
`μ_p = (h+mp+1)/(2k)` (grammar §4.2 `cor:standardintegralexp`, `d = 1`). -/
theorem standardIntegral1D_taylor_tree_isBigO (β ξ₀ c b : ℝ) (h k m N : ℕ)
    (hβ : 0 < β) (hb : 0 < b) (hk : 0 < k) :
    (fun n : ℝ => (∫ u in Ioc 0 b,
        u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m)))
      - ∑ p ∈ Finset.range N, (β * c) ^ p / p.factorial
          * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m * p : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + m * p : ℕ) : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) ξ₀))
      =O[atTop] fun n : ℝ => n ^ (-((((h + m * N : ℕ) : ℝ) + 1) / (2 * k))) := by
  set μN : ℝ := (((h + m * N : ℕ) : ℝ) + 1) / (2 * k) with hμN
  set ε : ℝ := β / 4 * b ^ (2 * k) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨CN, hCN⟩ : ∃ C : ℝ, C = (β * |c|) ^ N / N.factorial
    * ((1 / (2 * (k : ℝ))) * fluctuation β (μN + (N : ℝ) / 2) (ξ₀ + |c| * b ^ m)) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℝ, K = fun p => Real.exp (β * ξ₀ ^ 2 / 2)
    * ((β / 4) ^ (-((((h + m * p + k * p : ℕ) : ℝ) + 1) / (2 * k))) * (1 / (2 * (k : ℝ)))
      * Real.Gamma ((((h + m * p + k * p : ℕ) : ℝ) + 1) / (2 * k))) := ⟨_, rfl⟩
  have hK0 : ∀ p, 0 ≤ K p := by
    intro p
    simp only [hK]
    have := Real.Gamma_pos_of_pos
      (by positivity : (0 : ℝ) < (((h + m * p + k * p : ℕ) : ℝ) + 1) / (2 * k))
    positivity
  -- each tail scale `n^{p/2} e^{-εn}` is `o(n^{-μ_N})`
  have hl : ∀ p : ℕ, (fun n : ℝ => n ^ ((p : ℝ) / 2) * Real.exp (-ε * n))
      =o[atTop] fun n : ℝ => n ^ (-μN) := by
    intro p
    have h0 := (isBigO_refl (fun n : ℝ => n ^ ((p : ℝ) / 2)) atTop).mul_isLittleO
      (isLittleO_exp_neg_mul_rpow_atTop hε0 (-μN - (p : ℝ) / 2))
    refine h0.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    rw [← Real.rpow_add hn]; congr 1; ring
  have hall : ∀ᶠ n : ℝ in atTop, ∀ p ∈ Finset.range N,
      ‖n ^ ((p : ℝ) / 2) * Real.exp (-ε * n)‖ ≤ 1 * ‖n ^ (-μN)‖ :=
    (Filter.eventually_all_finset _).2 fun p _ => (hl p).bound one_pos
  apply IsBigO.of_bound (CN + ∑ p ∈ Finset.range N, (β * |c|) ^ p / p.factorial * K p)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hall] with n hn hb'
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow_pos : 0 < n ^ (-μN) := Real.rpow_pos_of_pos hn0 _
  simp only [Real.norm_eq_abs] at hb' ⊢
  rw [abs_of_pos hpow_pos]
  have hmain := standardIntegral1D_taylor_tree β n ξ₀ c b h k m N hβ hn hb hk
  rw [← hμN] at hmain
  -- each boundary tail is at most `K p · n^{-μ_N}`
  have htail : ∀ p ∈ Finset.range N,
      (∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
        * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        ≤ K p * n ^ (-μN) := by
    intro p hp
    have hb'p := hb' p hp
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hn0.le _) (Real.exp_pos _).le),
      abs_of_pos hpow_pos, one_mul] at hb'p
    have hH : (fun u : ℝ => u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        = fun u => Real.sqrt n ^ p * (u ^ (h + m * p + k * p)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) := by
      funext u; rw [mul_pow, ← pow_mul, pow_add u (h + m * p)]; ring
    have ht := standardIntegral1D_tail_le β n ξ₀ b (h + m * p + k * p) k hβ hn hb hk
    rw [show -(β / 4) * n * b ^ (2 * k) = -ε * n by rw [hε]; ring] at ht
    have hsq : Real.sqrt n ^ p = n ^ ((p : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; ring
    rw [hH, integral_const_mul, hsq]
    calc n ^ ((p : ℝ) / 2) * ∫ u in Ioi b, u ^ (h + m * p + k * p)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)
        ≤ n ^ ((p : ℝ) / 2) * (K p * Real.exp (-ε * n)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
          calc _ ≤ _ := ht
            _ = K p * Real.exp (-ε * n) := by simp only [hK]; ring
      _ = K p * (n ^ ((p : ℝ) / 2) * Real.exp (-ε * n)) := by ring
      _ ≤ K p * n ^ (-μN) := mul_le_mul_of_nonneg_left hb'p (hK0 p)
  calc _ ≤ _ := hmain
    _ = CN * n ^ (-μN) + ∑ p ∈ Finset.range N, (β * |c|) ^ p / p.factorial
          * ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
        rw [hCN]; ring
    _ ≤ CN * n ^ (-μN) + ∑ p ∈ Finset.range N, (β * |c|) ^ p / p.factorial * (K p * n ^ (-μN)) := by
        gcongr with p hp
        exact htail p hp
    _ = (CN + ∑ p ∈ Finset.range N, (β * |c|) ^ p / p.factorial * K p) * n ^ (-μN) := by
        rw [add_mul, Finset.sum_mul]; congr 1; exact Finset.sum_congr rfl fun p _ => by ring

end Laplace.Grammar
