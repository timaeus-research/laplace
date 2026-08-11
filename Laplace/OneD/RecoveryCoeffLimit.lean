/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.RecoveryAllOrder

/-!
# Each expansion coefficient is a limit of the data

The `Tendsto` packaging of the all-order expansion: the remainder of the
order-`n` truncation, rescaled by `t^((n+1)+1/2)`, converges to the
`(n+1)`-st coefficient (`quartic_expansion_coefficient_limit`). This is
the germbij note's statement that the asymptotic expansion determines
every coefficient, in the form a consumer of the expansion data would
use: each coefficient is recovered as a limit of the partition-function
values, inductively down the ladder.
-/

open Real MeasureTheory Filter
open scoped Nat

namespace Laplace.OneD

/-- **Each coefficient is the limit of the rescaled remainder.** The
order-`n` truncation error of the quartic-perturbed partition function,
rescaled by `t^((n+1)+1/2)`, converges to the `(n+1)`-st expansion
coefficient. -/
theorem quartic_expansion_coefficient_limit {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    Tendsto (fun t : ℝ ↦
      (partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t
        - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 1),
            (-b) ^ j * ((4 * j - 1)‼ : ℝ) / (Nat.factorial j : ℝ) *
              t ^ (-((j : ℝ) + 1 / 2)))
        * t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2))
      atTop
      (nhds (Real.sqrt (2 * π) * ((-b) ^ (n + 1) *
        ((4 * (n + 1) - 1)‼ : ℝ) / (Nat.factorial (n + 1) : ℝ)))) := by
  -- Abbreviations.
  set Z : ℝ → ℝ := fun t ↦
    partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t with hZ_def
  set c : ℕ → ℝ := fun j ↦
    (-b) ^ j * ((4 * j - 1)‼ : ℝ) / (Nat.factorial j : ℝ) with hc_def
  -- The order-n remainder splits as the (n+1)-st term plus the
  -- order-(n+1) remainder.
  have hkey : ∀ t : ℝ, 0 < t →
      (Z t - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 1),
        c j * t ^ (-((j : ℝ) + 1 / 2))) *
        t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2) =
      Real.sqrt (2 * π) * c (n + 1) +
      (Z t - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 2),
        c j * t ^ (-((j : ℝ) + 1 / 2))) *
        t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2) := by
    intro t ht
    have hsum : (∑ j ∈ Finset.range (n + 2),
        c j * t ^ (-((j : ℝ) + 1 / 2))) =
        (∑ j ∈ Finset.range (n + 1), c j * t ^ (-((j : ℝ) + 1 / 2))) +
        c (n + 1) * t ^ (-((((n + 1) : ℕ) : ℝ) + 1 / 2)) := by
      rw [Finset.sum_range_succ]
    have hcancel : t ^ (-((((n + 1) : ℕ) : ℝ) + 1 / 2)) *
        t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2) = 1 := by
      rw [← Real.rpow_add ht,
        show (-((((n + 1) : ℕ) : ℝ) + 1 / 2)) +
          ((((n + 1) : ℕ) : ℝ) + 1 / 2) = 0 by ring,
        Real.rpow_zero]
    calc (Z t - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 1),
          c j * t ^ (-((j : ℝ) + 1 / 2))) *
          t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2)
        = (Z t - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 2),
            c j * t ^ (-((j : ℝ) + 1 / 2))) *
            t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2) +
          Real.sqrt (2 * π) * c (n + 1) *
            (t ^ (-((((n + 1) : ℕ) : ℝ) + 1 / 2)) *
              t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2)) := by
          rw [hsum]
          ring
      _ = Real.sqrt (2 * π) * c (n + 1) +
          (Z t - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 2),
            c j * t ^ (-((j : ℝ) + 1 / 2))) *
            t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2) := by
          rw [hcancel]
          ring
  -- The order-(n+1) remainder, rescaled, tends to zero.
  have hzero : Tendsto (fun t : ℝ ↦
      (Z t - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 2),
        c j * t ^ (-((j : ℝ) + 1 / 2))) *
        t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2)) atTop (nhds 0) := by
    set C : ℝ := Real.sqrt (2 * π) * b ^ (n + 2) *
      ((4 * (n + 2) - 1)‼ : ℝ) / (Nat.factorial (n + 2) : ℝ) with hC_def
    have hbound : ∀ᶠ t : ℝ in atTop,
        ‖(Z t - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 2),
          c j * t ^ (-((j : ℝ) + 1 / 2))) *
          t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2)‖ ≤ C * t⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have h := quartic_partition_expansion_allOrder hb ht (n + 1)
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos ht _)]
      have hstep : |Z t - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 2),
          c j * t ^ (-((j : ℝ) + 1 / 2))| *
          t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2) ≤
          (C * t ^ (-(((n + 2) : ℕ) : ℝ) - 1 / 2)) *
          t ^ ((((n + 1) : ℕ) : ℝ) + 1 / 2) := by
        apply mul_le_mul_of_nonneg_right _
          (Real.rpow_pos_of_pos ht _).le
        calc |Z t - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 2),
              c j * t ^ (-((j : ℝ) + 1 / 2))|
            ≤ Real.sqrt (2 * π) * b ^ (n + 2) *
                ((4 * (n + 2) - 1)‼ : ℝ) / (Nat.factorial (n + 2) : ℝ) *
                t ^ (-(((n + 2) : ℕ) : ℝ) - 1 / 2) := h
          _ = C * t ^ (-(((n + 2) : ℕ) : ℝ) - 1 / 2) := by
              rw [hC_def]
      refine hstep.trans (le_of_eq ?_)
      rw [mul_assoc, ← Real.rpow_add ht]
      have hexp : (-(((n + 2) : ℕ) : ℝ) - 1 / 2) +
          ((((n + 1) : ℕ) : ℝ) + 1 / 2) = -1 := by
        push_cast
        ring
      rw [hexp, Real.rpow_neg_one]
    have hCt : Tendsto (fun t : ℝ ↦ C * t⁻¹) atTop (nhds 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul C
    exact squeeze_zero_norm' hbound hCt
  -- Combine.
  have hconst : Tendsto (fun _ : ℝ ↦ Real.sqrt (2 * π) * c (n + 1))
      atTop (nhds (Real.sqrt (2 * π) * c (n + 1))) := tendsto_const_nhds
  have hcomb := hconst.add hzero
  rw [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (hkey t ht).symm

end Laplace.OneD
