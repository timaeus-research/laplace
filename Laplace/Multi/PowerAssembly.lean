/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# Finite assembly of kernels certified at pure power scales

If finitely many kernels satisfy `t^{λ_i} K_i(t) → C_i`, then at the reference scale
`λ₀ ≤ λ_i` each contributes `C_i` when `λ_i = λ₀` and `0` otherwise
(`tendsto_rpow_mul_of_certified`), so the ratio of two such finite sums converges to the ratio of
the dominant constants provided the dominant denominator constant is nonzero
(`tendsto_sum_ratio`). This is the pure-power case of the cluster assembly, with the
non-dominant terms absorbed automatically (no positivity of every constant is needed).
-/

open Filter Topology Real

namespace Laplace.Multi

theorem tendsto_rpow_mul_of_certified {K : ℝ → ℝ} {lam lam₀ C : ℝ} (hmin : lam₀ ≤ lam)
    (hK : Tendsto (fun t ↦ t ^ lam * K t) atTop (𝓝 C)) :
    Tendsto (fun t ↦ t ^ lam₀ * K t) atTop (𝓝 (if lam = lam₀ then C else 0)) := by
  by_cases h : lam = lam₀
  · rw [if_pos h, ← h]
    exact hK
  · rw [if_neg h]
    have hlt : lam₀ < lam := lt_of_le_of_ne hmin (Ne.symm h)
    have h1 : Tendsto (fun t : ℝ ↦ t ^ (lam₀ - lam)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (sub_pos.mpr hlt)
      simpa [neg_sub] using this
    have h2 := h1.mul hK
    rw [zero_mul] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [← mul_assoc, ← Real.rpow_add ht, sub_add_cancel]

variable {ι : Type*} [Fintype ι]

/-- **Finite pure-power assembly**: the ratio of two finite sums of certified kernels converges to
the ratio of the dominant constants. -/
theorem tendsto_sum_ratio {K Kφ : ι → ℝ → ℝ} {lam C J : ι → ℝ} {lam₀ : ℝ}
    (hmin : ∀ i, lam₀ ≤ lam i)
    (hK : ∀ i, Tendsto (fun t ↦ t ^ lam i * K i t) atTop (𝓝 (C i)))
    (hKφ : ∀ i, Tendsto (fun t ↦ t ^ lam i * Kφ i t) atTop (𝓝 (J i)))
    (hpos : (∑ i, if lam i = lam₀ then C i else 0) ≠ 0) :
    Tendsto (fun t ↦ (∑ i, Kφ i t) / ∑ i, K i t) atTop
      (𝓝 ((∑ i, if lam i = lam₀ then J i else 0) / ∑ i, if lam i = lam₀ then C i else 0)) := by
  have hden : Tendsto (fun t ↦ ∑ i, t ^ lam₀ * K i t) atTop
      (𝓝 (∑ i, if lam i = lam₀ then C i else 0)) :=
    tendsto_finsetSum _ fun i _ ↦ tendsto_rpow_mul_of_certified (hmin i) (hK i)
  have hnum : Tendsto (fun t ↦ ∑ i, t ^ lam₀ * Kφ i t) atTop
      (𝓝 (∑ i, if lam i = lam₀ then J i else 0)) :=
    tendsto_finsetSum _ fun i _ ↦ tendsto_rpow_mul_of_certified (hmin i) (hKφ i)
  refine (hnum.div hden hpos).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Pi.div_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ (rpow_pos_of_pos ht _).ne']

end Laplace.Multi
