/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NewtonEdge

/-!
# The residual on the exceptional divisor is the edge form

Weighted blow-up chart of the `(x, s)`-plane at the wall point with weights `(α, γ)`:
`x = v^α u`, `s = σ v^γ` (the divisor is `v = 0`, `(u, σ)` are coordinates on it). For a
quasi-homogeneous edge form the pull-back is exactly `v · E(u, σ)` (`QuasiHomog.residual`), and for
`F = E + R` with `R` of higher weight the residual `F ∘ g / v` tends to the edge form as `v → 0⁺`
(`EdgeData.tendsto_residual`). The `R_lim` hypothesis of `EdgeData` is literally this divisor
statement with `v = 1/t`: the collapse exponent `γ`, the collapse variable `σ` and the crossover
profile are read off the exceptional divisor (germbij_slop S13).
-/

open Real Filter Topology

namespace Laplace.Multi

/-- The edge form pulls back to `v · E(u, σ)` along the weighted blow-up chart. -/
theorem QuasiHomog.residual {E : ℝ → ℝ → ℝ} {α γ : ℝ} (hE : QuasiHomog E α γ) {v : ℝ} (hv : 0 < v)
    (u σ : ℝ) : E (v ^ α * u) (σ * v ^ γ) = v * E u σ := by
  rw [mul_comm σ]
  exact hE v hv u σ

/-- **Residual on the divisor.** For `F = E + R` satisfying the Newton-edge hypotheses at `σ`, the
residual `F(v^α u, σ v^γ) / v` tends to the edge form `E(u, σ)` as `v → 0⁺`. -/
theorem EdgeData.tendsto_residual {E R : ℝ → ℝ → ℝ} {α γ σ : ℝ} (hd : EdgeData E R α γ σ) (u : ℝ) :
    Tendsto (fun v ↦ (E (v ^ α * u) (σ * v ^ γ) + R (v ^ α * u) (σ * v ^ γ)) / v) (𝓝[>] 0)
      (𝓝 (E u σ)) := by
  have h2 := (hd.R_lim u).comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  have h3 := h2.const_add (E u σ)
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv : 0 < v := hv
  have hα : (v⁻¹) ^ (-α) = v ^ α := by
    rw [Real.inv_rpow hv.le, Real.rpow_neg hv.le, inv_inv]
  have hγ : (v⁻¹) ^ (-γ) = v ^ γ := by
    rw [Real.inv_rpow hv.le, Real.rpow_neg hv.le, inv_inv]
  simp only [Function.comp, hα, hγ]
  rw [hd.quasi.residual hv, add_div, mul_div_cancel_left₀ _ hv.ne', div_eq_inv_mul]

end Laplace.Multi
