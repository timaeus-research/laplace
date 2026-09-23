/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# Competition between two wells with an energy offset: the hump

When a face form has a zero on the exceptional divisor (a Kouchnirenko-degenerate edge, e.g.
`u²(u²−σ)²` at `u = ±√σ`), the posterior at the layer scale splits into several wells of the same
type, and a further scale appears where the wells that are not true zeros of `F` are switched off
by their energy offset `z = t · F(critical point)`. In the separated-well regime the energy
statistic is a mass-weighted average of the well energies (`twoWell_energy`); for two wells of equal
type and equal mass it is the **hump** `1/2 + z/(1 + e^z)` (`humpProfile`), which starts and ends at
`1/2` and overshoots in between (`humpProfile_zero`, `tendsto_humpProfile_atTop`,
`humpProfile_gt_half`). For wells of unequal type the mass ratio carries a power of `t`, and the
exchange point is not a fixed value of the collapse variable but drifts like `log t`
(`exchange_ge_log`). These are the non-Newton layers of germbij_slop S13 (Astra Tests A and B,
confirmed numerically in `testB.py`).
-/

open Real Filter Topology

namespace Laplace.Multi

/-- Energy statistic of two separated wells with partition masses `A`, `B e^{-z}` and normalised
energies `E₀`, `E₁ + z` (the offset `z` is paid in energy by the lifted well). -/
theorem twoWell_energy {A B E₀ E₁ z : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (E₀ * A + (E₁ + z) * (B * Real.exp (-z))) / (A + B * Real.exp (-z)) =
      (E₀ + (E₁ + z) * (B / A * Real.exp (-z))) / (1 + B / A * Real.exp (-z)) := by
  have hA' : A ≠ 0 := hA.ne'
  field_simp

/-- The hump: two Morse wells of equal mass, one lifted by `z`. -/
noncomputable def humpProfile (z : ℝ) : ℝ := 1 / 2 + z / (1 + Real.exp z)

theorem twoWell_energy_eq_hump {A z : ℝ} (hA : 0 < A) :
    (1 / 2 * A + (1 / 2 + z) * (A * Real.exp (-z))) / (A + A * Real.exp (-z)) = humpProfile z := by
  unfold humpProfile
  rw [Real.exp_neg]
  have he : 0 < Real.exp z := Real.exp_pos z
  have h1 : 0 < 1 + Real.exp z := by positivity
  have hne : A + A * (Real.exp z)⁻¹ ≠ 0 := by positivity
  rw [div_eq_iff hne]
  field_simp
  ring

theorem humpProfile_zero : humpProfile 0 = 1 / 2 := by simp [humpProfile]

theorem humpProfile_gt_half {z : ℝ} (hz : 0 < z) : 1 / 2 < humpProfile z := by
  unfold humpProfile
  have : 0 < z / (1 + Real.exp z) := div_pos hz (by positivity)
  linarith

/-- The lifted well is eventually switched off: `z e^{-z} → 0`. -/
theorem tendsto_humpProfile_atTop : Tendsto humpProfile atTop (𝓝 (1 / 2)) := by
  have h : Tendsto (fun z : ℝ ↦ z / (1 + Real.exp z)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun z : ℝ ↦ z / Real.exp z) atTop (𝓝 0) := by
      have := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
      refine this.congr' (Filter.Eventually.of_forall fun z ↦ ?_)
      simp [Real.exp_neg, div_eq_mul_inv]
    refine squeeze_zero' (Filter.eventually_ge_atTop 0 |>.mono fun z hz ↦ by positivity)
      (Filter.eventually_ge_atTop 0 |>.mono fun z hz ↦ ?_) h1
    exact div_le_div_of_nonneg_left hz (Real.exp_pos z) (by linarith [Real.exp_pos z])
  have := h.const_add (1 / 2 : ℝ)
  rw [add_zero] at this
  exact this

/-- **Log-shifted exchange.** For wells of unequal type the mass ratio is `Q = C t^κ z^β e^{-z}`
(`κ = 1/16`, `β = 3/16` in Astra's Test B). Where the wells exchange dominance (`Q = 1`) the
collapse variable is not fixed but at least `κ log t + log C`: the transition drifts with `t`. -/
theorem exchange_ge_log {C κ β t z : ℝ} (hC : 0 < C) (ht : 0 < t) (hz : 1 ≤ z) (hβ : 0 ≤ β)
    (hQ : C * t ^ κ * z ^ β * Real.exp (-z) = 1) : κ * Real.log t + Real.log C ≤ z := by
  have hzβ : 1 ≤ z ^ β := Real.one_le_rpow hz hβ
  have hpos : 0 < C * t ^ κ := by positivity
  have h1 : Real.exp z = C * t ^ κ * z ^ β := by
    have := hQ
    rw [Real.exp_neg] at this
    field_simp at this
    linarith
  have h2 : C * t ^ κ ≤ Real.exp z := by
    rw [h1]
    exact le_mul_of_one_le_right hpos.le hzβ
  have h3 : Real.log (C * t ^ κ) ≤ z := by
    rw [← Real.log_exp z]
    exact Real.log_le_log hpos h2
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos ht κ).ne', Real.log_rpow ht] at h3
  linarith

end Laplace.Multi
