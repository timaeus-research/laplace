/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.LeadingPart
import Laplace.Multi.Identifiability

/-!
# The identifiability lower bound from leading-part structure

The multivariate analogue of the 1D analytic corollary: composing the
leading-part instantiation (`leading_part_scaled_set`) with the multivariate
composite (`pencil_difference_lower_bound_multi`). For nonnegative
potentials on `ι → ℝ` whose difference has a continuous homogeneous leading
part of degree `m`, nonzero in some direction, with an order-`(m+1)`
remainder, and which are dominated by `C0 ‖w‖²` near `0`: there are
constants `κ > 0` and `T₀ > 0` such that for every `t ≥ T₀` (under the
per-`t` integrability premises) the observable `(L₂ - L₁) ψ` witnesses

  `κ · t · t^(-m - d/2) ≤ ∫ (L₂ - L₁) ψ (e^{-t L₁} - e^{-t L₂})`,

so the two Boltzmann families cannot agree to all polynomial orders. With
this the multivariate chain runs from Taylor structure end to end, parallel
to the 1D chain from analyticity.
-/

open MeasureTheory

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- **Identifiability lower bound from leading-part structure**
(germbij Theorem 7.3, `ℝ^d`, Taylor hypotheses). Constants first, then all
`t ≥ T₀`; integrability premises are per-`t`. -/
theorem leading_part_pencil_difference_lower_bound
    (L₁ L₂ ψ P : (ι → ℝ) → ℝ) (m : ℕ)
    (hPc : Continuous P)
    (hPh : ∀ (c : ℝ) (x : ι → ℝ), 0 ≤ c → P (c • x) = c ^ m * P x)
    {x₀ : ι → ℝ} (hx₀ : P x₀ ≠ 0) (hx₀n : ‖x₀‖ = 3 / 2)
    {C u₁ : ℝ} (hC : 0 ≤ C) (hu₁ : 0 < u₁)
    (hrem : ∀ x : ι → ℝ, ‖x‖ ≤ 2 * u₁ →
      |(L₂ x - L₁ x) - P x| ≤ C * ‖x‖ ^ (m + 1))
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hsum : ∀ w : ι → ℝ, ‖w‖ ≤ R → L₁ w + L₂ w ≤ C0 * ‖w‖ ^ 2)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ R → ψ w = 1) :
    ∃ (κ T₀ : ℝ), 0 < κ ∧ 0 < T₀ ∧
      ∀ t : ℝ, T₀ ≤ t →
        Integrable (fun w ↦ (L₂ w - L₁ w) ^ 2 * ψ w *
          Real.exp (-(t * (L₁ w + L₂ w)))) →
        Integrable (Function.uncurry fun s w ↦
          ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
          ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, Integrable fun w ↦
          ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))))) →
        κ * (t * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2))
          ≤ ∫ w, ((L₂ w - L₁ w) * ψ w) *
              (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := by
  obtain ⟨S, c, u₀, hS, hSfin, hSvol0, hSnorm, hc, hu₀, hbound⟩ :=
    leading_part_scaled_set (fun w ↦ L₂ w - L₁ w) P m hPc hPh hx₀ hx₀n
      hC hu₁ hrem
  have hvolpos : 0 < (volume S).toReal := ENNReal.toReal_pos hSvol0 hSfin
  refine ⟨(volume S).toReal * (c ^ 2 * Real.exp (-(4 * C0))),
    max (4 / R ^ 2) (u₀⁻¹ ^ 2), by positivity,
    lt_max_of_lt_left (by positivity), ?_⟩
  intro t ht hmin hint hslice
  have htpos : 0 < t :=
    lt_of_lt_of_le (lt_max_of_lt_left (by positivity : (0:ℝ) < 4 / R ^ 2)) ht
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  -- The window condition.
  have ht4 : 4 ≤ R ^ 2 * t := by
    have h1 : 4 / R ^ 2 ≤ t := le_trans (le_max_left _ _) ht
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    calc (4 : ℝ) = R ^ 2 * (4 / R ^ 2) := by field_simp
      _ ≤ R ^ 2 * t := mul_le_mul_of_nonneg_left h1 hR2.le
  -- The leading-part scale condition.
  have hinvle : (Real.sqrt t)⁻¹ ≤ u₀ := by
    have h2 : u₀⁻¹ ^ 2 ≤ t := le_trans (le_max_right _ _) ht
    have h3 : u₀⁻¹ ≤ Real.sqrt t := by
      rw [show u₀⁻¹ = Real.sqrt (u₀⁻¹ ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt h2
    rw [inv_le_comm₀ hst hu₀]
    exact h3
  have hgrow : ∀ x ∈ S, c * ((Real.sqrt t)⁻¹) ^ m
      ≤ |L₂ ((Real.sqrt t)⁻¹ • x) - L₁ ((Real.sqrt t)⁻¹ • x)| := by
    intro x hx
    have h := hbound ((Real.sqrt t)⁻¹) ⟨inv_pos.mpr hst, hinvle⟩ x hx
    simpa using h
  have h := pencil_difference_lower_bound_multi L₁ L₂ ψ m hS hSfin hc.le hC0
    hR ht4 hL1 hL2 hSnorm hsum hgrow hψ0 hψ1 hmin hint hslice
  calc (volume S).toReal * (c ^ 2 * Real.exp (-(4 * C0))) *
        (t * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2))
      = (volume S).toReal * (c ^ 2 * Real.exp (-(4 * C0)) *
          (t * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2))) := by ring
    _ ≤ _ := h

end Laplace
