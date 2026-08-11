/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.AnalyticBridge

/-!
# Rapid decay contradiction

The `IsLittleO` packaging of the germbij Theorem 7.3 contradiction. A
function bounded below by `κ * t ^ γ` for large `t` cannot decay faster
than every negative power (`lower_bound_not_superpolynomial`), so the
pencil difference produced by the analytic multivariate chain does not
decay beyond all orders
(`analytic_pencil_difference_not_superpolynomial`): if the two Laplace
families agreed to all orders against the observable `(L₂ - L₁)ψ`, the
germs of `L₁` and `L₂` at `0` would have to coincide.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal

namespace Laplace

/-- A function eventually bounded below by `κ * t ^ γ` with `κ > 0` does
not decay faster than every negative power of `t`. -/
theorem lower_bound_not_superpolynomial {Δ : ℝ → ℝ} {κ T₀ γ : ℝ}
    (hκ : 0 < κ) (hbound : ∀ t : ℝ, T₀ ≤ t → κ * t ^ γ ≤ Δ t)
    (hdecay : ∀ N : ℕ, Δ =o[atTop] fun t : ℝ ↦ t ^ (-(N : ℝ))) :
    False := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-γ)
  have hγN : 0 ≤ γ + N := by linarith
  have hev := (isLittleO_iff.mp (hdecay N)) (half_pos hκ)
  obtain ⟨t, ht1, ht2⟩ := (hev.and (eventually_ge_atTop (max T₀ 1))).exists
  have h1t : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) ht2
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos h1t
  have hXpos : (0 : ℝ) < t ^ (-(N : ℝ)) := Real.rpow_pos_of_pos ht0 _
  have hnorm : ‖t ^ (-(N : ℝ))‖ = t ^ (-(N : ℝ)) :=
    Real.norm_of_nonneg hXpos.le
  have hkey : t ^ (-(N : ℝ)) ≤ t ^ γ :=
    calc t ^ (-(N : ℝ)) = t ^ (-(N : ℝ)) * 1 := (mul_one _).symm
      _ ≤ t ^ (-(N : ℝ)) * t ^ (γ + N) :=
          mul_le_mul_of_nonneg_left (Real.one_le_rpow h1t hγN) hXpos.le
      _ = t ^ γ := by rw [← Real.rpow_add ht0]; congr 1; ring
  have hchain : κ * t ^ (-(N : ℝ)) ≤ κ / 2 * t ^ (-(N : ℝ)) :=
    calc κ * t ^ (-(N : ℝ)) ≤ κ * t ^ γ :=
          mul_le_mul_of_nonneg_left hkey hκ.le
      _ ≤ Δ t := hbound t (le_trans (le_max_left _ _) ht2)
      _ ≤ ‖Δ t‖ := le_abs_self _
      _ ≤ κ / 2 * t ^ (-(N : ℝ)) := by rw [← hnorm]; exact ht1
  have : κ ≤ κ / 2 := le_of_mul_le_mul_right hchain hXpos
  linarith

/-- **The germbij Theorem 7.3 contradiction, multivariate** (analytic
hypotheses). The pencil difference against the observable `(L₂ - L₁)ψ`
does not decay faster than every negative power of `t`: agreement of the
two Laplace families beyond all orders is impossible while the diagonal
power series data of `L₂ - L₁` at `0` is nonzero. -/
theorem analytic_pencil_difference_not_superpolynomial
    {ι : Type*} [Fintype ι] (L₁ L₂ ψ : (ι → ℝ) → ℝ)
    {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} {r : ℝ≥0∞} (m : ℕ)
    (hg : HasFPowerSeriesOnBall (fun w ↦ L₂ w - L₁ w) p 0 r)
    (hlow : ∀ k, k < m → ∀ x : ι → ℝ, (p k) (fun _ ↦ x) = 0)
    {x₀ : ι → ℝ} (hx₀ : (p m) (fun _ ↦ x₀) ≠ 0) (hx₀n : ‖x₀‖ = 3 / 2)
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hsum : ∀ w : ι → ℝ, ‖w‖ ≤ R → L₁ w + L₂ w ≤ C0 * ‖w‖ ^ 2)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ R → ψ w = 1) :
    ¬ ∀ N : ℕ,
      (fun t : ℝ ↦ ∫ w, ((L₂ w - L₁ w) * ψ w) *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))))
        =o[atTop] fun t : ℝ ↦ t ^ (-(N : ℝ)) := by
  intro hdecay
  obtain ⟨κ, T₀, hκ, hT₀, hbound⟩ :=
    analytic_pencil_difference_lower_bound_multi L₁ L₂ ψ m hg hlow hx₀ hx₀n
      hL1c hL2c hL1 hL2 hC0 hR hsum hψc hψs hψ0 hψ1
  refine lower_bound_not_superpolynomial (T₀ := T₀)
    (γ := 1 - (m : ℝ) - (Fintype.card ι : ℝ) / 2) hκ
    (fun t (ht : T₀ ≤ t) ↦ ?_) hdecay
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hT₀ ht
  calc κ * t ^ (1 - (m : ℝ) - (Fintype.card ι : ℝ) / 2)
      = κ * (t * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2)) := by
        rw [show (1 - (m : ℝ) - (Fintype.card ι : ℝ) / 2)
            = 1 + (-(m : ℝ) - (Fintype.card ι : ℝ) / 2) by ring,
          Real.rpow_add ht0, Real.rpow_one]
    _ ≤ _ := hbound t ht

end Laplace
