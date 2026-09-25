/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MeanJourney

/-!
# The two journeys have the same Fisher energy

The natural journey `a₀ + s(a₁ − a₀)` has Fisher energy `E_e = t² ∫₀¹ Var_{a(s)}(R_{Δa}) ds` and the
mean journey `m₀ + s(m₁ − m₀)` has energy `E_m = ∫₀¹ Δm ⬝ Cov⁻¹ Δm ds`. Both equal the Jeffreys
divergence: `E_m` by `famKL_add_famKL_eq_integral_meanSpeed`, and `E_e` because the mean of `R_{Δa}`
moves along the natural segment at rate `−t Var(R_{Δa})`, so `E_e = −t Δa·Δm`
(`natural_energy_eq`), which is the symmetrised divergence (`famKL_add_famKL_eq_neg_mul_dot`). Hence
`E_e = E_m = KL(P_{a₁}‖P_{a₀}) + KL(P_{a₀}‖P_{a₁})` (`natural_energy_eq_mean_energy`) and
both
Fisher lengths are bounded by the square root of the Jeffreys divergence
(`sq_natural_length_le_jeffreys`, `sq_integral_sqrt_meanSpeed_le`), with equality exactly at
constant
Fisher speed. Dual flatness supplies no general ordering between the two lengths.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- **The Fisher energy of the natural journey is `−t Δa·Δm`.** -/
theorem natural_energy_eq (a₀ a₁ : ι → ℝ) :
    t ^ 2 * ∫ s in (0 : ℝ)..1, segVar μ π L₀ R t a₀ (a₁ - a₀) s =
      -t * dotJ (a₁ - a₀) (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) := by
  have hD := hasDerivAt_segMean hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀ (a₁ - a₀)
  have hcont : ContinuousOn (fun s ↦ -t * segVar μ π L₀ R t a₀ (a₁ - a₀) s) (uIcc (0 : ℝ) 1) :=
    ((continuous_segVar hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀ _).const_mul _).continuousOn
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hD s)
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hZ : ∀ a, Integrable (baseWeight π (affLoss L₀ R a) t) μ := fun a ↦
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  simp only [one_smul, add_sub_cancel, zero_smul, add_zero] at hFTC
  rw [priorExp_dirLoss (hZ a₁) hR, priorExp_dirLoss (hZ a₀) hR] at hFTC
  have e : t ^ 2 * ∫ s in (0 : ℝ)..1, segVar μ π L₀ R t a₀ (a₁ - a₀) s =
      -t * (-t * ∫ s in (0 : ℝ)..1, segVar μ π L₀ R t a₀ (a₁ - a₀) s) := by ring
  rw [e, hFTC]
  simp only [dotJ, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, meanMap]

omit ht in
/-- **Jeffreys' divergence is `−t Δa·Δm`.** -/
theorem famKL_add_famKL_eq_neg_mul_dot (a₀ a₁ : ι → ℝ) :
    famKL μ π L₀ R t a₁ a₀ + famKL μ π L₀ R t a₀ a₁ =
      -t * dotJ (a₁ - a₀) (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) := by
  rw [famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR, famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR]
  simp only [dotJ, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
    neg_mul, Finset.sum_neg_distrib]
  ring

/-- **Equal energy**: the natural journey and the mean journey have the same Fisher energy, the
Jeffreys divergence. -/
theorem natural_energy_eq_mean_energy [DecidableEq ι]
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) [Nonempty ι]
    (a₀ a₁ : ι → ℝ) :
    t ^ 2 * ∫ s in (0 : ℝ)..1, segVar μ π L₀ R t a₀ (a₁ - a₀) s =
      ∫ s in (0 : ℝ)..1, meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀)
        (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) s := by
  rw [natural_energy_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht,
    ← famKL_add_famKL_eq_neg_mul_dot hπm hπi hπ hπpos hL₀m hL₀ hR (t := t),
    famKL_add_famKL_eq_integral_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]

/-- **The natural Fisher length is bounded by the square root of Jeffreys' divergence.** -/
theorem sq_natural_length_le_jeffreys (a₀ a₁ : ι → ℝ) :
    (∫ s in (0 : ℝ)..1, Real.sqrt (t ^ 2 * segVar μ π L₀ R t a₀ (a₁ - a₀) s)) ^ 2 ≤
      famKL μ π L₀ R t a₁ a₀ + famKL μ π L₀ R t a₀ a₁ := by
  rw [famKL_add_famKL_eq_neg_mul_dot hπm hπi hπ hπpos hL₀m hL₀ hR (t := t),
    ← natural_energy_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht, ← intervalIntegral.integral_const_mul]
  have h := sq_integral_sqrt_mul_le (f := fun s ↦ t ^ 2 * segVar μ π L₀ R t a₀ (a₁ - a₀) s)
    (g := fun _ ↦ (1 : ℝ))
    ((continuous_segVar hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀ _).const_mul _).continuousOn
    continuousOn_const
    (fun s _ ↦ mul_nonneg (sq_nonneg t) (segVar_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR a₀ _ s))
    (fun _ _ ↦ zero_le_one)
  simpa using h

end

end Laplace.Multi
