/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMap

/-!
# The Gibbs variational principle for the response map

For a probability density `ρ` (relative to `μ`, absolutely continuous with respect to the prior
density `π`) the **Gibbs gap identity** is

  `t E_ρ[L] + KL(ρ ‖ π) = −log Z_t(L) + KL(ρ ‖ ρ_{t,L})`   (`gibbs_gap`),

where `ρ_{t,L} = e^{-tL} π / Z_t(L)` is the Gibbs density and `KL(ρ ‖ π) = ∫ ρ log (ρ/π)`
(`relEnt`). Since `KL(ρ ‖ ρ_{t,L}) ≥ 0` (`relEnt_gibbsDensity_nonneg`, Gibbs' inequality through
`log y ≤ y − 1`), the free energy is the infimum of the variational objective,

  `F_t(L) = −log Z_t(L) ≤ t E_ρ[L] + KL(ρ ‖ π)`   (`gibbs_variational`),

attained at the Gibbs density (`gibbs_variational_eq`). In the language of the response map: the
posterior `ρ_{t,q}` is the unique minimiser of `t E_ρ[L_q] + KL(ρ ‖ π)`, the free energy `F_t(q)` is
an infimum of functions affine in `q`, hence concave on the convex space of data distributions,
and the objective gap of any approximate posterior is exactly its KL error.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The relative entropy `KL(ρ ‖ π) = ∫ ρ log (ρ/π)` of two densities. -/
noncomputable def relEnt (ρ π : X → ℝ) : ℝ := ∫ x, ρ x * Real.log (ρ x / π x) ∂μ

/-- The Gibbs density `ρ_{t,L} = e^{-tL} π / Z_t(L)`. -/
noncomputable def gibbsDensity (π L : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  Real.exp (-(t * L x)) * π x / priorZ μ π L t

variable {μ}

theorem gibbsDensity_nonneg {π L : X → ℝ} (hπ : ∀ x, 0 ≤ π x) {t : ℝ}
    (hZ : 0 < priorZ μ π L t) (x : X) : 0 ≤ gibbsDensity μ π L t x :=
  div_nonneg (mul_nonneg (Real.exp_pos _).le (hπ x)) hZ.le

theorem gibbsDensity_pos {π L : X → ℝ} (hπ : ∀ x, 0 ≤ π x) {t : ℝ} (hZ : 0 < priorZ μ π L t)
    {x : X} (hx : π x ≠ 0) : 0 < gibbsDensity μ π L t x :=
  div_pos (mul_pos (Real.exp_pos _) (lt_of_le_of_ne (hπ x) (Ne.symm hx))) hZ

/-- The Gibbs density integrates to one. -/
theorem integral_gibbsDensity {π L : X → ℝ} {t : ℝ} (hZ : 0 < priorZ μ π L t) :
    ∫ x, gibbsDensity μ π L t x ∂μ = 1 := by
  unfold gibbsDensity
  rw [integral_div]
  exact div_self hZ.ne'

theorem integrable_gibbsDensity {π L : X → ℝ} {t : ℝ}
    (hZint : Integrable (fun x ↦ Real.exp (-(t * L x)) * π x) μ) :
    Integrable (gibbsDensity μ π L t) μ :=
  hZint.div_const _

/-- The pointwise log-density identity `log (ρ/ρ_{t,L}) = log (ρ/π) + tL + log Z`. -/
theorem log_div_gibbsDensity {ρ π L : X → ℝ} {t : ℝ} (hZ : 0 < priorZ μ π L t) {x : X}
    (hρ : ρ x ≠ 0) (hπ : π x ≠ 0) :
    Real.log (ρ x / gibbsDensity μ π L t x) =
      Real.log (ρ x / π x) + (t * L x + Real.log (priorZ μ π L t)) := by
  unfold gibbsDensity
  have he : Real.exp (-(t * L x)) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.log_div hρ (div_ne_zero (mul_ne_zero he hπ) hZ.ne'), Real.log_div (mul_ne_zero he hπ)
    hZ.ne', Real.log_mul he hπ, Real.log_exp, Real.log_div hρ hπ]
  ring

/-- **The Gibbs gap identity**: `t E_ρ[L] + KL(ρ ‖ π) = −log Z_t(L) + KL(ρ ‖ ρ_{t,L})` for a
probability density `ρ` absolutely continuous with respect to `π`. -/
theorem gibbs_gap {ρ π L : X → ℝ} {t : ℝ} (hZ : 0 < priorZ μ π L t)
    (hsupp : ∀ x, ρ x ≠ 0 → π x ≠ 0) (hρ1 : ∫ x, ρ x ∂μ = 1) (hρi : Integrable ρ μ)
    (hρL : Integrable (fun x ↦ ρ x * L x) μ)
    (hρπ : Integrable (fun x ↦ ρ x * Real.log (ρ x / π x)) μ) :
    t * ∫ x, ρ x * L x ∂μ + relEnt μ ρ π =
      -Real.log (priorZ μ π L t) + relEnt μ ρ (gibbsDensity μ π L t) := by
  have hpt : ∀ x, ρ x * Real.log (ρ x / gibbsDensity μ π L t x) =
      ρ x * Real.log (ρ x / π x) + (t * (ρ x * L x) + Real.log (priorZ μ π L t) * ρ x) := by
    intro x
    by_cases hρ : ρ x = 0
    · simp [hρ]
    · rw [log_div_gibbsDensity hZ hρ (hsupp x hρ)]
      ring
  have h2 : Integrable (fun x ↦ t * (ρ x * L x) + Real.log (priorZ μ π L t) * ρ x) μ :=
    (hρL.const_mul t).add (hρi.const_mul _)
  unfold relEnt
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hρπ h2,
    integral_add (hρL.const_mul t) (hρi.const_mul _), integral_const_mul, integral_const_mul, hρ1]
  ring

/-- **Gibbs' inequality**: `KL(ρ ‖ ρ_{t,L}) ≥ 0` for a probability density `ρ` absolutely
continuous with respect to `π`. -/
theorem relEnt_gibbsDensity_nonneg {ρ π L : X → ℝ} {t : ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hZ : 0 < priorZ μ π L t) (hZint : Integrable (fun x ↦ Real.exp (-(t * L x)) * π x) μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hsupp : ∀ x, ρ x ≠ 0 → π x ≠ 0) (hρ1 : ∫ x, ρ x ∂μ = 1)
    (hρi : Integrable ρ μ)
    (hint : Integrable (fun x ↦ ρ x * Real.log (ρ x / gibbsDensity μ π L t x)) μ) :
    0 ≤ relEnt μ ρ (gibbsDensity μ π L t) := by
  have hg1 := integral_gibbsDensity (μ := μ) hZ
  have hgi := integrable_gibbsDensity (μ := μ) hZint
  have hpt : ∀ x, ρ x - gibbsDensity μ π L t x ≤
      ρ x * Real.log (ρ x / gibbsDensity μ π L t x) := by
    intro x
    by_cases hρ : ρ x = 0
    · rw [hρ]
      simp only [zero_sub, zero_mul]
      exact neg_nonpos.mpr (gibbsDensity_nonneg hπ hZ x)
    · have hρpos : 0 < ρ x := lt_of_le_of_ne (hρ0 x) (Ne.symm hρ)
      have hgpos := gibbsDensity_pos hπ hZ (hsupp x hρ)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hgpos hρpos)
      rw [Real.log_div hgpos.ne' hρ] at hlog
      rw [Real.log_div hρ hgpos.ne']
      have : gibbsDensity μ π L t x / ρ x - 1 = (gibbsDensity μ π L t x - ρ x) / ρ x := by
        field_simp
      rw [this, le_div_iff₀ hρpos] at hlog
      nlinarith
  have hsub : Integrable (fun x ↦ ρ x - gibbsDensity μ π L t x) μ := hρi.sub hgi
  have := integral_mono hsub hint hpt
  rw [integral_sub hρi hgi, hρ1, hg1, sub_self] at this
  exact this

/-- **The Gibbs variational principle**: `−log Z_t(L) ≤ t E_ρ[L] + KL(ρ ‖ π)` for every probability
density `ρ` absolutely continuous with respect to `π`. -/
theorem gibbs_variational {ρ π L : X → ℝ} {t : ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hZ : 0 < priorZ μ π L t) (hZint : Integrable (fun x ↦ Real.exp (-(t * L x)) * π x) μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hsupp : ∀ x, ρ x ≠ 0 → π x ≠ 0) (hρ1 : ∫ x, ρ x ∂μ = 1)
    (hρi : Integrable ρ μ) (hρL : Integrable (fun x ↦ ρ x * L x) μ)
    (hρπ : Integrable (fun x ↦ ρ x * Real.log (ρ x / π x)) μ) :
    -Real.log (priorZ μ π L t) ≤ t * ∫ x, ρ x * L x ∂μ + relEnt μ ρ π := by
  have hint : Integrable (fun x ↦ ρ x * Real.log (ρ x / gibbsDensity μ π L t x)) μ := by
    refine (hρπ.add ((hρL.const_mul t).add (hρi.const_mul (Real.log (priorZ μ π L t))))).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply]
    by_cases hρ : ρ x = 0
    · simp [hρ]
    · rw [log_div_gibbsDensity hZ hρ (hsupp x hρ)]
      ring
  have := relEnt_gibbsDensity_nonneg hπ hZ hZint hρ0 hsupp hρ1 hρi hint
  rw [gibbs_gap hZ hsupp hρ1 hρi hρL hρπ]
  linarith

/-- The Gibbs density attains the variational bound: `KL(ρ_{t,L} ‖ ρ_{t,L}) = 0`, so
`t E_{ρ_{t,L}}[L] + KL(ρ_{t,L} ‖ π) = −log Z_t(L)`. -/
theorem gibbs_variational_eq {π L : X → ℝ} {t : ℝ}
    (hZ : 0 < priorZ μ π L t) (hZint : Integrable (fun x ↦ Real.exp (-(t * L x)) * π x) μ)
    (hgL : Integrable (fun x ↦ gibbsDensity μ π L t x * L x) μ)
    (hgπ : Integrable (fun x ↦ gibbsDensity μ π L t x *
      Real.log (gibbsDensity μ π L t x / π x)) μ) :
    t * ∫ x, gibbsDensity μ π L t x * L x ∂μ + relEnt μ (gibbsDensity μ π L t) π =
      -Real.log (priorZ μ π L t) := by
  have hsupp : ∀ x, gibbsDensity μ π L t x ≠ 0 → π x ≠ 0 := fun x hx hπx ↦ by
    apply hx
    simp [gibbsDensity, hπx]
  rw [gibbs_gap hZ hsupp (integral_gibbsDensity hZ) (integrable_gibbsDensity hZint) hgL hgπ]
  have : relEnt μ (gibbsDensity μ π L t) (gibbsDensity μ π L t) = 0 := by
    unfold relEnt
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    by_cases hx : gibbsDensity μ π L t x = 0
    · simp [hx]
    · simp [div_self hx]
  rw [this, add_zero]

end Laplace.Multi
