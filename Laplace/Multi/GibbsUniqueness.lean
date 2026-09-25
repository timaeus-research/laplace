/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.GibbsVariational

/-!
# Uniqueness of the Gibbs minimiser

The Gibbs variational principle (`GibbsVariational`) bounds `t E_ρ[L] + KL(ρ ‖ π)` below by the
free energy, with equality at the Gibbs density. Here we prove the converse: a probability density
`ρ` with `KL(ρ ‖ ρ_{t,L}) = 0` coincides with `ρ_{t,L}` almost everywhere
(`ae_eq_gibbsDensity_of_relEnt_eq_zero`), hence the variational bound is attained **only** by
the posterior (`ae_eq_gibbsDensity_of_variational_eq`). The proof is the strict form of Gibbs'
inequality: `log y < y − 1` for `y ≠ 1`, so the pointwise defect `ρ log(ρ/ρ_t) − (ρ − ρ_t) ≥ 0`
integrates to `KL(ρ ‖ ρ_t)` and vanishes a.e. only where `ρ = ρ_t`. In the language of the response
map: the posterior `ρ_{t,q}` is the unique output of the variational characterisation at every
point `q` of the data manifold.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The pointwise defect `ρ log(ρ/ρ_t) − (ρ − ρ_t)` is nonnegative and vanishes only where
`ρ = ρ_t` (for `ρ` absolutely continuous with respect to `π`). -/
theorem defect_eq_zero_iff {ρ π L : X → ℝ} {t : ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hZ : 0 < priorZ μ π L t) (hρ0 : ∀ x, 0 ≤ ρ x) (hsupp : ∀ x, ρ x ≠ 0 → π x ≠ 0) (x : X)
    (h0 : ρ x * Real.log (ρ x / gibbsDensity μ π L t x) - (ρ x - gibbsDensity μ π L t x) = 0) :
    ρ x = gibbsDensity μ π L t x := by
  by_cases hρ : ρ x = 0
  · rw [hρ] at h0 ⊢
    simp only [zero_mul, zero_sub, sub_neg_eq_add, zero_add] at h0
    exact h0.symm
  · have hρpos : 0 < ρ x := lt_of_le_of_ne (hρ0 x) (Ne.symm hρ)
    have hgpos := gibbsDensity_pos hπ hZ (hsupp x hρ)
    set g := gibbsDensity μ π L t x with hg
    by_contra hne
    have hy1 : g / ρ x ≠ 1 := by
      intro h1
      rw [div_eq_one_iff_eq hρ] at h1
      exact hne h1.symm
    have hlt := Real.log_lt_sub_one_of_pos (div_pos hgpos hρpos) hy1
    rw [Real.log_div hgpos.ne' hρ] at hlt
    have hlog : Real.log (ρ x / g) = -(Real.log g - Real.log (ρ x)) := by
      rw [Real.log_div hρ hgpos.ne']
      ring
    rw [hlog] at h0
    have : g / ρ x - 1 = (g - ρ x) / ρ x := by field_simp
    rw [this, lt_div_iff₀ hρpos] at hlt
    nlinarith

/-- **Uniqueness of the Gibbs minimiser**: `KL(ρ ‖ ρ_{t,L}) = 0` forces `ρ = ρ_{t,L}` a.e. -/
theorem ae_eq_gibbsDensity_of_relEnt_eq_zero {ρ π L : X → ℝ} {t : ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hZ : 0 < priorZ μ π L t) (hZint : Integrable (fun x ↦ Real.exp (-(t * L x)) * π x) μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hsupp : ∀ x, ρ x ≠ 0 → π x ≠ 0) (hρ1 : ∫ x, ρ x ∂μ = 1)
    (hρi : Integrable ρ μ)
    (hint : Integrable (fun x ↦ ρ x * Real.log (ρ x / gibbsDensity μ π L t x)) μ)
    (h0 : relEnt μ ρ (gibbsDensity μ π L t) = 0) : ρ =ᵐ[μ] gibbsDensity μ π L t := by
  have hg1 := integral_gibbsDensity (μ := μ) hZ
  have hgi := integrable_gibbsDensity (μ := μ) hZint
  have hsub : Integrable (fun x ↦ ρ x - gibbsDensity μ π L t x) μ := hρi.sub hgi
  -- the defect integrates to `KL − (1 − 1) = 0`
  have hdef : ∫ x, (ρ x * Real.log (ρ x / gibbsDensity μ π L t x) -
      (ρ x - gibbsDensity μ π L t x)) ∂μ = 0 := by
    rw [integral_sub hint hsub, integral_sub hρi hgi, hρ1, hg1]
    unfold relEnt at h0
    rw [h0]
    ring
  have hnn : ∀ x, 0 ≤ ρ x * Real.log (ρ x / gibbsDensity μ π L t x) -
      (ρ x - gibbsDensity μ π L t x) := by
    intro x
    by_cases hρ : ρ x = 0
    · rw [hρ]
      simp only [zero_mul, zero_sub, sub_neg_eq_add, zero_add]
      exact gibbsDensity_nonneg hπ hZ x
    · have hρpos : 0 < ρ x := lt_of_le_of_ne (hρ0 x) (Ne.symm hρ)
      have hgpos := gibbsDensity_pos hπ hZ (hsupp x hρ)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hgpos hρpos)
      rw [Real.log_div hgpos.ne' hρ] at hlog
      rw [Real.log_div hρ hgpos.ne']
      have : gibbsDensity μ π L t x / ρ x - 1 = (gibbsDensity μ π L t x - ρ x) / ρ x := by
        field_simp
      rw [this, le_div_iff₀ hρpos] at hlog
      nlinarith
  have hdefint : Integrable (fun x ↦ ρ x * Real.log (ρ x / gibbsDensity μ π L t x) -
      (ρ x - gibbsDensity μ π L t x)) μ := hint.sub hsub
  have hzero := (integral_eq_zero_iff_of_nonneg hnn hdefint).mp hdef
  filter_upwards [hzero] with x hx
  exact defect_eq_zero_iff hπ hZ hρ0 hsupp x hx

/-- **The variational bound is attained only at the posterior**: if `t E_ρ[L] + KL(ρ ‖ π) = −log Z`
then `ρ = ρ_{t,L}` a.e. -/
theorem ae_eq_gibbsDensity_of_variational_eq {ρ π L : X → ℝ} {t : ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hZ : 0 < priorZ μ π L t) (hZint : Integrable (fun x ↦ Real.exp (-(t * L x)) * π x) μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hsupp : ∀ x, ρ x ≠ 0 → π x ≠ 0) (hρ1 : ∫ x, ρ x ∂μ = 1)
    (hρi : Integrable ρ μ) (hρL : Integrable (fun x ↦ ρ x * L x) μ)
    (hρπ : Integrable (fun x ↦ ρ x * Real.log (ρ x / π x)) μ)
    (heq : t * ∫ x, ρ x * L x ∂μ + relEnt μ ρ π = -Real.log (priorZ μ π L t)) :
    ρ =ᵐ[μ] gibbsDensity μ π L t := by
  have hint : Integrable (fun x ↦ ρ x * Real.log (ρ x / gibbsDensity μ π L t x)) μ := by
    refine (hρπ.add ((hρL.const_mul t).add (hρi.const_mul (Real.log (priorZ μ π L t))))).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply]
    by_cases hρ : ρ x = 0
    · simp [hρ]
    · rw [log_div_gibbsDensity hZ hρ (hsupp x hρ)]
      ring
  have hgap := gibbs_gap hZ hsupp hρ1 hρi hρL hρπ
  rw [heq] at hgap
  have h0 : relEnt μ ρ (gibbsDensity μ π L t) = 0 := by linarith
  exact ae_eq_gibbsDensity_of_relEnt_eq_zero hπ hZ hZint hρ0 hsupp hρ1 hρi hint h0

end Laplace.Multi
