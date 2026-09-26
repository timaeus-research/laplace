/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BasepointCurvature
import Laplace.Multi.ResponsePathDifferential

/-!
# The Fisher speed of the response path

Along the data path `ρ_t = ν.tilted(t h)` the natural coordinates of the response move with
velocity `θ'_t = C_{θ_t}⁻¹ Cov_{ρ_t}(S, h)` (`hasDerivAt_dataTheta`).  The Fisher speed squared of
the response path `t ↦ q_{m_t} = P_{θ_t}` is the variance of `⟨θ'_t, S⟩` under `P_{θ_t}`, and it
equals the pairing of the velocity with the data forcing:

  `|q'_t|_F² = Var_{P_{θ_t}}⟨θ'_t, S⟩ = −⟨θ'_t, Cov_{ρ_t}(S,h)⟩ = bᵀ C_{θ_t}⁻¹ b`
  (`responseSpeedSq_eq_neg_dotJ`),

while the data path has Fisher speed squared `Var_{ρ_t}(h)`.  In one dimension this is
`Cov_{ρ_t}(S,h)² / Var_{P_{θ_t}}(S)` (`responseSpeedSq_eq_div_of_unique`): the response path is
faster than the data path exactly when `Cov_{ρ_t}(S,h)² > Var_{ρ_t}(h) Var_{q_t}(S)`, which can
happen off the family (`ThreePointNotContracting`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Speed

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The reconstructed family `P_θ = exp(−⟨θ,S⟩) ν / Z(θ)`. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The velocity of the natural coordinates along the data path,
`θ'_t = (Dm(θ_t)|_𝕍)⁻¹ Cov_{ρ_t}(S, h)`. -/
noncomputable def dataThetaVel (t : ℝ) : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  (CDE (dataTheta hS ν hh t)).symm ⟨dataCov S ν h t, dataCov_mem_dirSpan hS ν hh t⟩

theorem hasDerivAt_dataTheta_vel (t : ℝ) :
    HasDerivAt (dataTheta hS ν hh) (dataThetaVel hS ν hh t) t :=
  hasDerivAt_dataTheta hS ν hh t

/-- The chart derivative maps the velocity to the data forcing. -/
theorem chartDeriv_dataThetaVel (t : ℝ) :
    (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
      (dataTheta hS ν hh t) (dataThetaVel hS ν hh t) : J → ℝ) = dataCov S ν h t := by
  have e : chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS (dataTheta hS ν hh t) (dataThetaVel hS ν hh t) =
      (CDE (dataTheta hS ν hh t)) (dataThetaVel hS ν hh t) := by
    rw [← coe_chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS]
    rfl
  rw [e, dataThetaVel, ContinuousLinearEquiv.apply_symm_apply]

/-- The Fisher speed squared of the response path. -/
noncomputable def responseSpeedSq (t : ℝ) : ℝ :=
  lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (dirLoss S (dataThetaVel hS ν hh t : J → ℝ))
    (dirLoss S (dataThetaVel hS ν hh t : J → ℝ))

/-- **The Fisher speed of the response path is the pairing of the velocity with the forcing**:
`|q'_t|_F² = −⟨θ'_t, Cov_{ρ_t}(S,h)⟩`. -/
theorem responseSpeedSq_eq_neg_dotJ (t : ℝ) :
    responseSpeedSq hS ν hh t = -dotJ (dataThetaVel hS ν hh t : J → ℝ) (dataCov S ν h t) := by
  have h1 := dotJ_chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (dataTheta hS ν hh t) (dataThetaVel hS ν hh t : J → ℝ)
    (dataThetaVel hS ν hh t)
  rw [chartDeriv_dataThetaVel hS ν hh t, priorCov_eq_lawCov_familyMeasure hS ν] at h1
  unfold responseSpeedSq
  linarith

/-- The family member along the data path is a probability measure. -/
theorem isProbabilityMeasure_family_dataTheta (t : ℝ) :
    IsProbabilityMeasure (Pfam (dataTheta hS ν hh t : J → ℝ)) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  exact isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) measurable_const h0 hS (t := 1) _

/-- The Fisher speed of the response path is nonnegative. -/
theorem responseSpeedSq_nonneg (t : ℝ) : 0 ≤ responseSpeedSq hS ν hh t := by
  have hP := isProbabilityMeasure_family_dataTheta hS ν hh t
  exact lawCov_self_nonneg _ (bdd_dirLoss hS _)

omit [Nonempty X] hS hh in
/-- Bilinearity of the variance under scaling. -/
theorem lawCov_const_mul_const_mul (ρ : Measure X) [IsProbabilityMeasure ρ] (a b : ℝ)
    (f : X → ℝ) :
    lawCov ρ (fun x ↦ a * f x) (fun x ↦ b * f x) = a * b * lawCov ρ f f := by
  unfold lawCov
  have e : ∀ x, a * f x * (b * f x) = a * b * (f x * f x) := fun x ↦ by ring
  simp_rw [e]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- **The one-dimensional Fisher speed of the response path**:
`|q'_t|_F² = Cov_{ρ_t}(S,h)² / Var_{P_{θ_t}}(S)`. -/
theorem responseSpeedSq_eq_div_of_unique [Unique J] (t : ℝ)
    (hvar : 0 < lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (S default) (S default)) :
    responseSpeedSq hS ν hh t =
      dataCov S ν h t default ^ 2 /
        lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (S default) (S default) := by
  have hP := isProbabilityMeasure_family_dataTheta hS ν hh t
  have hcd := chartDeriv_dataThetaVel hS ν hh t
  have h1 := dotJ_chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (dataTheta hS ν hh t) (Pi.single default 1)
    (dataThetaVel hS ν hh t)
  rw [hcd, priorCov_eq_lawCov_familyMeasure hS ν] at h1
  have hdir : ∀ w : J → ℝ, dirLoss S w = fun x ↦ w default * S default x := fun w ↦ by
    funext x
    simp [dirLoss]
  rw [hdir, hdir, lawCov_const_mul_const_mul] at h1
  simp only [dotJ, Fintype.sum_unique, Pi.single_eq_same, one_mul] at h1
  -- `dataCov = −v Var`, so `v = −dataCov/Var`
  rw [responseSpeedSq_eq_neg_dotJ]
  simp only [dotJ, Fintype.sum_unique]
  have hv : (dataThetaVel hS ν hh t : J → ℝ) default = -dataCov S ν h t default /
      lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (S default) (S default) := by
    rw [eq_div_iff hvar.ne']
    linarith
  rw [hv]
  field_simp

end Speed

end Laplace.Multi
