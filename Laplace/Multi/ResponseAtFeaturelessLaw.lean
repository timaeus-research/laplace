/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSpeedDistortion
import Laplace.Multi.SusceptibilityDefect
import Laplace.Multi.FiniteResponse
import Laplace.Multi.FisherSpeedForm
import Laplace.Multi.NormalCone

/-!
# The response at the featureless law is Fisher-orthogonal projection

At `t = 0` the data path `ρ_t ∝ e^{t h} ν` starts at the featureless law `ν = P_0`, and the
response velocity is `θ'_0 = −C⁻¹ b` with `C = Cov_ν(S)`, `b = Cov_ν(S, h)`. Its Fisher norm
squared `|θ'_0|²_F = bᵀ C⁻¹ b` is the variance of the regressor `⟨−θ'_0, S⟩`, the
`L²(ν)`-orthogonal projection of `h − E_ν h` onto the centred sufficient statistics, and

`Var_ν h = |θ'_0|²_F + ‖h − E_ν h − h_resp‖²_{L²(ν)}`.

**At the featureless end, response is exactly Fisher-orthogonal projection**: the response
speed is the visible part of the data speed, the residual is invisible to the family, and the
regressor is the best visible approximation of the data direction. Expansion (response faster
than data) can emerge only away from the matched base law.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Featureless

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The response velocity at `t = 0` is the basepoint velocity `−C⁻¹ b`. -/
theorem dataThetaVel_zero : dataThetaVel hS ν hh 0 = basepointVelocity hS ν hh :=
  (hasDerivAt_dataTheta_vel hS ν hh 0).unique (hasDerivAt_dataTheta_zero hS ν hh)

/-- The response law at `t = 0` is the featureless law. -/
theorem familyMeasure_dataTheta_zero : Pfam (dataTheta hS ν hh 0 : J → ℝ) = ν := by
  rw [dataTheta_zero, Submodule.coe_zero]
  exact familyMeasure_zero_eq hS ν

/-- **The response speed at the featureless law is the variance of the regressor**
`⟨−θ'_0, S⟩`. -/
theorem responseSpeedSq_zero :
    responseSpeedSq hS ν hh 0 = lawCov ν (regressor hS ν hh) (regressor hS ν hh) := by
  unfold responseSpeedSq regressor
  rw [familyMeasure_dataTheta_zero, dataThetaVel_zero]
  have e : dirLoss S (-(basepointVelocity hS ν hh : J → ℝ)) =
      fun x ↦ -dirLoss S (basepointVelocity hS ν hh : J → ℝ) x :=
    funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [e, lawCov_neg_left, lawCov_neg_right_eq, neg_neg]

/-- The response speed at the featureless law is the Fisher norm squared of `θ'_0` at `0`. -/
theorem responseSpeedSq_zero_eq_fisherVar :
    responseSpeedSq hS ν hh 0 = fisherVar S ν 0 (basepointVelocity hS ν hh : J → ℝ) := by
  unfold responseSpeedSq fisherVar
  rw [familyMeasure_dataTheta_zero, dataThetaVel_zero, familyMeasure_zero_eq hS ν]

/-- **The featureless Pythagoras identity**:
`Var_ν h = |θ'_0|²_F + Var_ν(h − regressor)`. -/
theorem lawCov_self_eq_responseSpeedSq_zero_add :
    lawCov ν h h = responseSpeedSq hS ν hh 0 +
      lawCov ν (fun x ↦ h x - regressor hS ν hh x) (fun x ↦ h x - regressor hS ν hh x) := by
  rw [responseSpeedSq_zero, ← residual_variance hS ν hh]
  ring

/-- **The residual is invisible**: `Cov_ν(h − regressor, ⟨e, S⟩) = 0` for every direction. -/
theorem lawCov_residual_dirLoss_zero (e : J → ℝ) :
    lawCov ν (fun x ↦ h x - regressor hS ν hh x) (dirLoss S e) = 0 := by
  rw [lawCov_sub_left_eq ν hh (bdd_regressor hS ν hh) (bdd_dirLoss hS e), lawCov_comm,
    lawCov_comm ν (regressor hS ν hh), lawCov_dirLoss_regressor hS ν hh e, sub_self]

/-- **The regressor is the best visible approximation**: for every direction `e`,
`Var_ν(h − ⟨e,S⟩) = Var_ν(h − regressor) + Var_ν(regressor − ⟨e,S⟩)`. -/
theorem lawCov_sub_dirLoss_self_eq (e : J → ℝ) :
    lawCov ν (fun x ↦ h x - dirLoss S e x) (fun x ↦ h x - dirLoss S e x) =
      lawCov ν (fun x ↦ h x - regressor hS ν hh x) (fun x ↦ h x - regressor hS ν hh x) +
        lawCov ν (fun x ↦ regressor hS ν hh x - dirLoss S e x)
          (fun x ↦ regressor hS ν hh x - dirLoss S e x) := by
  have hr := bdd_regressor hS ν hh
  have hd := bdd_dirLoss hS e
  have e1 : (fun x ↦ h x - dirLoss S e x) =
      fun x ↦ (h x - regressor hS ν hh x) + (regressor hS ν hh x - dirLoss S e x) :=
    funext fun x ↦ by ring
  have e2 : (fun x ↦ regressor hS ν hh x - dirLoss S e x) =
      dirLoss S (-(basepointVelocity hS ν hh : J → ℝ) - e) :=
    funext fun x ↦ (dirLoss_sub' (S := S) _ _ x).symm
  have hcross : lawCov ν (fun x ↦ h x - regressor hS ν hh x)
      (fun x ↦ regressor hS ν hh x - dirLoss S e x) = 0 := by
    rw [e2]
    exact lawCov_residual_dirLoss_zero hS ν hh _
  rw [e1, lawCov_add_self ν (hh.sub hr) (hr.sub hd), hcross]
  ring

/-- The regressor minimises the residual variance among all visible directions. -/
theorem lawCov_residual_le (e : J → ℝ) :
    lawCov ν (fun x ↦ h x - regressor hS ν hh x) (fun x ↦ h x - regressor hS ν hh x) ≤
      lawCov ν (fun x ↦ h x - dirLoss S e x) (fun x ↦ h x - dirLoss S e x) := by
  rw [lawCov_sub_dirLoss_self_eq hS ν hh e]
  linarith [lawCov_self_nonneg ν ((bdd_regressor hS ν hh).sub (bdd_dirLoss hS e))]

/-- **Response speed is at most data speed at the featureless law**, with equality iff the data
direction is visible (`h − regressor` has zero variance). -/
theorem responseSpeedSq_zero_le : responseSpeedSq hS ν hh 0 ≤ lawCov ν h h := by
  rw [responseSpeedSq_zero]
  exact regressor_variance_le hS ν hh

theorem responseSpeedSq_zero_eq_iff :
    responseSpeedSq hS ν hh 0 = lawCov ν h h ↔
      lawCov ν (fun x ↦ h x - regressor hS ν hh x) (fun x ↦ h x - regressor hS ν hh x) = 0 := by
  rw [lawCov_self_eq_responseSpeedSq_zero_add hS ν hh]
  constructor
  · intro h1
    linarith
  · intro h1
    rw [h1, add_zero]

end Featureless

end Laplace.Multi
