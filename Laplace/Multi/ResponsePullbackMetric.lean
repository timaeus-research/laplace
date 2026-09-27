/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSpeedDistortion
import Laplace.Multi.DataDissipation
import Laplace.Multi.BoundaryBlowup
import Laplace.Multi.FisherSpeedForm

/-!
# The pulled-back response metric along the data manifold

Along the data path `ρ_t ∝ e^{t h} ν` the response `θ_t = Φ(ρ_t)` has Fisher speed squared
`|θ'_t|²_F = fisherVar θ_t θ'_t = b_tᵀ C_{θ_t}⁻¹ b_t` with `b_t = Cov_{ρ_t}(S, h)` — the
pull-back of the Fisher form through the response map. This module records its exact
covariance form and the comparison with the data Fisher–Rao speed `Var_{ρ_t}(h)`:

* `|θ'_t|²_F = Cov_{ρ_t}(⟨−θ'_t, S⟩, h)` (the response speed is a covariance under the DATA
  law, between the data direction and the visible contrast that the response actually moves);
* `(|θ'_t|²_F)² ≤ Var_{ρ_t}⟨θ'_t,S⟩ · Var_{ρ_t}(h)` (Cauchy–Schwarz), i.e.
  `|θ'_t|²_F ≤ (Var_{ρ_t}⟨θ'_t,S⟩ / Var_{P_{θ_t}}⟨θ'_t,S⟩) · Var_{ρ_t}(h)`: the response speed is
  the data speed times the **distortion** of the visible contrast `⟨θ'_t,S⟩` between the data
  law and the response law;
* at a matched point (`ρ_t = P_{θ_t}`) the distortion is one and the response is a contraction,
  `|θ'_t|²_F ≤ Var_{ρ_t}(h)`.

The pulled-back metric is therefore not a contraction of the data geometry in general
(`ThreePointNotContracting`), but it is controlled by the variance distortion along the
response's own velocity, and it is a contraction exactly on the family.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Pullback

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The response speed squared is the Fisher form of the response velocity. -/
theorem responseSpeedSq_eq_fisherVar (t : ℝ) :
    responseSpeedSq hS ν hh t =
      fisherVar S ν (dataTheta hS ν hh t : J → ℝ) (dataThetaVel hS ν hh t : J → ℝ) := rfl

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hh in
/-- The forcing `b_t = Cov_{ρ_t}(S, h)` in covariance form. -/
theorem dataCov_eq_lawCov (t : ℝ) :
    dataCov S ν h t = fun i ↦ lawCov (ν.tilted fun x ↦ t * h x) (S i) h := rfl

/-- **The response speed is a covariance under the data law**:
`|θ'_t|²_F = Cov_{ρ_t}(⟨−θ'_t, S⟩, h)`. -/
theorem responseSpeedSq_eq_lawCov_data (t : ℝ) :
    responseSpeedSq hS ν hh t =
      lawCov (ν.tilted fun x ↦ t * h x) (dirLoss S (-(dataThetaVel hS ν hh t : J → ℝ))) h := by
  have := isProbabilityMeasure_dataPath' ν hh t
  rw [responseSpeedSq_eq_neg_dotJ, dataCov_eq_lawCov]
  have e : dirLoss S (-(dataThetaVel hS ν hh t : J → ℝ)) =
      fun x ↦ -dirLoss S (dataThetaVel hS ν hh t : J → ℝ) x :=
    funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [e, lawCov_neg_left, lawCov_dirLoss_left hS _ _ h hh]
  rfl

/-- **Cauchy–Schwarz for the pulled-back metric**:
`(|θ'_t|²_F)² ≤ Var_{ρ_t}⟨θ'_t, S⟩ · Var_{ρ_t}(h)`. -/
theorem responseSpeedSq_sq_le (t : ℝ) :
    responseSpeedSq hS ν hh t ^ 2 ≤
      lawCov (ν.tilted fun x ↦ t * h x) (dirLoss S (dataThetaVel hS ν hh t : J → ℝ))
          (dirLoss S (dataThetaVel hS ν hh t : J → ℝ)) *
        lawCov (ν.tilted fun x ↦ t * h x) h h := by
  have := isProbabilityMeasure_dataPath' ν hh t
  rw [responseSpeedSq_eq_lawCov_data]
  refine (lawCov_sq_le _ (bdd_dirLoss hS _) hh).trans (le_of_eq ?_)
  congr 1
  have e : dirLoss S (-(dataThetaVel hS ν hh t : J → ℝ)) =
      fun x ↦ -dirLoss S (dataThetaVel hS ν hh t : J → ℝ) x :=
    funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [e, lawCov_neg_left, lawCov_neg_right_eq, neg_neg]

/-- **The distortion bound**: where the response moves (`|θ'_t|_F > 0`),
`|θ'_t|²_F ≤ (Var_{ρ_t}⟨θ'_t,S⟩ / Var_{P_{θ_t}}⟨θ'_t,S⟩) · Var_{ρ_t}(h)`. -/
theorem responseSpeedSq_le_distortion_mul (t : ℝ) (hpos : 0 < responseSpeedSq hS ν hh t) :
    responseSpeedSq hS ν hh t ≤
      (lawCov (ν.tilted fun x ↦ t * h x) (dirLoss S (dataThetaVel hS ν hh t : J → ℝ))
          (dirLoss S (dataThetaVel hS ν hh t : J → ℝ)) / responseSpeedSq hS ν hh t) *
        lawCov (ν.tilted fun x ↦ t * h x) h h := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos, ← sq]
  exact responseSpeedSq_sq_le hS ν hh t

/-- **Contraction at a matched law**: if the data law is the response law, the response speed
is at most the data speed, `|θ'_t|²_F ≤ Var_{ρ_t}(h)`. -/
theorem responseSpeedSq_le_of_matched (t : ℝ)
    (hm : (ν.tilted fun x ↦ t * h x) = Pfam (dataTheta hS ν hh t : J → ℝ)) :
    responseSpeedSq hS ν hh t ≤ lawCov (ν.tilted fun x ↦ t * h x) h h := by
  have := isProbabilityMeasure_dataPath' ν hh t
  have hD : 0 ≤ lawCov (ν.tilted fun x ↦ t * h x) h h := lawCov_self_nonneg _ hh
  have h1 := responseSpeedSq_sq_le hS ν hh t
  have hX : lawCov (ν.tilted fun x ↦ t * h x) (dirLoss S (dataThetaVel hS ν hh t : J → ℝ))
      (dirLoss S (dataThetaVel hS ν hh t : J → ℝ)) = responseSpeedSq hS ν hh t := by
    rw [hm]
    rfl
  rw [hX] at h1
  rcases (responseSpeedSq_nonneg hS ν hh t).lt_or_eq with hpos | hzero
  · rw [sq] at h1
    exact le_of_mul_le_mul_left h1 hpos
  · rw [← hzero]
    exact hD

end Pullback

end Laplace.Multi
