/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DataRayFacet

/-!
# Scalar block identities along the data path near a facet

With the linear depth velocity `r'_t = −⟨θ'_t, u⟩/⟨u,u⟩` and the tangential velocity
`v'_t = θ'_t + r'_t u`, the response velocity satisfies `θ'_t = v'_t − r'_t u`, and pairing the
equation `Dm(θ_t) θ'_t = Cov_{ρ_t}(S,h)` with `u` and with `v'_t` gives the two scalar block
identities

  `r'_t V_t = ⟨u, Cov_{ρ_t}(S,h)⟩ + c_t`,   `Var_{q_t}⟨v'_t,S⟩ = −⟨v'_t, Cov_{ρ_t}(S,h)⟩ + r'_t c_t`

with `V_t = Var_{q_t}⟨u,S⟩` and `c_t = Cov_{q_t}(⟨u,S⟩, ⟨v'_t,S⟩)` (`depthVel_mul_var_eq`,
`var_tangentVel_eq`). On the data side the slack mean `a_t = E_{ρ_t}(β − ⟨u,S⟩)` has derivative
`a'_t = −⟨u, Cov_{ρ_t}(S,h)⟩ = Cov_{ρ_t}(ℓ, h)` and, since `ℓ, H − h ≥ 0`,
`a'_t ≤ a_t E_{ρ_t}(H − h)` (`slackMeanVel_le`): the slack mean cannot grow faster than the
dissipation allows. These are
the only structural identities the reverse data-ray theorem needs; no inverse operator appears.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Blocks

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h) (u : J → ℝ) (β : ℝ)
include hS hh

local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

variable (S) in
/-- The data-side slack mean `a_t = E_{ρ_t}(β − ⟨u,S⟩)`. -/
noncomputable def slackMean (μ : Measure X) (g : X → ℝ) (w : J → ℝ) (β₀ t : ℝ) : ℝ :=
  ∫ x, (β₀ - dirLoss S w x) ∂μ.tilted (fun x ↦ t * g x)

omit [Nonempty X] [Nonempty J] hS hh in
theorem integral_dirLoss_eq_dotJ (ρ : Measure X) [IsProbabilityMeasure ρ] (hSb : ∀ j, Bdd (S j)) :
    ∫ x, dirLoss S u x ∂ρ = dotJ u fun i ↦ ∫ x, S i x ∂ρ := by
  simp only [dirLoss, dotJ]
  rw [integral_finsetSum _ fun i _ ↦ (integrable_of_bdd_prob ρ (hSb i)).const_mul (u i)]
  exact Finset.sum_congr rfl fun i _ ↦ integral_const_mul _ _

omit [Nonempty X] [Nonempty J] in
/-- The slack mean in terms of the data means. -/
theorem slackMean_eq (t : ℝ) :
    slackMean S ν h u β t = β - dotJ u fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ t * h x) := by
  have := isProbabilityMeasure_dataPath' ν hh t
  rw [slackMean, integral_sub (integrable_const _) (integrable_of_bdd_prob _ (bdd_dirLoss hS u)),
    integral_const, integral_dirLoss_eq_dotJ u _ hS]
  simp

/-- The model-side slack mean agrees with the data-side one. -/
theorem integral_slack_family_eq (t : ℝ) :
    ∫ x, (β - dirLoss S u x) ∂Pfam (dataTheta hS ν hh t : J → ℝ) = slackMean S ν h u β t := by
  have hP := isProbabilityMeasure_family_dataTheta hS ν hh t
  rw [slackMean_eq hS ν hh u β t, integral_sub (integrable_const _)
    (integrable_of_bdd_prob _ (bdd_dirLoss hS u)), integral_const, integral_dirLoss_eq_dotJ u _ hS,
    ← meanMap_dataTheta hS ν hh t, mean_familyMeasure_one_zero hS ν]
  simp

omit [Nonempty J] in
/-- **The slack mean has derivative `−⟨u, Cov_{ρ_t}(S,h)⟩`.** -/
theorem hasDerivAt_slackMean (t : ℝ) :
    HasDerivAt (slackMean S ν h u β) (-dotJ u (dataCov S ν h t)) t := by
  have e : slackMean S ν h u β = fun s ↦ β - ∑ i, u i * ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x) := by
    funext s
    rw [slackMean_eq hS ν hh u β s]
    rfl
  rw [e]
  have hsum : HasDerivAt (fun s ↦ ∑ i, u i * ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x))
      (∑ i, u i * dataCov S ν h t i) t :=
    HasDerivAt.fun_sum fun i _ ↦ (hasDerivAt_integral_dataPath ν hS hh i t).const_mul (u i)
  exact hsum.const_sub β

omit [Nonempty X] [Nonempty J] in
/-- `⟨u, Cov_{ρ_t}(S,h)⟩ = Cov_{ρ_t}(⟨u,S⟩, h)`. -/
theorem dotJ_dataCov_eq_lawCov (t : ℝ) :
    dotJ u (dataCov S ν h t) = lawCov (ν.tilted fun x ↦ t * h x) (dirLoss S u) h := by
  have := isProbabilityMeasure_dataPath' ν hh t
  rw [lawCov_dirLoss_left hS _ u h hh]
  rfl

variable {H : ℝ} (hH : ∀ x, h x ≤ H)
include hH

omit [Nonempty X] [Nonempty J] in
/-- **The slack mean grows at most at the dissipation rate**:
`a'_t = −⟨u, Cov_{ρ_t}(S,h)⟩ ≤ a_t E_{ρ_t}(H − h)`. -/
theorem slackMeanVel_le (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) (t : ℝ) :
    -dotJ u (dataCov S ν h t) ≤
      slackMean S ν h u β t * ∫ x, (H - h x) ∂ν.tilted (fun x ↦ t * h x) := by
  have hP := isProbabilityMeasure_dataPath' ν hh t
  set ρ := ν.tilted fun x ↦ t * h x with hρ
  have hℓ : Bdd fun x ↦ β - dirLoss S u x := (Bdd.const β).sub (bdd_dirLoss hS u)
  have hd : Bdd fun x ↦ H - h x := (Bdd.const H).sub hh
  -- a' = Cov(ℓ, h) = −Cov(ℓ, H − h)
  have e1 : -dotJ u (dataCov S ν h t) = lawCov ρ (fun x ↦ β - dirLoss S u x) h := by
    rw [dotJ_dataCov_eq_lawCov hS ν hh u t,
      lawCov_sub_left_eq ρ (Bdd.const β) (bdd_dirLoss hS u) hh, lawCov_const_left_eq_zero]
    ring
  have e2 : lawCov ρ (fun x ↦ β - dirLoss S u x) h =
      -lawCov ρ (fun x ↦ β - dirLoss S u x) (fun x ↦ H - h x) := by
    rw [lawCov_const_sub_right ρ hℓ hh, neg_neg]
  -- the product `ℓ d` has nonnegative mean
  have hac : ρ ≪ ν := by
    rw [hρ, Measure.tilted]
    exact withDensity_absolutelyContinuous _ _
  have hprod : 0 ≤ ∫ x, (β - dirLoss S u x) * (H - h x) ∂ρ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hac.ae_le hβ] with x hx
    exact mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 (hH x))
  rw [e1, e2, lawCov, slackMean]
  linarith

end Blocks

section Facet

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h) (u : J → ℝ)
include hS hh

local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The depth velocity `r'_t = −⟨θ'_t, u⟩/⟨u,u⟩`. -/
noncomputable def depthVel (t : ℝ) : ℝ := -dotJ (dataThetaVel hS ν hh t : J → ℝ) u / dotJ u u

/-- The tangential velocity `v'_t = θ'_t + r'_t u`. -/
noncomputable def tangentVel (t : ℝ) : J → ℝ :=
  (dataThetaVel hS ν hh t : J → ℝ) + depthVel hS ν hh u t • u

theorem coe_dataThetaVel_eq_tangentVel_sub (t : ℝ) :
    (dataThetaVel hS ν hh t : J → ℝ) = tangentVel hS ν hh u t - depthVel hS ν hh u t • u := by
  rw [tangentVel, add_sub_cancel_right]

theorem dotJ_tangentVel_u (hu : dotJ u u ≠ 0) (t : ℝ) : dotJ (tangentVel hS ν hh u t) u = 0 := by
  rw [tangentVel, dotJ_comm', (isLinearMap_dotJ u).map_add, (isLinearMap_dotJ u).map_smul,
    smul_eq_mul, dotJ_comm' u, depthVel]
  field_simp
  ring

omit [Nonempty X] [Nonempty J] hh in
/-- The bilinear covariance of visible contrasts. -/
theorem lawCov_dirLoss_sub_smul (ρ : Measure X) [IsProbabilityMeasure ρ] (e w : J → ℝ) (c : ℝ) :
    lawCov ρ (dirLoss S e) (dirLoss S (w - c • u)) =
      lawCov ρ (dirLoss S e) (dirLoss S w) - c * lawCov ρ (dirLoss S e) (dirLoss S u) := by
  have e1 : dirLoss S (w - c • u) = fun x ↦ dirLoss S w x - c * dirLoss S u x := by
    funext x
    rw [dirLoss_sub', dirLoss_smul]
  rw [e1, lawCov_comm, lawCov_sub_left_eq ρ (bdd_dirLoss hS w) (Bdd.const_mul c (bdd_dirLoss hS u))
    (bdd_dirLoss hS e), lawCov_const_mul_left', lawCov_comm, lawCov_comm ρ (fun x ↦ dirLoss S u x)]

/-- **The first block identity**: `r'_t V_t = ⟨u, Cov_{ρ_t}(S,h)⟩ + c_t`. -/
theorem depthVel_mul_var_eq (t : ℝ) :
    depthVel hS ν hh u t *
        lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (dirLoss S u) (dirLoss S u) =
      dotJ u (dataCov S ν h t) +
        lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (dirLoss S u)
          (dirLoss S (tangentVel hS ν hh u t)) := by
  have hP := isProbabilityMeasure_family_dataTheta hS ν hh t
  have h1 := dotJ_chartDeriv_eq_neg_lawCov hS ν (dataTheta hS ν hh t) u (dataThetaVel hS ν hh t)
  rw [chartDeriv_dataThetaVel hS ν hh t, coe_dataThetaVel_eq_tangentVel_sub hS ν hh u t,
    lawCov_dirLoss_sub_smul hS u] at h1
  rw [h1]
  ring

/-- **The second block identity**: `Var_{q_t}⟨v'_t,S⟩ = −⟨v'_t, Cov_{ρ_t}(S,h)⟩ + r'_t c_t`. -/
theorem var_tangentVel_eq (t : ℝ) :
    lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (dirLoss S (tangentVel hS ν hh u t))
        (dirLoss S (tangentVel hS ν hh u t)) =
      -dotJ (tangentVel hS ν hh u t) (dataCov S ν h t) +
        depthVel hS ν hh u t * lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (dirLoss S u)
          (dirLoss S (tangentVel hS ν hh u t)) := by
  have hP := isProbabilityMeasure_family_dataTheta hS ν hh t
  have h1 := dotJ_chartDeriv_eq_neg_lawCov hS ν (dataTheta hS ν hh t) (tangentVel hS ν hh u t)
    (dataThetaVel hS ν hh t)
  rw [chartDeriv_dataThetaVel hS ν hh t, coe_dataThetaVel_eq_tangentVel_sub hS ν hh u t,
    lawCov_dirLoss_sub_smul hS u] at h1
  rw [h1, lawCov_comm _ (dirLoss S u)]
  ring

end Facet

end Laplace.Multi
