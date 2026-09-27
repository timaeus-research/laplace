/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovarianceFrechet
import Laplace.Multi.FaceCoercivity
import Laplace.Multi.FacetFisherAccess
import Laplace.Multi.DataRayHelpers
import Laplace.Multi.MeanSegment

/-!
# The Fisher variance form and the Fisher norm of a velocity

`fisherVar S ν θ w = Var_{P_θ}⟨w,S⟩` and `fisherNorm S ν θ w = √(fisherVar S ν θ w)`: the Riemannian
data of the response space. This module records the four facts the path API needs: joint continuity
in `(θ, w)`, nonnegativity, homogeneity `fisherNorm θ (c • w) = |c| fisherNorm θ w`, and the global
bound `fisherNorm θ w ≤ card J · B · ‖w‖` for a uniform bound `B` of the statistics; plus the
coercivity on the direction space (from `FaceCoercivity`).
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Defs

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (S : J → X → ℝ) (ν : Measure X)

/-- The Fisher variance form `G(θ,w) = Var_{P_θ}⟨w,S⟩`. -/
noncomputable def fisherVar (θ w : J → ℝ) : ℝ :=
  lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) (dirLoss S w) (dirLoss S w)

/-- The Fisher norm of the velocity `w` at `θ`: `F(θ,w) = √G(θ,w)`. -/
noncomputable def fisherNorm (θ w : J → ℝ) : ℝ := √(fisherVar S ν θ w)

theorem fisherNorm_nonneg (θ w : J → ℝ) : 0 ≤ fisherNorm S ν θ w := Real.sqrt_nonneg _

end Defs

section Basic

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

theorem fisherVar_nonneg (θ w : J → ℝ) : 0 ≤ fisherVar S ν θ w := by
  have := isProbabilityMeasure_family hS ν θ
  exact lawCov_self_nonneg _ (bdd_dirLoss hS w)

theorem fisherNorm_sq (θ w : J → ℝ) : fisherNorm S ν θ w ^ 2 = fisherVar S ν θ w :=
  Real.sq_sqrt (fisherVar_nonneg hS ν θ w)

theorem fisherVar_smul (θ w : J → ℝ) (c : ℝ) :
    fisherVar S ν θ (c • w) = c ^ 2 * fisherVar S ν θ w := by
  have := isProbabilityMeasure_family hS ν θ
  exact lawCov_dirLoss_smul_self _ c w

theorem fisherNorm_smul (θ w : J → ℝ) (c : ℝ) :
    fisherNorm S ν θ (c • w) = |c| * fisherNorm S ν θ w := by
  rw [fisherNorm, fisherVar_smul hS ν, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

theorem fisherNorm_neg (θ w : J → ℝ) : fisherNorm S ν θ (-w) = fisherNorm S ν θ w := by
  have := fisherNorm_smul hS ν θ w (-1)
  rwa [neg_one_smul, abs_neg, abs_one, one_mul] at this

theorem fisherNorm_zero (θ : J → ℝ) : fisherNorm S ν θ 0 = 0 := by
  have := fisherNorm_smul hS ν θ 0 0
  rwa [zero_smul, abs_zero, zero_mul] at this

/-- The Fisher form is minus the Jacobian of the mean map paired with the velocity. -/
theorem fisherVar_eq_neg_dotJ (θ w : J → ℝ) :
    fisherVar S ν θ w =
      -dotJ w (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ w) := by
  rw [dotJ_meanMapDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
    hS θ w w, priorCov_eq_lawCov_familyMeasure hS ν, neg_neg]
  rfl

/-- **Joint continuity of the Fisher form** in the base point and the velocity. -/
theorem continuous_fisherVar :
    Continuous fun p : (J → ℝ) × (J → ℝ) ↦ fisherVar S ν p.1 p.2 := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hD := continuous_meanMapDeriv (μ := ν) measurable_const (integrable_const 1)
    (fun _ ↦ zero_le_one) (one_integral_pos ν) measurable_const h0 hS one_pos
  have h1 : Continuous fun p : (J → ℝ) × (J → ℝ) ↦
      meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 p.1 p.2 :=
    (hD.comp continuous_fst).clm_apply continuous_snd
  have h2 : Continuous fun p : (J → ℝ) × (J → ℝ) ↦
      dotJ p.2 (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 p.1 p.2) := by
    simp only [dotJ]
    exact continuous_finsetSum _ fun i _ ↦
      ((continuous_apply i).comp continuous_snd).mul ((continuous_apply i).comp h1)
  refine h2.neg.congr fun p ↦ ?_
  rw [fisherVar_eq_neg_dotJ hS ν]
  rfl

theorem continuous_fisherNorm :
    Continuous fun p : (J → ℝ) × (J → ℝ) ↦ fisherNorm S ν p.1 p.2 :=
  (continuous_fisherVar hS ν).sqrt

/-- The Fisher norm along a continuous path with continuous velocity is continuous. -/
theorem continuous_fisherNorm_comp {γ γ' : ℝ → J → ℝ} (hγ : Continuous γ) (hγ' : Continuous γ') :
    Continuous fun t ↦ fisherNorm S ν (γ t) (γ' t) :=
  (continuous_fisherNorm hS ν).comp₂ hγ hγ'

/-- **The global bound** `F(θ,w) ≤ card J · B · ‖w‖`. -/
theorem fisherNorm_le {B : ℝ} (hB : ∀ i x, |S i x| ≤ B) (hB0 : 0 ≤ B) (θ w : J → ℝ) :
    fisherNorm S ν θ w ≤ (Fintype.card J : ℝ) * B * ‖w‖ := by
  have := isProbabilityMeasure_family hS ν θ
  refine Real.sqrt_le_iff.2 ⟨by positivity, lawCov_self_le_sq _ (bdd_dirLoss hS w) fun x ↦ ?_⟩
  refine (abs_dirLoss_le_sum_mul hB _ x).trans ?_
  rw [mul_assoc, mul_comm B, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (sum_abs_le_card_mul_norm _) hB0

theorem exists_fisherNorm_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ w : J → ℝ, fisherNorm S ν θ w ≤ K * ‖w‖ := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  exact ⟨(Fintype.card J : ℝ) * B, by positivity, fun θ w ↦ fisherNorm_le hS ν hB hB0 θ w⟩

/-- Coercivity on the direction space: `λ ‖w‖² ≤ G(θ,w)` for `w ∈ W`. -/
theorem fisherVar_coercive (θ : J → ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, lam * ‖w‖ ^ 2 ≤ fisherVar S ν θ w :=
  exists_coercive_familyMeasure hS ν θ

end Basic

end Laplace.Multi
