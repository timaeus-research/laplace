/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherPathLength
import Laplace.Multi.MeanMapChart
import Laplace.Multi.BoundaryBlowup

/-!
# The mean map is controlled by the Fisher length

Along a `C¹` path `γ` in parameter space, `d/dt m_j(γ_t) = −Cov_{P_{γ_t}}(S_j, ⟨γ'_t,S⟩)`, and
Cauchy–Schwarz for covariances gives `|d/dt m_j(γ_t)| ≤ B F(γ_t,γ'_t)` for a uniform bound `B` of
the statistics. Hence (sup norm on `J → ℝ`)
`‖m(γ_b) − m(γ_a)‖ ≤ B ∫_a^b F(γ_t,γ'_t) dt`: **the mean displacement is at most `B` times the
Fisher length**, on every subinterval.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section MeanControl

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The Jacobian of the mean map. -/
local notation "Dmean" => meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- A coordinate of the Jacobian is minus a covariance. -/
theorem meanMapDeriv_apply_eq_neg_lawCov (θ w : J → ℝ) (i : J) :
    Dmean θ w i = -lawCov (Pfam θ) (S i) (dirLoss S w) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  obtain ⟨M, h⟩ := tiltData_aff measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
    (one_integral_pos ν) measurable_const h0 hS θ w 1
  have hZ : priorZ ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 ≠ 0 := h.ν_pos.ne'
  rw [meanMapDeriv_apply measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
    measurable_const h0 hS one_pos hZ w i, priorCov_eq_lawCov_familyMeasure hS ν]
  ring

/-- **Cauchy–Schwarz for the mean's velocity**: `|d m_i| ≤ B F(θ,w)`. -/
theorem abs_meanMapDeriv_le {B : ℝ} (hB : ∀ i x, |S i x| ≤ B) (hB0 : 0 ≤ B) (θ w : J → ℝ)
    (i : J) : |Dmean θ w i| ≤ B * fisherNorm S ν θ w := by
  have hP := isProbabilityMeasure_family hS ν θ
  rw [meanMapDeriv_apply_eq_neg_lawCov hS ν, abs_neg]
  have h1 := lawCov_sq_le (Pfam θ) (hS i) (bdd_dirLoss hS w)
  have h2 : lawCov (Pfam θ) (S i) (S i) ≤ B ^ 2 := lawCov_self_le_sq _ (hS i) (hB i)
  calc |lawCov (Pfam θ) (S i) (dirLoss S w)|
      ≤ √(lawCov (Pfam θ) (S i) (S i) * lawCov (Pfam θ) (dirLoss S w) (dirLoss S w)) :=
        Real.abs_le_sqrt h1
    _ ≤ √(B ^ 2 * lawCov (Pfam θ) (dirLoss S w) (dirLoss S w)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h2 (fisherVar_nonneg hS ν θ w))
    _ = B * fisherNorm S ν θ w := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB0]
        rfl

/-- The mean map along a `C¹` path is differentiable with velocity `Dm(γ_t) γ'_t`. -/
theorem hasDerivAt_meanMap_comp {γ γ' : ℝ → J → ℝ} {t : ℝ} (hγ : HasDerivAt γ (γ' t) t) :
    HasDerivAt (fun s ↦ mean (γ s)) (Dmean (γ t) (γ' t)) t := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  exact (hasStrictFDerivAt_meanMap measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
    (one_integral_pos ν) measurable_const h0 hS one_pos (γ t)).hasFDerivAt.comp_hasDerivAt t hγ

/-- **The mean displacement of a coordinate is at most `B` times the Fisher length.** -/
theorem abs_meanMap_sub_le_integral {γ γ' : ℝ → J → ℝ} (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hγ' : Continuous γ') {B : ℝ} (hB : ∀ i x, |S i x| ≤ B) (hB0 : 0 ≤ B) {a b : ℝ}
    (hab : a ≤ b) (i : J) :
    |mean (γ b) i - mean (γ a) i| ≤ B * ∫ t in a..b, fisherNorm S ν (γ t) (γ' t) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t ↦ (hγ t).continuousAt
  have hd : ∀ t, HasDerivAt (fun s ↦ mean (γ s) i) (Dmean (γ t) (γ' t) i) t := fun t ↦
    hasDerivAt_pi.1 (hasDerivAt_meanMap_comp hS ν (hγ t)) i
  have hD := continuous_meanMapDeriv (μ := ν) measurable_const (integrable_const 1)
    (fun _ ↦ zero_le_one) (one_integral_pos ν) measurable_const h0 hS one_pos
  have hcont : Continuous fun t ↦ Dmean (γ t) (γ' t) i :=
    (continuous_apply i).comp ((hD.comp hγc).clm_apply hγ')
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (hcont.intervalIntegrable _ _)]
  calc |∫ t in a..b, Dmean (γ t) (γ' t) i| ≤ ∫ t in a..b, |Dmean (γ t) (γ' t) i| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, B * fisherNorm S ν (γ t) (γ' t) :=
        intervalIntegral.integral_mono_on hab (hcont.abs.intervalIntegrable _ _)
          ((continuous_const.mul (continuous_fisherNorm_comp hS ν hγc hγ')).intervalIntegrable _ _)
          fun t _ ↦ abs_meanMapDeriv_le hS ν hB hB0 _ _ i
    _ = B * ∫ t in a..b, fisherNorm S ν (γ t) (γ' t) := intervalIntegral.integral_const_mul _ _

/-- **The mean displacement is at most `B` times the Fisher length** (sup norm). -/
theorem norm_meanMap_sub_le_integral {γ γ' : ℝ → J → ℝ} (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hγ' : Continuous γ') {B : ℝ} (hB : ∀ i x, |S i x| ≤ B) (hB0 : 0 ≤ B) {a b : ℝ}
    (hab : a ≤ b) :
    ‖mean (γ b) - mean (γ a)‖ ≤ B * ∫ t in a..b, fisherNorm S ν (γ t) (γ' t) := by
  have hI : 0 ≤ ∫ t in a..b, fisherNorm S ν (γ t) (γ' t) :=
    intervalIntegral.integral_nonneg hab fun t _ ↦ fisherNorm_nonneg S ν _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_meanMap_sub_le_integral hS ν hγ hγ' hB hB0 hab i

omit [Nonempty X] hS [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- A `FisherPath` is a `C¹` path in the ambient space. -/
theorem FisherPath.hasDerivAt_coe {x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S} (p : FisherPath S ν x y)
    (t : ℝ) : HasDerivAt (fun s ↦ (p.toFun s : J → ℝ)) (p.vel t : J → ℝ) t :=
  (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt t (p.hasDerivAt t)

/-- **The mean displacement along a Fisher path is at most `B` times its length.** -/
theorem norm_meanMap_sub_le_length {x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S} (p : FisherPath S ν x y)
    {B : ℝ} (hB : ∀ i x, |S i x| ≤ B) (hB0 : 0 ≤ B) :
    ‖mean (y : J → ℝ) - mean (x : J → ℝ)‖ ≤ B * p.length := by
  have h := norm_meanMap_sub_le_integral hS ν (γ := fun s ↦ (p.toFun s : J → ℝ))
    (γ' := fun s ↦ (p.vel s : J → ℝ)) (p.hasDerivAt_coe ν)
    (continuous_subtype_val.comp p.continuous_vel) hB hB0 zero_le_one
  rwa [p.source, p.target] at h

end MeanControl

end Laplace.Multi
