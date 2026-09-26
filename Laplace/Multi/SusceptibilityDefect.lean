/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ObservableDefect
import Laplace.Multi.RegressionProjection
import Laplace.Multi.FisherVariational

/-!
# The initial susceptibility defect is the data expectation of the regression residual

At `s = 0` the derivative of the observable defect `Δ_φ(s) = E_{D_s} φ − E_{Π(M_s)} φ` along the
atlas path is

  `Δ_φ'(0) = E_D (φ − ⟨a, S⟩) − E_ν (φ − ⟨a, S⟩)`            (`hasDerivAt_observableDefect_zero`),

where `a ∈ 𝕍` is the regression coefficient of `φ` on the statistic under `ν`
(`Cov_ν(S_j, ⟨a,S⟩) = Cov_ν(S_j, φ)`). In the language of `RegressionProjection`: the first-order
response of `φ` to the data that the atlas misses is exactly the change, from `ν` to `D`, of the
expectation of the part of `φ` orthogonal to the affine span of the statistic, `(I − B₀) φ`. The
atlas captures the whole first-order response of every affine function of the statistic and
nothing of the response of the residual.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Cov

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]

omit [IsProbabilityMeasure ρ] in
theorem lawCov_neg_right_eq (g k : X → ℝ) : lawCov ρ g (fun x ↦ -k x) = -lawCov ρ g k := by
  simp only [lawCov, mul_neg, integral_neg]
  ring

theorem lawCov_sub_left_eq {f g k : X → ℝ} (hf : Bdd f) (hg : Bdd g) (hk : Bdd k) :
    lawCov ρ (fun x ↦ f x - g x) k = lawCov ρ f k - lawCov ρ g k := by
  simp only [lawCov]
  have h1 : Integrable (fun x ↦ f x * k x) ρ := integrable_of_bdd_prob ρ (hf.mul hk)
  have h2 : Integrable (fun x ↦ g x * k x) ρ := integrable_of_bdd_prob ρ (hg.mul hk)
  have e : (fun x ↦ (f x - g x) * k x) = fun x ↦ f x * k x - g x * k x := by
    funext x
    ring
  rw [e, integral_sub h1 h2,
    integral_sub (integrable_of_bdd_prob ρ hf) (integrable_of_bdd_prob ρ hg)]
  ring

end Cov

section Defect

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Nonempty J] in
/-- The regression residual is uncorrelated with every visible contrast. -/
theorem lawCov_residual_dirLoss {φ : X → ℝ} (hφ : Bdd φ) {a : J → ℝ}
    (hreg : ∀ j, lawCov ν (S j) (dirLoss S a) = lawCov ν (S j) φ) (v : J → ℝ) :
    lawCov ν (fun x ↦ φ x - dirLoss S a x) (dirLoss S v) = 0 := by
  rw [lawCov_comm, lawCov_dirLoss_left hS ν v _ (hφ.sub (bdd_dirLoss hS a))]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [lawCov_comm, lawCov_sub_left_eq ν hφ (bdd_dirLoss hS a) (hS j), lawCov_comm,
    lawCov_comm ν (dirLoss S a), hreg j, sub_self, mul_zero]

/-- **The initial susceptibility defect**: with `a ∈ 𝕍` the regression coefficient of `φ` under
`ν`, `Δ_φ'(0) = E_D(φ − ⟨a,S⟩) − E_ν(φ − ⟨a,S⟩)`. -/
theorem hasDerivAt_observableDefect_zero (D : Measure X) [IsProbabilityMeasure D]
    (hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤) {φ : X → ℝ} (hφ : Bdd φ) :
    ∃ a ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      (∀ j, lawCov ν (S j) (dirLoss S a) = lawCov ν (S j) φ) ∧
      HasDerivAt (fun s ↦ (1 - s) * (∫ x, φ x ∂ν) + s * (∫ x, φ x ∂D) -
          ∫ x, φ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
            (atlasTheta hS ν (fun i ↦ ∫ x, S i x ∂D) s))
        ((∫ x, (φ x - dirLoss S a x) ∂D) - ∫ x, (φ x - dirLoss S a x) ∂ν) 0 := by
  obtain ⟨a, ha, hreg⟩ := exists_regression_coefficient hS ν (M := fun i ↦ ∫ x, S i x ∂D) 0 hφ
  have h0 : familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν (fun i ↦ ∫ x, S i x ∂D) 0) = ν := by
    rw [atlasTheta_zero, Submodule.coe_zero, familyMeasure_one_zero]
  rw [h0] at hreg
  refine ⟨a, ha, hreg, ?_⟩
  have h := hasDerivAt_observableDefect hS ν D hfin hφ le_rfl zero_lt_one
  refine h.congr_deriv ?_
  rw [h0]
  have hres := lawCov_residual_dirLoss hS ν hφ hreg (atlasVel hS ν hfin 0 : J → ℝ)
  rw [lawCov_sub_left_eq ν hφ (bdd_dirLoss hS a) (bdd_dirLoss hS _), sub_eq_zero] at hres
  have hv := lawCov_dirLoss_neg_atlasVel hS ν hfin 0 a
  have hneg : dirLoss S (-(atlasVel hS ν hfin 0 : J → ℝ)) =
      fun x ↦ -dirLoss S (atlasVel hS ν hfin 0 : J → ℝ) x := funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [h0, hneg, lawCov_neg_right_eq] at hv
  rw [hres, neg_eq_iff_eq_neg.1 hv, (isLinearMap_dotJ a).map_sub, meanMap_zero_eq_mean ν,
    dotJ_integral_eq D hS a, dotJ_integral_eq ν hS a,
    integral_sub (integrable_of_bdd_prob D hφ) (integrable_of_bdd_prob D (bdd_dirLoss hS a)),
    integral_sub (integrable_of_bdd_prob ν hφ) (integrable_of_bdd_prob ν (bdd_dirLoss hS a))]
  ring

end Defect

end Laplace.Multi
