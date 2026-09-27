/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FaceMassConcentration
import Laplace.Multi.BoundedTiltFisherComparison
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating tilted expectations along a finite-parameter family of tilts

For bounded contrasts `h_j` and `C¹` coefficients `a : ℝ → ι → ℝ`, the data path
`ρ_t ∝ e^{g_t} ν` with `g_t = ∑_j a_j(t) h_j = ⟨a(t), h⟩` has differentiable expectations:

`d/dt E_{ρ_t} φ = Cov_{ρ_t}(φ, ġ_t)`,  `ġ_t = ⟨a'(t), h⟩`   (`hasDerivAt_integral_tilted_dirLoss`),

by dominated differentiation of `t ↦ ∫ φ e^{g_t} dν` (`hasDerivAt_integral_mul_exp_dirLoss`) and
the quotient rule. The covariances `t ↦ Cov_{ρ_t}(φ, ġ_t)` are continuous
(`continuous_lawCov_tilted_dirLoss`). This is the finite-dimensional coefficient calculus behind
the response path `t ↦ Φ(g_t)` of a journey through the data manifold.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Exp

variable {X : Type*} [MeasurableSpace X]

theorem bdd_exp_of_bdd {g : X → ℝ} (hg : Bdd g) : Bdd fun x ↦ Real.exp (g x) := by
  obtain ⟨K, hK⟩ := hg.2
  exact ⟨hg.1.exp, Real.exp K, fun x ↦ by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (abs_le.1 (hK x)).2⟩

end Exp

section Coeff

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {ι : Type*} [Fintype ι]
  (ν : Measure X) [IsProbabilityMeasure ν] {h : ι → X → ℝ} (hh : ∀ j, Bdd (h j))
  {a a' : ℝ → ι → ℝ} (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
include hh ha ha'

/-- Uniform bounds on a coefficient tilt over a ball of times. -/
theorem exists_bound_dirLoss_ball (t₀ : ℝ) :
    ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧ (∀ t ∈ Metric.ball t₀ 1, ∀ x, |dirLoss h (a t) x| ≤ K) ∧
      ∀ t ∈ Metric.ball t₀ 1, ∀ x, |dirLoss h (a' t) x| ≤ K' := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hh
  have hac : Continuous a := continuous_iff_continuousAt.2 fun t ↦ (ha t).continuousAt
  obtain ⟨Ca, hCa⟩ := (isCompact_closedBall t₀ 1).exists_bound_of_continuousOn hac.continuousOn
  obtain ⟨Ca', hCa'⟩ := (isCompact_closedBall t₀ 1).exists_bound_of_continuousOn ha'.continuousOn
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (hCa t₀ (Metric.mem_closedBall_self zero_le_one))
  have hCa'0 : 0 ≤ Ca' := (norm_nonneg _).trans (hCa' t₀ (Metric.mem_closedBall_self zero_le_one))
  have key : ∀ (b : ℝ → ι → ℝ) (C : ℝ), (∀ t ∈ Metric.closedBall t₀ 1, ‖b t‖ ≤ C) →
      ∀ t ∈ Metric.ball t₀ 1, ∀ x, |dirLoss h (b t) x| ≤ (Fintype.card ι : ℝ) * C * B := by
    intro b C hC t ht x
    calc |dirLoss h (b t) x| ≤ (∑ j, |b t j|) * B := abs_dirLoss_le_sum_mul hB _ x
      _ ≤ (∑ _j : ι, C) * B := by
          refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ ↦ ?_) hB0
          have := norm_le_pi_norm (b t) j
          rw [Real.norm_eq_abs] at this
          exact this.trans (hC t (Metric.ball_subset_closedBall ht))
      _ = (Fintype.card ι : ℝ) * C * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ⟨_, _, by positivity, by positivity, key a Ca hCa, key a' Ca' hCa'⟩

/-- **Dominated differentiation of the tilted numerator**:
`d/dt ∫ φ e^{g_t} dν = ∫ φ e^{g_t} ġ_t dν`. -/
theorem hasDerivAt_integral_mul_exp_dirLoss {φ : X → ℝ} (hφ : Bdd φ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, φ x * Real.exp (dirLoss h (a t) x) ∂ν)
      (∫ x, φ x * Real.exp (dirLoss h (a t₀) x) * dirLoss h (a' t₀) x ∂ν) t₀ := by
  obtain ⟨K, K', hK0, hK'0, hK, hK'⟩ := exists_bound_dirLoss_ball hh ha ha' t₀
  obtain ⟨Mφ, hMφ⟩ := hφ.2
  have hMφ0 : 0 ≤ Mφ := (abs_nonneg _).trans (hMφ (Classical.arbitrary X))
  have hmeasF : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun x ↦ φ x * Real.exp (dirLoss h (a t) x)) ν :=
    Eventually.of_forall fun t ↦ (hφ.1.mul (bdd_dirLoss hh (a t)).1.exp).aestronglyMeasurable
  have hint : Integrable (fun x ↦ φ x * Real.exp (dirLoss h (a t₀) x)) ν :=
    integrable_of_bdd_prob ν (hφ.mul (bdd_exp_of_bdd (bdd_dirLoss hh (a t₀))))
  have hmeasF' : AEStronglyMeasurable
      (fun x ↦ φ x * Real.exp (dirLoss h (a t₀) x) * dirLoss h (a' t₀) x) ν :=
    ((hφ.1.mul (bdd_dirLoss hh (a t₀)).1.exp).mul (bdd_dirLoss hh (a' t₀)).1).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂ν, ∀ t ∈ Metric.ball t₀ 1,
      ‖φ x * Real.exp (dirLoss h (a t) x) * dirLoss h (a' t) x‖ ≤ Mφ * Real.exp K * K' :=
    Eventually.of_forall fun x t ht ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (mul_le_mul (hMφ x) (Real.exp_le_exp.2 (abs_le.1 (hK t ht x)).2)
        (Real.exp_pos _).le hMφ0) (hK' t ht x) (abs_nonneg _) (by positivity)
  have hdiff : ∀ᵐ x ∂ν, ∀ t ∈ Metric.ball t₀ 1,
      HasDerivAt (fun t ↦ φ x * Real.exp (dirLoss h (a t) x))
        (φ x * Real.exp (dirLoss h (a t) x) * dirLoss h (a' t) x) t :=
    Eventually.of_forall fun x t _ ↦ by
      have hd : HasDerivAt (fun t ↦ dirLoss h (a t) x) (dirLoss h (a' t) x) t := by
        unfold dirLoss
        exact HasDerivAt.fun_sum fun j _ ↦ (hasDerivAt_pi.1 (ha t) j).mul_const _
      exact (hd.exp.const_mul (φ x)).congr_deriv (by ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun t x ↦ φ x * Real.exp (dirLoss h (a t) x))
    (F' := fun t x ↦ φ x * Real.exp (dirLoss h (a t) x) * dirLoss h (a' t) x)
    (bound := fun _ ↦ Mφ * Real.exp K * K') (Metric.ball_mem_nhds t₀ one_pos) hmeasF hint hmeasF'
    hbound (integrable_const _) hdiff).2

omit [Nonempty X] [IsProbabilityMeasure ν] hh ha ha' in
/-- The tilted expectation as a ratio of numerators. -/
theorem integral_tilted_dirLoss_eq_div (φ : X → ℝ) (t : ℝ) :
    ∫ x, φ x ∂ν.tilted (dirLoss h (a t)) =
      (∫ x, φ x * Real.exp (dirLoss h (a t) x) ∂ν) /
        ∫ x, (1 : ℝ) * Real.exp (dirLoss h (a t) x) ∂ν := by
  rw [integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div, one_mul]
  rw [integral_div]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)

/-- **The derivative of a tilted expectation along the coefficient path is a covariance**:
`d/dt E_{ρ_t} φ = Cov_{ρ_t}(φ, ġ_t)`. -/
theorem hasDerivAt_integral_tilted_dirLoss {φ : X → ℝ} (hφ : Bdd φ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, φ x ∂ν.tilted (dirLoss h (a t)))
      (lawCov (ν.tilted (dirLoss h (a t₀))) φ (dirLoss h (a' t₀))) t₀ := by
  have hN := hasDerivAt_integral_mul_exp_dirLoss ν hh ha ha' hφ t₀
  have hD := hasDerivAt_integral_mul_exp_dirLoss ν hh ha ha' (Bdd.const (1 : ℝ)) t₀
  have hZ : 0 < ∫ x, (1 : ℝ) * Real.exp (dirLoss h (a t₀) x) ∂ν := by
    simp only [one_mul]
    exact integral_exp_pos (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t₀)))
  have hP := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t₀)))
  refine ((hN.div hD hZ.ne').congr_of_eventuallyEq (Eventually.of_forall fun t ↦ by
    rw [Pi.div_apply]
    exact integral_tilted_dirLoss_eq_div ν φ t)).congr_deriv ?_
  rw [lawCov, integral_tilted_dirLoss_eq_div ν, integral_tilted_dirLoss_eq_div ν,
    integral_tilted_dirLoss_eq_div ν]
  have e1 : ∫ x, φ x * dirLoss h (a' t₀) x * Real.exp (dirLoss h (a t₀) x) ∂ν =
      ∫ x, φ x * Real.exp (dirLoss h (a t₀) x) * dirLoss h (a' t₀) x ∂ν :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have e2 : ∫ x, dirLoss h (a' t₀) x * Real.exp (dirLoss h (a t₀) x) ∂ν =
      ∫ x, (1 : ℝ) * Real.exp (dirLoss h (a t₀) x) * dirLoss h (a' t₀) x ∂ν :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [e1, e2]
  field_simp

/-- Tilted expectations are continuous along the coefficient path. -/
theorem continuous_integral_tilted_dirLoss {φ : X → ℝ} (hφ : Bdd φ) :
    Continuous fun t ↦ ∫ x, φ x ∂ν.tilted (dirLoss h (a t)) :=
  continuous_iff_continuousAt.2 fun t ↦
    (hasDerivAt_integral_tilted_dirLoss ν hh ha ha' hφ t).continuousAt

/-- **The forcing covariances are continuous along the coefficient path**:
`t ↦ Cov_{ρ_t}(φ, ġ_t)` is continuous. -/
theorem continuous_lawCov_tilted_dirLoss {φ : X → ℝ} (hφ : Bdd φ) :
    Continuous fun t ↦ lawCov (ν.tilted (dirLoss h (a t))) φ (dirLoss h (a' t)) := by
  have e : ∀ t, lawCov (ν.tilted (dirLoss h (a t))) φ (dirLoss h (a' t)) =
      (∑ j, a' t j * ∫ x, φ x * h j x ∂ν.tilted (dirLoss h (a t))) -
        (∫ x, φ x ∂ν.tilted (dirLoss h (a t))) *
          ∑ j, a' t j * ∫ x, h j x ∂ν.tilted (dirLoss h (a t)) := fun t ↦ by
    have hP := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (bdd_dirLoss hh (a t)))
    rw [lawCov]
    congr 1
    · have : (fun x ↦ φ x * dirLoss h (a' t) x) = fun x ↦ ∑ j, a' t j * (φ x * h j x) := by
        funext x
        simp only [dirLoss, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      rw [this, integral_finsetSum _ fun j _ ↦
        (integrable_of_bdd_prob _ (hφ.mul (hh j))).const_mul _]
      exact Finset.sum_congr rfl fun j _ ↦ integral_const_mul _ _
    · congr 1
      have : (fun x ↦ dirLoss h (a' t) x) = fun x ↦ ∑ j, a' t j * h j x := funext fun x ↦ rfl
      rw [this, integral_finsetSum _ fun j _ ↦ (integrable_of_bdd_prob _ (hh j)).const_mul _]
      exact Finset.sum_congr rfl fun j _ ↦ integral_const_mul _ _
  have hfun : (fun t ↦ lawCov (ν.tilted (dirLoss h (a t))) φ (dirLoss h (a' t))) =
      fun t ↦ (∑ j, a' t j * ∫ x, φ x * h j x ∂ν.tilted (dirLoss h (a t))) -
        (∫ x, φ x ∂ν.tilted (dirLoss h (a t))) *
          ∑ j, a' t j * ∫ x, h j x ∂ν.tilted (dirLoss h (a t)) := funext e
  rw [hfun]
  refine (continuous_finsetSum _ fun j _ ↦ ((continuous_apply j).comp ha').mul
    (continuous_integral_tilted_dirLoss ν hh ha ha' (hφ.mul (hh j)))).sub
    ((continuous_integral_tilted_dirLoss ν hh ha ha' hφ).mul
      (continuous_finsetSum _ fun j _ ↦ ((continuous_apply j).comp ha').mul
        (continuous_integral_tilted_dirLoss ν hh ha ha' (hh j))))

end Coeff

end Laplace.Multi
