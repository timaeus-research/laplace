/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSusceptibility

/-!
# The curvature of the visible information at the featureless law

Along the data path `D_s = ν.tilted (s h)` the visible information `𝓘_ν(M(s))` starts at the
featureless law with zero velocity (`hasDerivAt_genRate_dataPath_zero`), because the natural
coordinate of the featureless response is zero (`dataTheta_zero`). Its curvature there is a
variance:

* `basepointVelocity` is `θ'(0) = (Dm(0)|_𝕍)⁻¹ Cov_ν(S, h)`, and `regressor = ⟨−θ'(0), S⟩` is the
  regression of `h` on the visible statistics: `Cov_ν(⟨e, S⟩, regressor) = Cov_ν(⟨e, S⟩, h)` for
  every `e` (`lawCov_dirLoss_regressor`).
* **`hasDerivAt_deriv_genRate_dataPath_zero`**: the second derivative of `s ↦ 𝓘_ν(M(s))` at `0` is
  `Var_ν(regressor)`.
* **`regressor_variance_le`** and **`residual_variance`**: `Var_ν(regressor) ≤ Var_ν h`, with gap
  `Var_ν(h − regressor)`: infinitesimal information entering the data splits into the part visible
  through the chosen responses and the residual variance of the unexplained part.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Cov

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The covariance under a law: `Cov_ν(φ, ψ) = E φψ − Eφ Eψ`. -/
noncomputable def lawCov (φ ψ : X → ℝ) : ℝ :=
  (∫ x, φ x * ψ x ∂ν) - (∫ x, φ x ∂ν) * ∫ x, ψ x ∂ν

omit [IsProbabilityMeasure ν] in
theorem lawCov_comm (φ ψ : X → ℝ) : lawCov ν φ ψ = lawCov ν ψ φ := by
  unfold lawCov
  have e : (fun x ↦ φ x * ψ x) = fun x ↦ ψ x * φ x := funext fun x ↦ mul_comm _ _
  rw [e]
  ring

omit [IsProbabilityMeasure ν] in
theorem lawCov_neg_left (φ ψ : X → ℝ) : lawCov ν (fun x ↦ -φ x) ψ = -lawCov ν φ ψ := by
  unfold lawCov
  simp only [neg_mul, integral_neg]
  ring

/-- The variance is nonnegative. -/
theorem lawCov_self_nonneg {φ : X → ℝ} (hφ : Bdd φ) : 0 ≤ lawCov ν φ φ := by
  have hi := integrable_of_bdd_prob ν hφ
  have hi2 := integrable_of_bdd_prob ν (hφ.mul hφ)
  have key : lawCov ν φ φ = ∫ x, (φ x - ∫ y, φ y ∂ν) ^ 2 ∂ν := by
    have e : ∀ x, (φ x - ∫ y, φ y ∂ν) ^ 2 =
        φ x * φ x - (2 * ∫ y, φ y ∂ν) * φ x + (∫ y, φ y ∂ν) ^ 2 := fun x ↦ by ring
    simp_rw [e]
    have hA : Integrable (fun x ↦ φ x * φ x - (2 * ∫ y, φ y ∂ν) * φ x) ν :=
      hi2.sub (hi.const_mul _)
    rw [integral_add hA (integrable_const _), integral_sub hi2 (hi.const_mul _),
      integral_const_mul, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, lawCov]
    ring
  rw [key]
  exact integral_nonneg fun x ↦ sq_nonneg _

/-- The variance of a difference. -/
theorem lawCov_sub_self {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ) :
    lawCov ν (fun x ↦ φ x - ψ x) (fun x ↦ φ x - ψ x) =
      lawCov ν φ φ - 2 * lawCov ν φ ψ + lawCov ν ψ ψ := by
  have hφi := integrable_of_bdd_prob ν hφ
  have hψi := integrable_of_bdd_prob ν hψ
  have hφφ := integrable_of_bdd_prob ν (hφ.mul hφ)
  have hφψ := integrable_of_bdd_prob ν (hφ.mul hψ)
  have hψψ := integrable_of_bdd_prob ν (hψ.mul hψ)
  have e : ∀ x, (φ x - ψ x) * (φ x - ψ x) = φ x * φ x - 2 * (φ x * ψ x) + ψ x * ψ x :=
    fun x ↦ by ring
  unfold lawCov
  simp_rw [e]
  have hA : Integrable (fun x ↦ φ x * φ x - 2 * (φ x * ψ x)) ν := hφφ.sub (hφψ.const_mul 2)
  rw [integral_add hA hψψ, integral_sub hφφ (hφψ.const_mul 2), integral_const_mul,
    integral_sub hφi hψi]
  ring

end Cov

section Basepoint

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Nonempty J] hS in
/-- The featureless normalisation, pinned to the law. -/
theorem one_integral_pos : (0 : ℝ) < ∫ x, (fun _ : X ↦ (1 : ℝ)) x ∂ν := by simp

omit [Nonempty X] [Nonempty J] hS in
theorem tilted_zero_mul (h : X → ℝ) : ν.tilted (fun x ↦ 0 * h x) = ν := by
  simp only [zero_mul]
  rw [tilted_const' ν 0, measure_univ, inv_one, one_smul]

omit [Nonempty X] [Nonempty J] hS in
/-- The featureless covariance of the family is the covariance of the law. -/
theorem priorCov_one_zero (φ ψ : X → ℝ) :
    priorCov ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S 0) φ ψ 1 = lawCov ν φ ψ := by
  simp [priorCov, priorExp, priorZ, affLoss, lawCov]

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS in
theorem dirLoss_neg (v : J → ℝ) (x : X) : dirLoss S (-v) x = -dirLoss S v x := by
  simp only [dirLoss, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

omit [Nonempty X] [Nonempty J] in
/-- Linearity of the covariance in a visible contrast. -/
theorem lawCov_dirLoss_left (v : J → ℝ) (ψ : X → ℝ) (hψ : Bdd ψ) :
    lawCov ν (dirLoss S v) ψ = ∑ i, v i * lawCov ν (S i) ψ := by
  have h1 : ∫ x, dirLoss S v x * ψ x ∂ν = ∑ i, v i * ∫ x, S i x * ψ x ∂ν := by
    simp only [dirLoss, Finset.sum_mul]
    rw [integral_finsetSum _ fun i _ ↦
      ((integrable_of_bdd_prob ν ((hS i).mul hψ)).const_mul (v i)).congr
        (Eventually.of_forall fun x ↦ by ring)]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← integral_const_mul]; congr 1; funext x; ring
  have h2 : ∫ x, dirLoss S v x ∂ν = ∑ i, v i * ∫ x, S i x ∂ν := by
    rw [← dotJ_integral_eq ν hS v]
    rfl
  unfold lawCov
  rw [h1, h2, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
theorem dataCov_zero (h : X → ℝ) : dataCov S ν h 0 = fun i ↦ lawCov ν (S i) h := by
  funext i
  simp only [dataCov, tilted_zero_mul, lawCov]

variable {h : X → ℝ} (hh : Bdd h)
include hh

theorem pathV_zero : pathV hS ν hh 0 = 0 := by
  apply Subtype.ext
  rw [pathV_apply, tilted_zero_mul, meanMap_zero_eq_mean ν]
  simp

theorem dataTheta_zero : dataTheta hS ν hh 0 = 0 := by
  unfold dataTheta
  rw [pathV_zero]
  have h0 : chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
      (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) = 0 := by
    apply Subtype.ext
    rw [chartV_apply]
    simp
  have := chartVInv_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S)
  rwa [h0] at this

/-- **The visible information starts with zero velocity at the featureless law.** -/
theorem hasDerivAt_genRate_dataPath_zero :
    HasDerivAt (fun s ↦ (genRate ν S (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x))).toReal)
      0 0 := by
  have := hasDerivAt_genRate_dataPath hS ν hh 0
  rwa [dataTheta_zero, Submodule.coe_zero, dotJ_zero_left, neg_zero] at this

/-- **The velocity of the natural coordinates at the featureless law**:
`(Dm(0)|_𝕍)⁻¹ Cov_ν(S, h)`. -/
noncomputable def basepointVelocity : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
    hS 0).symm
    ⟨dataCov S ν h 0, dataCov_mem_dirSpan hS ν hh 0⟩

theorem hasDerivAt_dataTheta_zero :
    HasDerivAt (dataTheta hS ν hh) (basepointVelocity hS ν hh) 0 := by
  have := hasDerivAt_dataTheta hS ν hh 0
  rwa [dataTheta_zero] at this

theorem chartDeriv_basepointVelocity :
    chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS 0
        (basepointVelocity hS ν hh) =
      ⟨dataCov S ν h 0, dataCov_mem_dirSpan hS ν hh 0⟩ := by
  have hcd : ∀ w, chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS 0 w =
      chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS 0 w :=
    fun w ↦ by
      rw [← coe_chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS 0]
      rfl
  unfold basepointVelocity
  rw [← hcd]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

/-- **The regression of `h` on the visible statistics**: `⟨−θ'(0), S⟩`. -/
noncomputable def regressor : X → ℝ := dirLoss S (-(basepointVelocity hS ν hh : J → ℝ))

theorem bdd_regressor : Bdd (regressor hS ν hh) := bdd_dirLoss hS _

/-- **The regression identity**: `Cov_ν(⟨e, S⟩, regressor) = Cov_ν(⟨e, S⟩, h)` for every
direction. -/
theorem lawCov_dirLoss_regressor (e : J → ℝ) :
    lawCov ν (dirLoss S e) (regressor hS ν hh) = lawCov ν (dirLoss S e) h := by
  have h1 := congrArg (fun v : dirSpan ν (fun _ ↦ (1 : ℝ)) S ↦ dotJ e (v : J → ℝ))
    (chartDeriv_basepointVelocity hS ν hh)
  simp only at h1
  rw [dotJ_chartDeriv, Submodule.coe_zero, priorCov_one_zero, dataCov_zero] at h1
  have h2 : dotJ e (fun i ↦ lawCov ν (S i) h) = lawCov ν (dirLoss S e) h := by
    rw [lawCov_dirLoss_left hS ν e h hh]
    rfl
  rw [h2] at h1
  unfold regressor
  have h3 : lawCov ν (dirLoss S e) (dirLoss S (-(basepointVelocity hS ν hh : J → ℝ))) =
      -lawCov ν (dirLoss S e) (dirLoss S (basepointVelocity hS ν hh : J → ℝ)) := by
    rw [lawCov_comm ν (dirLoss S e), lawCov_comm ν (dirLoss S e), ← lawCov_neg_left]
    congr 1
    funext x
    exact dirLoss_neg (S := S) _ x
  rw [h3]
  exact h1

omit [Fintype J] [Nonempty J] in
/-- Differentiability of the data forcing along the path. -/
theorem hasDerivAt_dataCov (s₀ : ℝ) : ∃ K' : J → ℝ, HasDerivAt (dataCov S ν h) K' s₀ :=
  ⟨_, hasDerivAt_pi.2 fun i ↦ (hasDerivAt_integral_tilted ν hh ((hS i).mul hh) s₀).sub
    ((hasDerivAt_integral_tilted ν hh (hS i) s₀).mul (hasDerivAt_integral_tilted ν hh hh s₀))⟩

/-- **The curvature of the visible information at the featureless law is the variance of the
regression of `h` on the visible statistics.** -/
theorem hasDerivAt_rateVel_zero :
    HasDerivAt (fun s ↦ -dotJ (dataTheta hS ν hh s : J → ℝ) (dataCov S ν h s))
      (lawCov ν (regressor hS ν hh) (regressor hS ν hh)) 0 := by
  obtain ⟨K', hK⟩ := hasDerivAt_dataCov hS ν hh 0
  have hθ : HasDerivAt (fun s ↦ (dataTheta hS ν hh s : J → ℝ))
      (basepointVelocity hS ν hh : J → ℝ) 0 :=
    (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_dataTheta_zero hS ν hh)
  have hsum : HasDerivAt (fun s ↦ ∑ i, (dataTheta hS ν hh s : J → ℝ) i * dataCov S ν h s i)
      (∑ i, ((basepointVelocity hS ν hh : J → ℝ) i * dataCov S ν h 0 i +
        (dataTheta hS ν hh 0 : J → ℝ) i * K' i)) 0 := by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    have hi : HasDerivAt (fun s ↦ (dataTheta hS ν hh s : J → ℝ) i * dataCov S ν h s i)
        ((basepointVelocity hS ν hh : J → ℝ) i * dataCov S ν h 0 i +
          (dataTheta hS ν hh 0 : J → ℝ) i * K' i) 0 :=
      (hasDerivAt_pi.1 hθ i).mul (hasDerivAt_pi.1 hK i)
    exact hi
  refine hsum.neg.congr_deriv ?_
  rw [dataTheta_zero, dataCov_zero]
  simp only [Submodule.coe_zero, Pi.zero_apply, zero_mul, add_zero]
  have h1 : ∑ i, (basepointVelocity hS ν hh : J → ℝ) i * lawCov ν (S i) h =
      lawCov ν (dirLoss S (basepointVelocity hS ν hh : J → ℝ)) h :=
    (lawCov_dirLoss_left hS ν _ h hh).symm
  rw [h1]
  have h2 := lawCov_dirLoss_regressor hS ν hh (-(basepointVelocity hS ν hh : J → ℝ))
  unfold regressor at h2 ⊢
  rw [h2]
  have h3 : lawCov ν (dirLoss S (-(basepointVelocity hS ν hh : J → ℝ))) h =
      -lawCov ν (dirLoss S (basepointVelocity hS ν hh : J → ℝ)) h := by
    rw [← lawCov_neg_left]
    congr 1
    funext x
    exact dirLoss_neg (S := S) _ x
  rw [h3]

/-- **The second derivative of the visible information at the featureless law** is the variance
of the regression of `h` on the visible statistics. -/
theorem hasDerivAt_deriv_genRate_dataPath_zero :
    HasDerivAt (deriv fun s ↦
        (genRate ν S (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x))).toReal)
      (lawCov ν (regressor hS ν hh) (regressor hS ν hh)) 0 := by
  have e : (deriv fun s ↦ (genRate ν S (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x))).toReal) =
      fun s ↦ -dotJ (dataTheta hS ν hh s : J → ℝ) (dataCov S ν h s) :=
    funext fun s ↦ (hasDerivAt_genRate_dataPath hS ν hh s).deriv
  rw [e]
  exact hasDerivAt_rateVel_zero hS ν hh

/-- **The residual variance identity**: `Var_ν h − Var_ν(regressor) = Var_ν(h − regressor)`. -/
theorem residual_variance :
    lawCov ν h h - lawCov ν (regressor hS ν hh) (regressor hS ν hh) =
      lawCov ν (fun x ↦ h x - regressor hS ν hh x) (fun x ↦ h x - regressor hS ν hh x) := by
  have hg : lawCov ν (regressor hS ν hh) (regressor hS ν hh) =
      lawCov ν (regressor hS ν hh) h :=
    lawCov_dirLoss_regressor hS ν hh (-(basepointVelocity hS ν hh : J → ℝ))
  rw [lawCov_sub_self ν hh (bdd_regressor hS ν hh), hg, lawCov_comm ν h (regressor hS ν hh)]
  ring

/-- **The visible curvature is at most the variance of the data direction.** -/
theorem regressor_variance_le :
    lawCov ν (regressor hS ν hh) (regressor hS ν hh) ≤ lawCov ν h h := by
  have := lawCov_self_nonneg ν (hh.sub (bdd_regressor hS ν hh))
  rw [← residual_variance hS ν hh] at this
  linarith

end Basepoint

end Laplace.Multi
