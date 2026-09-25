/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SliceChart

/-!
# The loss surface over the feature space

Over the interior of the moment body of the features, `h(t, M) = ⟨L₀⟩` at the unique point of the
temperature-`t` slice with feature response `M` (this is `obsMean L₀ t M`). Its temperature
derivative at fixed feature response is minus the variance of the loss unexplained by the features,

  `∂_t h(t, M) = −Var(L₀ − ∑ₖ bₖ Rₖ)`,   `C b = c`   (`hasDerivAt_lossSurface`),

where `C = Cov(R, R)` and `c = Cov(R, L₀)` under the posterior at `(t, M)`; more generally for any
bounded observable `∂_t ⟨φ⟩|_M = −(Cov(φ, L₀) − ∑ₖ bₖ Cov(φ, Rₖ))` (`hasDerivAt_obsMean_temp`):
fixed-feature annealing responds only to the component of the loss orthogonal to the features.
Consequently `h` is nonincreasing in `t` (`lossSurface_antitoneOn`). In the feature directions the
gradient of any observable's surface is the vector of its regression coefficients on the features
(`obsMean_fderiv_eq_regression`): `D_M ⟨φ⟩ [d] = ∑ₖ bₖ dₖ` with `C b = Cov(R, φ)`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

omit [MeasurableSpace X] in
theorem dirLoss_pi_single [DecidableEq ι] (R : ι → X → ℝ) (k : ι) :
    dirLoss R (Pi.single k 1) = R k := by
  funext x
  simp [dirLoss, Pi.single_apply]

omit [MeasurableSpace X] in
theorem dirLoss_jointStat_single_some [DecidableEq ι] (L₀ : X → ℝ) (R : ι → X → ℝ) (k : ι) :
    dirLoss (jointStat L₀ R) (Pi.single (some k) 1) = R k := by
  funext x
  simp [dirLoss, Pi.single_apply, jointStat]

omit [MeasurableSpace X] in
theorem dirLoss_jointStat_single_none [DecidableEq ι] (L₀ : X → ℝ) (R : ι → X → ℝ) :
    dirLoss (jointStat L₀ R) (Pi.single none 1) = L₀ := by
  funext x
  simp [dirLoss, Pi.single_apply, jointStat]

/-- The covariance matrix of the features under `P_a`. -/
noncomputable def featCov (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) :
    Matrix ι ι ℝ :=
  Matrix.of fun k l ↦ priorCov μ π (affLoss L₀ R a) (R k) (R l) t

/-- The covariances of the features with an observable under `P_a`. -/
noncomputable def featObsCov (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ)
    (φ : X → ℝ) : ι → ℝ :=
  fun k ↦ priorCov μ π (affLoss L₀ R a) (R k) φ t

omit [MeasurableSpace X] in
theorem sum_smul_single_eq [DecidableEq ι] (b : ι → ℝ) :
    ∑ k, b k • (Pi.single k 1 : ι → ℝ) = b := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem featCov_eq_covMat [DecidableEq ι] (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) :
    featCov μ π L₀ R t a = covMat μ π L₀ R t a fun k ↦ Pi.single k 1 := by
  ext k l
  simp [featCov, covMat, dirLoss_pi_single]

theorem featObsCov_eq_covVec [DecidableEq ι] (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ)
    (φ : X → ℝ) :
    featObsCov μ π L₀ R t a φ = covVec μ π L₀ R t a (fun k ↦ Pi.single k 1) φ := by
  funext k
  simp [featObsCov, covVec, dirLoss_pi_single]

/-- The feature covariance in the joint family at `Θ(t, a)` is the feature covariance at
`(t, a)`. -/
theorem covMat_joint_eq [DecidableEq ι] (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) :
    covMat μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a)
        (fun k ↦ Pi.single (some k) 1) = featCov μ π L₀ R t a := by
  ext k l
  simp [covMat, featCov, dirLoss_jointStat_single_some, priorCov_natCoord]

theorem covVec_joint_eq [DecidableEq ι] (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) :
    covVec μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) (fun k ↦ Pi.single (some k) 1)
        (dirLoss (jointStat L₀ R) (Pi.single none 1)) = featObsCov μ π L₀ R t a L₀ := by
  funext k
  simp [covVec, featObsCov, dirLoss_jointStat_single_some, dirLoss_jointStat_single_none,
    priorCov_natCoord]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR hnd

/-- **The feature covariance matrix is invertible** under nondegeneracy. -/
theorem featCov_mulVec_injective {t : ℝ} (ht : 0 < t) (a : ι → ℝ) :
    Function.Injective (featCov μ π L₀ R t a).mulVec := by
  classical
  rw [featCov_eq_covMat]
  exact covMat_mulVec_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a _
    (Pi.linearIndependent_single_one ι ℝ)

theorem featCov_mulVec_surjective {t : ℝ} (ht : 0 < t) (a : ι → ℝ) :
    Function.Surjective (featCov μ π L₀ R t a).mulVec := by
  classical
  exact Matrix.mulVec_surjective_iff_isUnit.2 (Matrix.mulVec_injective_iff_isUnit.1
    (featCov_mulVec_injective hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a))

variable [Nonempty ι]

/-- **Temperature derivative of any observable at fixed feature response**:
`∂_t ⟨φ⟩|_M = −(Cov(φ, L₀) − ∑ₖ bₖ Cov(φ, Rₖ))` with `C b = Cov(R, L₀)`, all under the posterior at
`(t₀, M)`. Fixed-feature annealing responds only to the loss component orthogonal to the
features. -/
theorem hasDerivAt_obsMean_temp {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) {φ : X → ℝ} (hφ : Bdd φ) {b : ι → ℝ}
    (hb : (featCov μ π L₀ R t₀ (Function.invFun (meanMap μ π L₀ R t₀) M)).mulVec b =
      featObsCov μ π L₀ R t₀ (Function.invFun (meanMap μ π L₀ R t₀) M) L₀) :
    HasDerivAt (fun t ↦ obsMean μ π L₀ φ R t M)
      (-(priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) φ L₀ t₀ -
        ∑ k, b k * priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M)) φ (R k)
          t₀)) t₀ := by
  classical
  set a₀ := Function.invFun (meanMap μ π L₀ R t₀) M with ha₀
  set θ₀ := tempPath μ π L₀ R M t₀ with hθ₀
  have hθ₀eq : θ₀ = natCoord t₀ a₀ := tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  -- the velocity of the temperature path
  set u := (sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀).symm (Pi.single none 1) with hu
  have hu1 : u none = 1 := tempPath_velocity_none hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀
  have hpath : HasDerivAt (tempPath μ π L₀ R M)
      (Pi.single none 1 + ∑ k, u (some k) • (Pi.single (some k) 1 : Option ι → ℝ)) t₀ := by
    have h := hasDerivAt_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
    rwa [← velocity_decomp u hu1]
  -- the feature responses are constant along the path
  have hconst : ∀ k, ∀ᶠ t in 𝓝 t₀, priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R)
      (tempPath μ π L₀ R M t)) (dirLoss (jointStat L₀ R) (Pi.single (some k) 1)) 1 = M k := by
    intro k
    filter_upwards [lt_mem_nhds ht₀] with t ht
    rw [dirLoss_jointStat_single_some]
    exact tempPath_response hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM k
  -- the covariance data at the base point
  have hbJ : (covMat μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ₀
      (fun k ↦ Pi.single (some k) 1)).mulVec b =
      covVec μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ₀ (fun k ↦ Pi.single (some k) 1)
        (dirLoss (jointStat L₀ R) (Pi.single none 1)) := by
    rw [hθ₀eq, covMat_joint_eq, covVec_joint_eq]
    exact hb
  have hinjJ : Function.Injective (covMat μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ₀
      (fun k ↦ Pi.single (some k) 1)).mulVec := by
    rw [hθ₀eq, covMat_joint_eq]
    exact featCov_mulVec_injective hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ a₀
  have key := multi_constrained_response_deriv_path hπm hπi hπ hπpos measurable_const h0 hS'
    one_pos (tempPath μ π L₀ R M) (Pi.single none 1) (fun k ↦ Pi.single (some k) 1)
    (fun k ↦ u (some k)) t₀ hpath hconst hbJ hinjJ hφ
  -- read the observable along the path in the `a`-chart
  have hfun : (fun t ↦ obsMean μ π L₀ φ R t M) =ᶠ[𝓝 t₀] fun t ↦
      priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t)) φ 1 := by
    filter_upwards [lt_mem_nhds ht₀] with t ht
    exact obsMean_eq_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM φ
  refine (key.congr_of_eventuallyEq hfun).congr_deriv ?_
  have hθ₀eq' : tempPath μ π L₀ R M t₀ = natCoord t₀ a₀ := hθ₀eq
  rw [hθ₀eq', dirLoss_jointStat_single_none]
  simp only [dirLoss_jointStat_single_some, priorCov_natCoord]
  ring

/-- **The loss surface descends at the rate of the unexplained variance**:
`∂_t h(t, M) = −Var(L₀ − ∑ₖ bₖ Rₖ)` with `C b = Cov(R, L₀)`. -/
theorem hasDerivAt_lossSurface {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) {b : ι → ℝ}
    (hb : (featCov μ π L₀ R t₀ (Function.invFun (meanMap μ π L₀ R t₀) M)).mulVec b =
      featObsCov μ π L₀ R t₀ (Function.invFun (meanMap μ π L₀ R t₀) M) L₀) :
    HasDerivAt (fun t ↦ obsMean μ π L₀ L₀ R t M)
      (-priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M))
        (fun x ↦ L₀ x - dirLoss R b x) (fun x ↦ L₀ x - dirLoss R b x) t₀) t₀ := by
  classical
  refine (hasDerivAt_obsMean_temp hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM ⟨hL₀m, M₀, hL₀⟩
    hb).congr_deriv ?_
  rw [featCov_eq_covMat, featObsCov_eq_covVec] at hb
  have h := residual_var hπm hπi hπ hπpos hL₀m hL₀ hR (t := t₀) _ (fun k ↦ Pi.single k 1)
    ⟨hL₀m, M₀, hL₀⟩ b hb
  rw [sum_smul_single_eq] at h
  rw [h]
  congr 2
  exact Finset.sum_congr rfl fun k _ ↦ by rw [dirLoss_pi_single, priorCov_comm π _ L₀ (R k) t₀]

/-- The temperature derivative of the loss surface is nonpositive. -/
theorem lossSurface_deriv_nonpos {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    deriv (fun t ↦ obsMean μ π L₀ L₀ R t M) t₀ ≤ 0 := by
  obtain ⟨b, hb⟩ := featCov_mulVec_surjective hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀
    (Function.invFun (meanMap μ π L₀ R t₀) M)
    (featObsCov μ π L₀ R t₀ (Function.invFun (meanMap μ π L₀ R t₀) M) L₀)
  rw [(hasDerivAt_lossSurface hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM hb).deriv, neg_nonpos]
  exact priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t₀) _
    (Bdd.sub ⟨hL₀m, M₀, hL₀⟩ (bdd_dirLoss hR b))

/-- **The loss surface is nonincreasing in the temperature at fixed feature response.** -/
theorem lossSurface_antitoneOn {M : ι → ℝ} (hM : M ∈ interior (momentBody μ π R)) :
    AntitoneOn (fun t ↦ obsMean μ π L₀ L₀ R t M) (Ioi 0) := by
  have hdiff : DifferentiableOn ℝ (fun t ↦ obsMean μ π L₀ L₀ R t M) (Ioi 0) := by
    intro t ht
    obtain ⟨b, hb⟩ := featCov_mulVec_surjective hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht
      (Function.invFun (meanMap μ π L₀ R t) M)
      (featObsCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M) L₀)
    exact (hasDerivAt_lossSurface hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
      hb).differentiableAt.differentiableWithinAt
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hdiff.continuousOn ?_ ?_
  · rw [interior_Ioi]; exact hdiff
  · rw [interior_Ioi]
    exact fun t ht ↦ lossSurface_deriv_nonpos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM

end

section Gradient

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hφm hφ

omit [Nonempty X] ht hnd hφm hφ in
/-- The feature covariance applied to a direction is the covariance with the contrast. -/
theorem featCov_mulVec_apply (a v : ι → ℝ) (i : ι) :
    (featCov μ π L₀ R t a).mulVec v i = priorCov μ π (affLoss L₀ R a) (R i) (dirLoss R v) t := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  rw [priorCov_comm π _ (R i) _ t, ← sum_mul_priorCov_eq hν hR (hR i) v]
  simp only [Matrix.mulVec, dotProduct, featCov, Matrix.of_apply]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [priorCov_comm π _ (R i) (R l) t, mul_comm]

/-- **The gradient of an observable's surface in the feature directions is its regression
coefficient vector**: `D_M ⟨φ⟩ [d] = ∑ₖ bₖ dₖ` whenever `C b = Cov(R, φ)`. -/
theorem obsMean_fderiv_eq_regression (a d : ι → ℝ) {b : ι → ℝ}
    (hb : (featCov μ π L₀ R t a).mulVec b = featObsCov μ π L₀ R t a φ) :
    ((obsMapDeriv μ π L₀ φ R t a).comp
        (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a)) d = ∑ k, b k * d k := by
  obtain ⟨v, rfl⟩ := featCov_mulVec_surjective hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a d
  have hd : (featCov μ π L₀ R t a).mulVec v =
      fun i ↦ priorCov μ π (affLoss L₀ R a) (R i) (dirLoss R v) t :=
    funext fun i ↦ featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a v i
  rw [hd, obsMean_deriv_cov hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hφm hφ a v]
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  -- `∑ₖ bₖ (Cv)ₖ = ∑ₗ vₗ (Cb)ₗ = ∑ₗ vₗ Cov(Rₗ, φ) = Cov(R_v, φ)`
  have e1 : ∑ k, b k * priorCov μ π (affLoss L₀ R a) (R k) (dirLoss R v) t =
      ∑ l, v l * priorCov μ π (affLoss L₀ R a) (R l) φ t := by
    have hC : ∀ k, priorCov μ π (affLoss L₀ R a) (R k) (dirLoss R v) t =
        ∑ l, v l * priorCov μ π (affLoss L₀ R a) (R l) (R k) t := fun k ↦ by
      rw [priorCov_comm π _ (R k) _ t, ← sum_mul_priorCov_eq hν hR (hR k) v]
    have hCb : ∀ l, priorCov μ π (affLoss L₀ R a) (R l) φ t =
        ∑ k, b k * priorCov μ π (affLoss L₀ R a) (R l) (R k) t := fun l ↦ by
      have := congrFun hb l
      simp only [Matrix.mulVec, dotProduct, featCov, Matrix.of_apply, featObsCov] at this
      rw [← this]
      exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
    simp only [hC, hCb, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  rw [e1, sum_mul_priorCov_eq hν hR ⟨hφm, Mφ, hφ⟩ v, priorCov_comm π _ (dirLoss R v) φ t]

end Gradient

end Laplace.Multi
