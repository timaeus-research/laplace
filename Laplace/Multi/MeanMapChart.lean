/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MeanMapJacobian

/-!
# The response coordinates are a local chart of the data manifold

For an affine data family with non-degenerate contrasts, the mean map `m(a) = (⟨Rᵢ⟩_{t,a})ᵢ` is
**strictly** differentiable (`hasStrictFDerivAt_meanMap`) with an invertible Jacobian
(`meanMapDerivEquiv`, from the finite-dimensional injective ⇒ bijective step), so the inverse
function theorem applies: there is a local inverse `meanMapInverse` with

  `meanMapInverse (m a) = a` near `a₀`, `m (meanMapInverse y) = y` near `m a₀`,
  `D(meanMapInverse)(m a₀) = (Dm(a₀))⁻¹` (`hasStrictFDerivAt_meanMapInverse`),

and `m` maps neighbourhoods of `a₀` onto neighbourhoods of `m a₀` (`map_nhds_meanMap`). The
posterior means of the contrasts are thus genuine local coordinates on the data manifold, with the
data coordinate recovered from the response by a strictly differentiable inverse whose derivative
is the inverse response form (`−(1/t) G_{a₀}`)⁻¹. This closes Astra's item D.

The one analytic input beyond `MeanMapJacobian` is continuity of the Jacobian in `a`
(`continuousAt_affNumDeriv`), by dominated convergence with the same majorant as the derivative.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

variable [Nonempty X]

/-- **Continuity of the numerator derivative in the data coordinate**, by dominated convergence. -/
theorem continuousAt_affNumDeriv {π L₀ : X → ℝ} (hπm : Measurable π)
    (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {φ : X → ℝ} (hφm : Measurable φ)
    {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ) {t : ℝ} (ht : 0 < t) (a₀ : ι → ℝ) :
    ContinuousAt (fun a ↦ affNumDeriv μ π L₀ φ R t a) a₀ := by
  classical
  choose M hM using fun j ↦ (hR j).2
  set S : ℝ := ∑ j, M j with hS
  have hMj : ∀ j, 0 ≤ M j := fun j ↦ le_trans (abs_nonneg _) (hM j (Classical.arbitrary X))
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ hMj j
  have hMφ : 0 ≤ Mφ := le_trans (abs_nonneg _) (hφ (Classical.arbitrary X))
  have hLm : ∀ a, Measurable (affLoss L₀ R a) := fun a ↦ (bdd_affLoss hL₀m hL₀ hR a).1
  obtain ⟨_, ML, hLb⟩ := bdd_affLoss hL₀m hL₀ hR a₀
  have hbase : Integrable (fun x ↦ Real.exp (-(t * affLoss L₀ R a₀ x)) * π x) μ :=
    hπi.bdd_mul (c := Real.exp (t * ML))
      (Real.measurable_exp.comp ((hLm a₀).const_mul t).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
        have := hLb x
        rw [abs_le] at this
        nlinarith [ht.le])
  have hdiff : ∀ a x, affLoss L₀ R a x = affLoss L₀ R a₀ x + dirLoss R (a - a₀) x := fun a x ↦ by
    simp only [affLoss, dirLoss, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  have hdir : ∀ (w : ι → ℝ) x, |dirLoss R w x| ≤ ‖w‖ * S := fun w x ↦ by
    calc |dirLoss R w x| = |∑ j, w j * R j x| := rfl
      _ ≤ ∑ j, |w j * R j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ‖w‖ * M j := Finset.sum_le_sum fun j _ ↦ by
          rw [abs_mul]
          refine mul_le_mul ?_ (hM j x) (abs_nonneg _) (norm_nonneg _)
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm w j
      _ = ‖w‖ * S := by rw [hS, Finset.mul_sum]
  have hea : ∀ a ∈ Metric.ball a₀ 1, ∀ x, Real.exp (-(t * affLoss L₀ R a x)) ≤
      Real.exp (t * S) * Real.exp (-(t * affLoss L₀ R a₀ x)) := fun a ha x ↦ by
    rw [← Real.exp_add, Real.exp_le_exp, hdiff a x]
    have h1 := hdir (a - a₀) x
    have h2 : ‖a - a₀‖ ≤ 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at ha
      exact ha.le
    have h3 : |dirLoss R (a - a₀) x| ≤ S := le_trans h1 (by nlinarith)
    rw [abs_le] at h3
    nlinarith [ht.le]
  have hsum : ∀ x, ∑ j, |R j x| ≤ S := fun x ↦ Finset.sum_le_sum fun j _ ↦ hM j x
  have hF'_meas : ∀ a : ι → ℝ, AEStronglyMeasurable
      (fun x ↦ (-(t * (φ x * Real.exp (-(t * affLoss L₀ R a x)) * π x))) • dirCLM R x) μ :=
    fun a ↦ by
    have hc : Measurable fun x ↦ -(t * (φ x * Real.exp (-(t * affLoss L₀ R a x)) * π x)) :=
      (((hφm.mul (Real.measurable_exp.comp ((hLm a).const_mul t).neg)).mul hπm).const_mul
        t).neg
    exact hc.aestronglyMeasurable.smul (aestronglyMeasurable_dirCLM hR)
  unfold affNumDeriv
  refine continuousAt_of_dominated (bound := fun x ↦
      t * Mφ * S * Real.exp (t * S) * (Real.exp (-(t * affLoss L₀ R a₀ x)) * π x))
    (Filter.Eventually.of_forall hF'_meas) ?_ (hbase.const_mul _)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds a₀ one_pos) fun a ha ↦
      Filter.Eventually.of_forall fun x ↦ ?_
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos ht, abs_mul, abs_mul,
      Real.abs_exp, abs_of_nonneg (hπ x)]
    have hd : ‖dirCLM R x‖ ≤ S := le_trans (norm_dirCLM_le R x) (hsum x)
    have hlhs : |φ x| * Real.exp (-(t * affLoss L₀ R a x)) * π x ≤
        Mφ * (Real.exp (t * S) * Real.exp (-(t * affLoss L₀ R a₀ x))) * π x :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hφ x) (hea a ha x) (Real.exp_pos _).le hMφ) (hπ x)
    calc t * (|φ x| * Real.exp (-(t * affLoss L₀ R a x)) * π x) * ‖dirCLM R x‖
        ≤ t * (Mφ * (Real.exp (t * S) * Real.exp (-(t * affLoss L₀ R a₀ x))) * π x) * S :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlhs ht.le) hd (norm_nonneg _)
            (mul_nonneg ht.le (mul_nonneg (mul_nonneg hMφ (mul_nonneg (Real.exp_pos _).le
              (Real.exp_pos _).le)) (hπ x)))
      _ = t * Mφ * S * Real.exp (t * S) * (Real.exp (-(t * affLoss L₀ R a₀ x)) * π x) := by ring
  · exact (((hasFDerivAt_affWeight L₀ R φ π t x a₀).continuousAt.const_mul t).neg).smul
      continuousAt_const

/-- **Strict differentiability of the mean map** (its Jacobian is continuous in `a`). -/
theorem hasStrictFDerivAt_meanMap {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
    (a₀ : ι → ℝ) :
    HasStrictFDerivAt (meanMap μ π L₀ R t) (meanMapDeriv μ π L₀ R t a₀) a₀ := by
  have hZ : ∀ a, priorZ μ π (affLoss L₀ R a) t ≠ 0 := fun a ↦
    (tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a 0 t).choose_spec.ν_pos.ne'
  have hder : ∀ a, HasFDerivAt (fun a i ↦ priorExp μ π (affLoss L₀ R a) (R i) t)
      (ContinuousLinearMap.pi fun i ↦
        (priorZ μ π (affLoss L₀ R a) t)⁻¹ • affNumDeriv μ π L₀ (R i) R t a -
          ((∫ x, R i x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) *
            (priorZ μ π (affLoss L₀ R a) t ^ 2)⁻¹) • affNumDeriv μ π L₀ (fun _ ↦ 1) R t a) a :=
    fun a ↦ hasFDerivAt_meanMap hπm hπi hπ hL₀m hL₀ hR ht (hZ a)
  unfold meanMap meanMapDeriv
  refine hasStrictFDerivAt_pi'' fun i ↦ ?_
  rw [ContinuousLinearMap.proj_pi]
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (f' := fun a ↦
      (priorZ μ π (affLoss L₀ R a) t)⁻¹ • affNumDeriv μ π L₀ (R i) R t a -
        ((∫ x, R i x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) *
          (priorZ μ π (affLoss L₀ R a) t ^ 2)⁻¹) • affNumDeriv μ π L₀ (fun _ ↦ 1) R t a)
    (Filter.Eventually.of_forall fun a ↦ hasFDerivAt_pi.mp (hder a) i) ?_
  -- continuity of the Jacobian entry
  obtain ⟨_, hZ'⟩ := hasFDerivAt_affNum hπm hπi hπ hL₀m hL₀ hR (φ := fun _ ↦ (1 : ℝ))
    measurable_const (Mφ := 1) (fun _ ↦ by simp) ht a₀
  obtain ⟨Mi, hMi⟩ := (hR i).2
  obtain ⟨_, hN'⟩ := hasFDerivAt_affNum hπm hπi hπ hL₀m hL₀ hR (φ := R i) (hR i).1 hMi ht a₀
  have hZc : ContinuousAt (fun a ↦ priorZ μ π (affLoss L₀ R a) t) a₀ := by
    have := hZ'.continuousAt
    simp only [one_mul] at this
    exact this
  have hNc : ContinuousAt
      (fun a ↦ ∫ x, R i x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) a₀ := hN'.continuousAt
  have hDi : ContinuousAt (fun a ↦ affNumDeriv μ π L₀ (R i) R t a) a₀ :=
    continuousAt_affNumDeriv hπm hπi hπ hL₀m hL₀ hR (hR i).1 hMi ht a₀
  have hD1 : ContinuousAt (fun a ↦ affNumDeriv μ π L₀ (fun _ ↦ (1 : ℝ)) R t a) a₀ :=
    continuousAt_affNumDeriv hπm hπi hπ hL₀m hL₀ hR measurable_const (Mφ := 1) (fun _ ↦ by simp)
      ht a₀
  exact ((hZc.inv₀ (hZ a₀)).smul hDi).sub
    ((hNc.mul ((hZc.pow 2).inv₀ (pow_ne_zero 2 (hZ a₀)))).smul hD1)

/-- The Jacobian of the mean map as a continuous linear equivalence (finite dimension: injective
⇒ bijective). -/
noncomputable def meanMapDerivEquiv {π L₀ : X → ℝ} {R : ι → X → ℝ} {t : ℝ} {a₀ : ι → ℝ}
    (hinj : Function.Injective (meanMapDeriv μ π L₀ R t a₀)) : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
  (LinearEquiv.ofInjectiveEndo (meanMapDeriv μ π L₀ R t a₀ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    hinj).toContinuousLinearEquiv

omit [Nonempty X] in
theorem coe_meanMapDerivEquiv {π L₀ : X → ℝ} {R : ι → X → ℝ} {t : ℝ} {a₀ : ι → ℝ}
    (hinj : Function.Injective (meanMapDeriv μ π L₀ R t a₀)) :
    (meanMapDerivEquiv hinj : (ι → ℝ) →L[ℝ] (ι → ℝ)) = meanMapDeriv μ π L₀ R t a₀ := by
  ext v
  simp only [meanMapDerivEquiv, ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_ofInjectiveEndo,
    ContinuousLinearMap.coe_coe]

/-- The mean map is strictly differentiable with an invertible derivative at every data point. -/
theorem hasStrictFDerivAt_meanMap_equiv {π L₀ : X → ℝ} (hπm : Measurable π)
    (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀)
    {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) (a₀ : ι → ℝ) :
    HasStrictFDerivAt (meanMap μ π L₀ R t)
      (meanMapDerivEquiv (meanMapDeriv_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀) :
        (ι → ℝ) →L[ℝ] (ι → ℝ)) a₀ := by
  rw [coe_meanMapDerivEquiv]
  exact hasStrictFDerivAt_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀

/-- **The local inverse of the mean map**: the data coordinate as a function of the response. -/
noncomputable def meanMapInverse {π L₀ : X → ℝ} (hπm : Measurable π)
    (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀)
    {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) (a₀ : ι → ℝ) :
    (ι → ℝ) → (ι → ℝ) :=
  (hasStrictFDerivAt_meanMap_equiv hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀).localInverse _ _ _

section Chart

variable {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) (a₀ : ι → ℝ)

include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd

/-- The data coordinate is recovered from the response near `a₀`. -/
theorem meanMapInverse_meanMap :
    ∀ᶠ a in 𝓝 a₀,
      meanMapInverse hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ (meanMap μ π L₀ R t a) = a :=
  (hasStrictFDerivAt_meanMap_equiv hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀).eventually_left_inverse

/-- Every response near `m(a₀)` is the response of a data point. -/
theorem meanMap_meanMapInverse :
    ∀ᶠ y in 𝓝 (meanMap μ π L₀ R t a₀),
      meanMap μ π L₀ R t (meanMapInverse hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ y) = y :=
  (hasStrictFDerivAt_meanMap_equiv hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀).eventually_right_inverse

/-- The local inverse fixes the base response. -/
theorem meanMapInverse_apply_meanMap :
    meanMapInverse hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ (meanMap μ π L₀ R t a₀) = a₀ :=
  (hasStrictFDerivAt_meanMap_equiv hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀).localInverse_apply_image

/-- The local inverse is continuous at the base response. -/
theorem meanMapInverse_continuousAt :
    ContinuousAt (meanMapInverse hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀) (meanMap μ π L₀ R t a₀) :=
  (hasStrictFDerivAt_meanMap_equiv hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀).localInverse_continuousAt

/-- **The inverse chart is strictly differentiable with derivative `(Dm(a₀))⁻¹`.** -/
theorem hasStrictFDerivAt_meanMapInverse :
    HasStrictFDerivAt (meanMapInverse hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀)
      ((meanMapDerivEquiv (meanMapDeriv_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀)).symm :
        (ι → ℝ) →L[ℝ] (ι → ℝ)) (meanMap μ π L₀ R t a₀) :=
  (hasStrictFDerivAt_meanMap_equiv hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀).to_localInverse

/-- **The response coordinates are a local chart**: the mean map carries neighbourhoods of `a₀`
onto neighbourhoods of `m(a₀)`. -/
theorem map_nhds_meanMap :
    map (meanMap μ π L₀ R t) (𝓝 a₀) = 𝓝 (meanMap μ π L₀ R t a₀) :=
  (hasStrictFDerivAt_meanMap_equiv hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀).map_nhds_eq_of_equiv

/-- The derivative of the inverse chart composed with the Jacobian is the identity. -/
theorem meanMapInverse_deriv_comp :
    ((meanMapDerivEquiv (meanMapDeriv_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀)).symm :
        (ι → ℝ) →L[ℝ] (ι → ℝ)).comp (meanMapDeriv μ π L₀ R t a₀) =
      ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have h := coe_meanMapDerivEquiv (μ := μ)
    (meanMapDeriv_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀)
  rw [← h]
  exact ContinuousLinearEquiv.coe_symm_comp_coe
    (meanMapDerivEquiv (meanMapDeriv_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀))

end Chart

end Laplace.Multi
