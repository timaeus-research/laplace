/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MeanMapInjective

/-!
# The Fréchet derivative of the affine numerators

Towards the mean map as a chart (Astra's item D): the numerators `a ↦ ∫ φ e^{-t L_a} π` of the
affine family are Fréchet differentiable in `a ∈ ℝ^k`, with derivative the integral of the
pointwise derivative `−t φ e^{-t L_a} π · R_(·)(x)` (`hasFDerivAt_affNum`), by dominated
differentiation under the integral (`hasFDerivAt_integral_of_dominated_of_fderiv_le`) with the
direction functional `dirCLM R x : v ↦ R_v(x)` (`dirCLM`, `norm_dirCLM_le`) and the uniform
bound `e^{-t L_a} ≤ e^{t ∑ Mⱼ} e^{-t L_{a₀}}` on the unit ball. Evaluated on a direction `v` the
derivative is `−t ∫ φ R_v e^{-t L_{a₀}} π` (`hasFDerivAt_affNum_apply`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The direction functional `v ↦ R_v(x) = ∑ⱼ vⱼ Rⱼ(x)` as a continuous linear map. -/
noncomputable def dirCLM (R : ι → X → ℝ) (x : X) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ j, R j x • ContinuousLinearMap.proj j

omit [MeasurableSpace X] in
theorem dirCLM_apply (R : ι → X → ℝ) (x : X) (v : ι → ℝ) : dirCLM R x v = dirLoss R v x := by
  simp [dirCLM, dirLoss, mul_comm]

omit [MeasurableSpace X] in
/-- `‖dirCLM R x‖ ≤ ∑ⱼ |Rⱼ(x)|` (sup norm on `ι → ℝ`). -/
theorem norm_dirCLM_le (R : ι → X → ℝ) (x : X) : ‖dirCLM R x‖ ≤ ∑ j, |R j x| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ ↦ abs_nonneg _)
    fun v ↦ ?_
  rw [dirCLM_apply, Real.norm_eq_abs]
  calc |dirLoss R v x| = |∑ j, v j * R j x| := rfl
    _ ≤ ∑ j, |v j * R j x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |R j x| * ‖v‖ := Finset.sum_le_sum fun j _ ↦ by
        rw [abs_mul, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm v j
    _ = (∑ j, |R j x|) * ‖v‖ := (Finset.sum_mul _ _ _).symm

/-- The direction functional is (a.e. strongly) measurable in `x`. -/
theorem aestronglyMeasurable_dirCLM {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) :
    AEStronglyMeasurable (fun x ↦ dirCLM R x) μ := by
  unfold dirCLM
  have := Finset.aestronglyMeasurable_sum (μ := μ) Finset.univ fun j _ ↦
    (hR j).1.aestronglyMeasurable.smul_const (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) j)
  refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [Finset.sum_apply]

omit [MeasurableSpace X] in
/-- The affine loss as a base plus the direction functional. -/
theorem affLoss_eq_dirCLM (L₀ : X → ℝ) (R : ι → X → ℝ) (a : ι → ℝ) (x : X) :
    affLoss L₀ R a x = L₀ x + dirCLM R x a := by
  rw [dirCLM_apply]
  rfl

omit [MeasurableSpace X] in
/-- The pointwise Fréchet derivative of `a ↦ φ(x) e^{-t L_a(x)} π(x)`. -/
theorem hasFDerivAt_affWeight (L₀ : X → ℝ) (R : ι → X → ℝ) (φ π : X → ℝ) (t : ℝ) (x : X)
    (a : ι → ℝ) :
    HasFDerivAt (fun a : ι → ℝ ↦ φ x * Real.exp (-(t * affLoss L₀ R a x)) * π x)
      ((-(t * (φ x * Real.exp (-(t * affLoss L₀ R a x)) * π x))) • dirCLM R x) a := by
  have h1 : HasFDerivAt (fun a : ι → ℝ ↦ -(t * affLoss L₀ R a x)) (-(t • dirCLM R x)) a := by
    have h0 : HasFDerivAt (fun a : ι → ℝ ↦ affLoss L₀ R a x) (dirCLM R x) a := by
      have := ((dirCLM R x).hasFDerivAt (x := a)).const_add (L₀ x)
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun b ↦ ?_)
      simp only [affLoss_eq_dirCLM]
    exact (h0.const_mul t).neg
  have h2 := (h1.exp.const_mul (φ x)).mul_const (π x)
  refine h2.congr_fderiv ?_
  ext v
  simp only [smul_apply, neg_apply, smul_eq_mul]
  ring

/-- **Fréchet differentiability of the affine numerators**: for bounded `φ`, base loss and
contrasts, and `t > 0`,
`a ↦ ∫ φ e^{-t L_a} π` has derivative `∫ (−t φ e^{-t L_{a₀}} π) • dirCLM R x` at every `a₀`. -/
theorem hasFDerivAt_affNum [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π)
    (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {φ : X → ℝ} (hφm : Measurable φ)
    {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ) {t : ℝ} (ht : 0 < t) (a₀ : ι → ℝ) :
    Integrable (fun x ↦ (-(t * (φ x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x))) • dirCLM R x) μ ∧
    HasFDerivAt (fun a : ι → ℝ ↦ ∫ x, φ x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ)
      (∫ x, (-(t * (φ x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x))) • dirCLM R x ∂μ) a₀ := by
  classical
  choose M hM using fun j ↦ (hR j).2
  set S : ℝ := ∑ j, M j with hS
  have hMj : ∀ j, 0 ≤ M j := fun j ↦ le_trans (abs_nonneg _) (hM j (Classical.arbitrary X))
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ hMj j
  have hMφ : 0 ≤ Mφ := le_trans (abs_nonneg _) (hφ (Classical.arbitrary X))
  have hLm : ∀ a, Measurable (affLoss L₀ R a) := fun a ↦ (bdd_affLoss hL₀m hL₀ hR a).1
  have hF_meas : ∀ a : ι → ℝ,
      AEStronglyMeasurable (fun x ↦ φ x * Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
    fun a ↦ ((hφm.mul (Real.measurable_exp.comp ((hLm a).const_mul t).neg)).mul
      hπm).aestronglyMeasurable
  obtain ⟨_, ML, hLb⟩ := bdd_affLoss hL₀m hL₀ hR a₀
  have hbase : Integrable (fun x ↦ Real.exp (-(t * affLoss L₀ R a₀ x)) * π x) μ :=
    hπi.bdd_mul (c := Real.exp (t * ML))
      (Real.measurable_exp.comp ((hLm a₀).const_mul t).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
        have := hLb x
        rw [abs_le] at this
        nlinarith [ht.le])
  have hF_int : Integrable (fun x ↦ φ x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x) μ :=
    (hbase.bdd_mul hφm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hφ x)).congr
      (Filter.Eventually.of_forall fun x ↦ by ring)
  -- the difference of two affine losses is a direction loss, bounded by `‖a − a₀‖ S`
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
  have h_bound : ∀ᵐ x ∂μ, ∀ a ∈ Metric.ball a₀ 1,
      ‖(-(t * (φ x * Real.exp (-(t * affLoss L₀ R a x)) * π x))) • dirCLM R x‖ ≤
        t * Mφ * S * Real.exp (t * S) * (Real.exp (-(t * affLoss L₀ R a₀ x)) * π x) := by
    refine Filter.Eventually.of_forall fun x a ha ↦ ?_
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
  have hF'_meas : AEStronglyMeasurable
      (fun x ↦ (-(t * (φ x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x))) • dirCLM R x) μ := by
    have hc : Measurable fun x ↦ -(t * (φ x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x)) :=
      (((hφm.mul (Real.measurable_exp.comp ((hLm a₀).const_mul t).neg)).mul hπm).const_mul
        t).neg
    exact hc.aestronglyMeasurable.smul (aestronglyMeasurable_dirCLM hR)
  refine ⟨(hbase.const_mul _).mono' hF'_meas
    (h_bound.mono fun x hx ↦ hx a₀ (Metric.mem_ball_self one_pos)), ?_⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds a₀ one_pos)
    (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound (hbase.const_mul _)
    (Filter.Eventually.of_forall fun x a _ ↦ hasFDerivAt_affWeight L₀ R φ π t x a)

/-- The derivative of a numerator evaluated on a direction `v`: `−t ∫ φ R_v e^{-t L_{a₀}} π`. -/
theorem affNum_fderiv_apply {π L₀ φ : X → ℝ} {R : ι → X → ℝ} {t : ℝ} {a₀ : ι → ℝ}
    (hint : Integrable
      (fun x ↦ (-(t * (φ x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x))) • dirCLM R x) μ)
    (v : ι → ℝ) :
    (∫ x, (-(t * (φ x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x))) • dirCLM R x ∂μ) v =
      -t * ∫ x, φ x * dirLoss R v x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x ∂μ := by
  rw [ContinuousLinearMap.integral_apply hint v, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [smul_apply, smul_eq_mul, dirCLM_apply]
  ring

end Laplace.Multi
