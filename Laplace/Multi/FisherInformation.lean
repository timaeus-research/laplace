/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MeanMapInjective

/-!
# The response form is the Fisher information of the posterior family

The posteriors `P_a ∝ e^{-t L_a} π` of an affine data family form a statistical model over the data
coordinate `a`. Its score in the direction `v` is

  `∂_v log p_a(x) = −t (R_v(x) − ⟨R_v⟩_a)`   (`affScore`, `hasDerivAt_affLogDensity`),

it has posterior mean zero (`priorExp_affScore`), and its second moment is the response form:

  `E_a[∂_v log p_a · ∂_w log p_a] = t² Cov_a(R_v, R_w) = G_a(v, w)`
  (`fisherInformation_eq_responseForm`).

So the response form `G_a` — the metric of the whole response-map programme, the object whose
lengths give the `√λ log t`, `√t` and `O(1)` laws — is literally the Fisher–Rao metric of the
posterior family pulled back to the data manifold (Astra, round 25, item 5, in its intrinsic form).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The log-density of the affine posterior family relative to the prior: `−t L_a(x) − log Z(a)`. -/
noncomputable def affLogDensity (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a : ι → ℝ) (x : X) : ℝ :=
  -(t * affLoss L₀ R a x) - affLogZ μ π L₀ R t a

/-- The score of the affine family in the direction `v`: `−t (R_v(x) − ⟨R_v⟩_a)`. -/
noncomputable def affScore (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a v : ι → ℝ)
    (x : X) : ℝ :=
  -t * (dirLoss R v x - priorExp μ π (affLoss L₀ R a) (dirLoss R v) t)

variable [Nonempty X]

/-- **The score is the directional derivative of the log-density.** -/
theorem hasDerivAt_affLogDensity {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (t : ℝ) (a v : ι → ℝ) (x : X) :
    HasDerivAt (fun ε : ℝ ↦ affLogDensity μ π L₀ R t (a + ε • v) x)
      (affScore μ π L₀ R t a v x) 0 := by
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a v t
  have h0 : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) 0 :=
    h.changeR measurable_const fun _ ↦ by simp
  have hZ := h0.hasDerivAt_affLogZ_dir hR v
  -- the loss along the line is affine in `ε`
  have hL : HasDerivAt (fun ε : ℝ ↦ -(t * affLoss L₀ R (a + ε • v) x))
      (-(t * dirLoss R v x)) 0 := by
    have e : ∀ ε : ℝ, -(t * affLoss L₀ R (a + ε • v) x) =
        -(t * affLoss L₀ R a x) + ε * (-(t * dirLoss R v x)) := fun ε ↦ by
      rw [affLoss_add_smul]
      simp only [pathLoss]
      ring
    simp_rw [e]
    exact (((hasDerivAt_id' (x := (0 : ℝ))).mul_const _).const_add _).congr_deriv (one_mul _)
  have := hL.sub hZ
  refine this.congr_deriv ?_
  unfold affScore
  ring

omit [Nonempty X] in
/-- The score has posterior mean zero. -/
theorem priorExp_affScore {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (t : ℝ) (a v : ι → ℝ) :
    priorExp μ π (affLoss L₀ R a) (affScore μ π L₀ R t a v) t = 0 := by
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a v t
  have hZ : priorZ μ π (affLoss L₀ R a) t ≠ 0 := h.ν_pos.ne'
  unfold affScore priorExp
  unfold priorZ at hZ ⊢
  have hRv : Integrable (fun x ↦ dirLoss R v x * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) μ :=
    h.ν_int.bdd_mul h.R_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact h.R_bound x)
  set m := (∫ x, dirLoss R v x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) /
    ∫ x, Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ with hm
  have e : ∀ x, -t * (dirLoss R v x - m) * Real.exp (-(t * affLoss L₀ R a x)) * π x =
      (-t) * (dirLoss R v x * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) -
        (-t * m) * (Real.exp (-(t * affLoss L₀ R a x)) * π x) := fun x ↦ by ring
  simp_rw [e]
  have I1 : Integrable (fun x ↦ (-t) *
      (dirLoss R v x * (Real.exp (-(t * affLoss L₀ R a x)) * π x))) μ := hRv.const_mul _
  have I0 : Integrable (fun x ↦ (-t * m) * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) μ :=
    h.ν_int.const_mul _
  rw [integral_sub I1 I0, integral_const_mul, integral_const_mul]
  have hRv' : (∫ x, dirLoss R v x * (Real.exp (-(t * affLoss L₀ R a x)) * π x) ∂μ) =
      ∫ x, dirLoss R v x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  rw [hRv', div_eq_zero_iff]
  left
  rw [hm]
  field_simp
  ring

omit [Nonempty X] in
/-- **Fisher information = response form**:
`E_a[∂_v log p_a · ∂_w log p_a] = t² Cov_a(R_v, R_w)`. -/
theorem fisherInformation_eq_responseForm {π L₀ : X → ℝ} (hπm : Measurable π)
    (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀)
    {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (t : ℝ)
    (a v w : ι → ℝ) :
    priorExp μ π (affLoss L₀ R a)
        (fun x ↦ affScore μ π L₀ R t a v x * affScore μ π L₀ R t a w x) t =
      responseForm μ π L₀ R a t v w := by
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a v t
  have hZ : priorZ μ π (affLoss L₀ R a) t ≠ 0 := h.ν_pos.ne'
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  obtain ⟨hwm, Mw, hwb⟩ := bdd_dirLoss hR w
  have hint : ∀ φ : X → ℝ, Bdd φ →
      Integrable (fun x ↦ φ x * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) μ := fun φ hφ ↦ by
    obtain ⟨hm, Mφ, hMφ⟩ := hφ
    exact h.ν_int.bdd_mul hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hMφ x)
  have hIv := hint _ ⟨hvm, Mv, hvb⟩
  have hIw := hint _ ⟨hwm, Mw, hwb⟩
  have hIvw := hint _ (Bdd.mul ⟨hvm, Mv, hvb⟩ ⟨hwm, Mw, hwb⟩)
  unfold responseForm priorCov affScore priorExp
  unfold priorZ at hZ ⊢
  set Z := ∫ x, Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ with hZdef
  set mv := (∫ x, dirLoss R v x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) / Z with hmv
  set mw := (∫ x, dirLoss R w x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) / Z with hmw
  have expand : ∀ x, -t * (dirLoss R v x - mv) * (-t * (dirLoss R w x - mw)) *
      Real.exp (-(t * affLoss L₀ R a x)) * π x =
      t ^ 2 * (dirLoss R v x * dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) -
        (t ^ 2 * mv) * (dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) -
        (t ^ 2 * mw) * (dirLoss R v x * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) +
        (t ^ 2 * mv * mw) * (Real.exp (-(t * affLoss L₀ R a x)) * π x) := fun x ↦ by ring
  simp_rw [expand]
  have I3 : Integrable (fun x ↦ t ^ 2 *
      (dirLoss R v x * dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x))) μ :=
    hIvw.const_mul _
  have I2 : Integrable (fun x ↦ (t ^ 2 * mv) *
      (dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x))) μ := hIw.const_mul _
  have I1 : Integrable (fun x ↦ (t ^ 2 * mw) *
      (dirLoss R v x * (Real.exp (-(t * affLoss L₀ R a x)) * π x))) μ := hIv.const_mul _
  have I0 : Integrable (fun x ↦ (t ^ 2 * mv * mw) *
      (Real.exp (-(t * affLoss L₀ R a x)) * π x)) μ := h.ν_int.const_mul _
  have I32 : Integrable (fun x ↦ t ^ 2 *
      (dirLoss R v x * dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) -
      (t ^ 2 * mv) * (dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x))) μ :=
    I3.sub I2
  have I321 : Integrable (fun x ↦ t ^ 2 *
      (dirLoss R v x * dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) -
      (t ^ 2 * mv) * (dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x)) -
      (t ^ 2 * mw) * (dirLoss R v x * (Real.exp (-(t * affLoss L₀ R a x)) * π x))) μ :=
    I32.sub I1
  rw [integral_add I321 I0, integral_sub I32 I1, integral_sub I3 I2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]
  have ev : (∫ x, dirLoss R v x * (Real.exp (-(t * affLoss L₀ R a x)) * π x) ∂μ) =
      ∫ x, dirLoss R v x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  have ew : (∫ x, dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x) ∂μ) =
      ∫ x, dirLoss R w x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  have evw : (∫ x, dirLoss R v x * dirLoss R w x * (Real.exp (-(t * affLoss L₀ R a x)) * π x) ∂μ)
      = ∫ x, dirLoss R v x * dirLoss R w x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  rw [ev, ew, evw, hmv, hmw]
  field_simp
  ring

end Laplace.Multi
