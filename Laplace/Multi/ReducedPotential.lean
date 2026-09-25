/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LossSurface

/-!
# The reduced potential `J(t, M) = I_t(M)` and its block Hessian

The fixed-temperature dual potential `I_t(M)` (the seabed's `dualPotential … t M`) is the reduced
potential of the joint family. Its derivatives at `(t, M)`, `M` in the interior of the moment body:

* `∂_t J = h(t, M)`, the loss surface (`hasDerivAt_dualPotential_temp`; the envelope identity);
* `∇_M J = −t a(t, M)`, minus the natural feature coordinate (`hasFDerivAt_dualPotential`, landed);
* `D_M² J = C⁻¹`, the inverse feature covariance (`featCov_mulVec_dualHessian`);
* `∂_t ∇_M J = −∂_t β = b = C⁻¹ c` (`tempPath_velocity_some`) and `∇_M ∂_t J = ∇_M h = b`
  (`obsMean_fderiv_eq_regression`), the regression coefficients of the loss on the features;
* `∂_t² J = ∂_t h = −σ²`, minus the unexplained variance (`hasDerivAt_lossSurface`).

Also `∂_t A_t(a) = −⟨L₀ + ⟨a,R⟩⟩_{t,a}` (`hasDerivAt_affLogZ_temp`), and for the information
relative to the featureless distribution `𝒦(t, M) = J(t, M) + A_t(0) = KL(P_{t,M} ‖ P_{t,0})`,
`∂_t 𝒦 = h(t, M) − ⟨L₀⟩_{t,0}` (`hasDerivAt_infoRel_temp`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- **Temperature derivative of the free energy at fixed data**:
`∂_t A_t(a) = −(⟨L₀⟩_{t,a} + ⟨a, m(t,a)⟩) = −⟨L_a⟩_{t,a}`. -/
theorem hasDerivAt_affLogZ_temp (a : ι → ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ affLogZ μ π L₀ R t a)
      (-(priorExp μ π (affLoss L₀ R a) L₀ t₀ + dotJ a (meanMap μ π L₀ R t₀ a))) t₀ := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hB := hasFDerivAt_affLogZ hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS' one_pos
    (natCoord t₀ a)
  have hline : HasDerivAt (fun t : ℝ ↦ natCoord t a) (natCoord 1 a) t₀ := by
    have e : (fun t : ℝ ↦ natCoord t a) = fun t : ℝ ↦ t • natCoord 1 a :=
      funext fun t ↦ natCoord_eq_smul t a
    rw [e]
    simpa using (hasDerivAt_id t₀).smul_const (natCoord 1 a)
  have h := hB.comp_hasDerivAt t₀ hline
  have e2 : (fun t ↦ affLogZ μ π L₀ R t a) =
      (affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1) ∘ (fun t ↦ natCoord t a) := by
    funext t
    simp only [Function.comp, affLogZ_natCoord]
  rw [e2]
  refine h.congr_deriv ?_
  simp only [_root_.smul_apply, smul_eq_mul, dotCLM_apply, dotJ, Fintype.sum_option, natCoord,
    Option.elim, meanMap_natCoord_none, meanMap_natCoord_some]
  ring_nf

variable (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hnd

/-- `D_M² J = C⁻¹`: the dual Hessian inverts the feature covariance. -/
theorem featCov_mulVec_dualHessian {t : ℝ} (ht : 0 < t) (a d : ι → ℝ) :
    (featCov μ π L₀ R t a).mulVec
      (dualHessian hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a d) = d := by
  obtain ⟨v, rfl⟩ := featCov_mulVec_surjective hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a d
  have hd : (featCov μ π L₀ R t a).mulVec v =
      fun i ↦ priorCov μ π (affLoss L₀ R a) (R i) (dirLoss R v) t :=
    funext fun i ↦ featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a v i
  rw [hd, dualHessian_apply_cov hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a v, hd]

variable [Nonempty ι]

/-- The reduced potential read along the temperature path:
`J(t, M) = −⟨θ(t,M), (0, M)⟩ − B(θ(t,M))`. -/
theorem dualPotential_eq_tempPath {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    dualPotential μ π L₀ R t M =
      -dotJ (tempPath μ π L₀ R M t) (jointPoint 0 M) -
        affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (tempPath μ π L₀ R M t) := by
  rw [tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM, affLogZ_natCoord]
  unfold dualPotential
  congr 1
  simp only [dotJ, Fintype.sum_option, natCoord, jointPoint, Option.elim, mul_zero, zero_add,
    neg_mul, Finset.mul_sum]
  rw [Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **The envelope identity**: `∂_t J(t, M) = h(t, M)`, the loss surface. -/
theorem hasDerivAt_dualPotential_temp {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ dualPotential μ π L₀ R t M) (obsMean μ π L₀ L₀ R t₀ M) t₀ := by
  classical
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hB := hasFDerivAt_affLogZ hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS' one_pos
    (tempPath μ π L₀ R M t₀)
  have h1 : HasFDerivAt (fun θ : Option ι → ℝ ↦ dotJ θ (jointPoint 0 M)) (dotCLM (jointPoint 0 M))
      (tempPath μ π L₀ R M t₀) := by
    have e : (fun θ : Option ι → ℝ ↦ dotJ θ (jointPoint 0 M)) = ⇑(dotCLM (jointPoint 0 M)) :=
      funext fun θ ↦ (dotCLM_apply _ θ).symm
    rw [e]
    exact (dotCLM (jointPoint 0 M)).hasFDerivAt
  have hG := h1.neg.sub hB
  have hpath := hasDerivAt_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
  have h := hG.comp_hasDerivAt t₀ hpath
  have hfun : (fun t ↦ dualPotential μ π L₀ R t M) =ᶠ[𝓝 t₀] fun t ↦
      -dotJ (tempPath μ π L₀ R M t) (jointPoint 0 M) -
        affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (tempPath μ π L₀ R M t) := by
    filter_upwards [lt_mem_nhds ht₀] with t ht
    exact dualPotential_eq_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
  refine (h.congr_of_eventuallyEq hfun).congr_deriv ?_
  have hu1 := tempPath_velocity_none hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t₀)
  have hnone : meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (tempPath μ π L₀ R M t₀) none =
      priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t₀)) L₀ 1 :=
    rfl
  rw [obsMean_eq_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM L₀]
  simp only [_root_.sub_apply, _root_.neg_apply, _root_.smul_apply, smul_eq_mul, dotCLM_apply,
    dotJ, Fintype.sum_option, jointPoint, Option.elim, hu1, hnone,
    tempPath_response hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM]
  ring

/-- **The information relative to the featureless distribution** `𝒦(t, M) = J(t, M) + A_t(0)`
grows in temperature at the rate `h(t, M) − ⟨L₀⟩_{t,0}`. -/
theorem hasDerivAt_infoRel_temp {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ dualPotential μ π L₀ R t M + affLogZ μ π L₀ R t 0)
      (obsMean μ π L₀ L₀ R t₀ M - priorExp μ π (affLoss L₀ R 0) L₀ t₀) t₀ := by
  refine ((hasDerivAt_dualPotential_temp hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM).add
    (hasDerivAt_affLogZ_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 t₀)).congr_deriv ?_
  simp only [dotJ, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  ring

/-- **The mixed partial**: the feature components of the temperature-path velocity are
`∂_t β = −b`, minus the regression coefficients of the loss on the features (`C b = Cov(R, L₀)`). -/
theorem tempPath_velocity_some [DecidableEq ι] {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) {b : ι → ℝ}
    (hb : (featCov μ π L₀ R t₀ (Function.invFun (meanMap μ π L₀ R t₀) M)).mulVec b =
      featObsCov μ π L₀ R t₀ (Function.invFun (meanMap μ π L₀ R t₀) M) L₀) (k : ι) :
    (sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t₀)).symm
      (Pi.single none 1) (some k) = -b k := by
  classical
  have hθ₀eq : tempPath μ π L₀ R M t₀ = natCoord t₀ (Function.invFun (meanMap μ π L₀ R t₀) M) :=
    tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hu1 := tempPath_velocity_none hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t₀)
  have hpath : HasDerivAt (tempPath μ π L₀ R M)
      (Pi.single none 1 + ∑ k, (sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
        (tempPath μ π L₀ R M t₀)).symm (Pi.single none 1) (some k) •
          (Pi.single (some k) 1 : Option ι → ℝ)) t₀ := by
    have h := hasDerivAt_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
    rwa [← velocity_decomp _ hu1]
  have hconst : ∀ k, ∀ᶠ t in 𝓝 t₀, priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R)
      (tempPath μ π L₀ R M t)) (dirLoss (jointStat L₀ R) (Pi.single (some k) 1)) 1 = M k := by
    intro k
    filter_upwards [lt_mem_nhds ht₀] with t ht
    rw [dirLoss_jointStat_single_some]
    exact tempPath_response hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM k
  have hbJ : (covMat μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (tempPath μ π L₀ R M t₀)
      (fun k ↦ Pi.single (some k) 1)).mulVec b =
      covVec μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (tempPath μ π L₀ R M t₀)
        (fun k ↦ Pi.single (some k) 1) (dirLoss (jointStat L₀ R) (Pi.single none 1)) := by
    rw [hθ₀eq, covMat_joint_eq, covVec_joint_eq]
    exact hb
  have hinjJ : Function.Injective (covMat μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
      (tempPath μ π L₀ R M t₀) (fun k ↦ Pi.single (some k) 1)).mulVec := by
    rw [hθ₀eq, covMat_joint_eq]
    exact featCov_mulVec_injective hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ _
  have := constrained_velocity_eq hπm hπi hπ hπpos measurable_const h0 hS' one_pos
    (tempPath μ π L₀ R M) (Pi.single none 1) (fun k ↦ Pi.single (some k) 1)
    (fun k ↦ (sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t₀)).symm
      (Pi.single none 1) (some k)) t₀ hpath hconst hbJ hinjJ
  exact congrFun this k

end

end Laplace.Multi
