/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.JointChartMetric
import Laplace.Multi.HalfspaceProjection

/-!
# Relative entropy geometry and the featureless point

The entropy of a member `P_θ` of the joint family relative to the prior `π̄` is
`𝒮(θ) = −KL(P_θ ‖ π̄)` (`relEntropy`). In natural coordinates it is
`𝒮(θ) = ⟨θ, m(θ)⟩ + A(θ) − A(0)` (`relEntropy_eq`), i.e. in the `(t, a)` chart
`𝒮 = t h + t a·M + A_t(a) − log ∫π` (`relEntropy_natCoord`). It is maximal at the prior
(`relEntropy_nonpos`, `relEntropy_zero`).

Its differential is `d𝒮 = ⟨θ, dm⟩ = −G_θ(θ, ·)` (`hasDerivAt_relEntropy_path`); along the
temperature path at fixed response it decreases at the rate `t Var(H)`, `H` the residual
(`hasDerivAt_relEntropy_temp`), the constrained form of `d𝒮 = t dh + t a·dM`.

**The featureless point is the maximum-relative-entropy member at its loss expectation**: for
every member `ϑ` with `⟨L₀⟩_ϑ = ⟨L₀⟩_{t,0}`,
`𝒮(t, 0) − 𝒮(ϑ) = KL(P_ϑ ‖ P_{t,0}) ≥ 0`
(`relEntropy_featureless_sub`, `relEntropy_le_featureless`),
the Gibbs variational principle inside the family. The general identity is
`𝒮(θ) − 𝒮(ϑ) = KL(P_ϑ ‖ P_θ) − ⟨θ, m(ϑ) − m(θ)⟩` (`relEntropy_sub_eq`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The entropy of `P_θ` relative to the prior: `𝒮(θ) = −KL(P_θ ‖ π̄)`. -/
noncomputable def relEntropy (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (θ : Option ι → ℝ) : ℝ :=
  -mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (dirLoss (jointStat L₀ R) (0 - θ)) 1 0 1

omit [MeasurableSpace X] [Fintype ι] in
theorem natCoord_none (t : ℝ) (a : ι → ℝ) : natCoord t a none = t := rfl

omit [MeasurableSpace X] [Fintype ι] in
theorem natCoord_some (t : ℝ) (a : ι → ℝ) (i : ι) : natCoord t a (some i) = t * a i := rfl

theorem affLogZ_joint_zero (π L₀ : X → ℝ) (R : ι → X → ℝ) :
    affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 0 = Real.log (∫ x, π x ∂μ) := by
  unfold affLogZ priorZ
  simp [affLoss]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- `𝒮(θ) = ⟨θ, m(θ)⟩ + A(θ) − A(0)`. -/
theorem relEntropy_eq (θ : Option ι → ℝ) :
    relEntropy μ π L₀ R θ =
      ∑ j, θ j * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ j +
        affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ -
        affLogZ μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 0 := by
  unfold relEntropy
  rw [natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR θ 0]
  simp only [Pi.zero_apply, zero_sub, neg_mul, Finset.sum_neg_distrib]
  ring

/-- In the `(t, a)` chart: `𝒮 = t ⟨L₀⟩ + t ⟨a, m_t(a)⟩ + A_t(a) − log ∫π`. -/
theorem relEntropy_natCoord (t : ℝ) (a : ι → ℝ) :
    relEntropy μ π L₀ R (natCoord t a) =
      t * priorExp μ π (affLoss L₀ R a) L₀ t + t * ∑ i, a i * meanMap μ π L₀ R t a i +
        affLogZ μ π L₀ R t a - Real.log (∫ x, π x ∂μ) := by
  rw [relEntropy_eq hπm hπi hπ hπpos hL₀m hL₀ hR, Fintype.sum_option, affLogZ_joint_zero,
    affLogZ_natCoord, natCoord_none, meanMap_natCoord_none, Finset.mul_sum]
  simp only [natCoord_some, meanMap_natCoord_some, mul_assoc]

/-- The prior has zero relative entropy. -/
theorem relEntropy_zero : relEntropy μ π L₀ R 0 = 0 := by
  rw [relEntropy_eq hπm hπi hπ hπpos hL₀m hL₀ hR]
  simp

/-- **The prior maximises the relative entropy**: `𝒮(θ) ≤ 0`. -/
theorem relEntropy_nonpos (θ : Option ι → ℝ) : relEntropy μ π L₀ R θ ≤ 0 := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have := famKL_nonneg hπm hπi hπ hπpos measurable_const h0 hS' one_pos θ 0
  unfold famKL at this
  unfold relEntropy
  linarith

/-- **The differential of the relative entropy is `⟨θ, dm⟩ = −G_θ(θ, ·)`.** -/
theorem hasDerivAt_relEntropy_path {η : ℝ → Option ι → ℝ} {η' : Option ι → ℝ} {s : ℝ}
    (hη : HasDerivAt η η' s) :
    HasDerivAt (fun s ↦ relEntropy μ π L₀ R (η s)) (-natForm μ π L₀ R (η s) (η s) η') s := by
  have h := (hasDerivAt_natKL_path hπm hπi hπ hπpos hL₀m hL₀ hR 0 hη).neg
  refine h.congr_deriv ?_
  simp only [natForm, sub_zero]

/-- **The general entropy difference**: `𝒮(θ) − 𝒮(ϑ) = KL(P_ϑ ‖ P_θ) − ⟨θ, m(ϑ) − m(θ)⟩`. -/
theorem relEntropy_sub_eq (θ ϑ : Option ι → ℝ) :
    relEntropy μ π L₀ R θ - relEntropy μ π L₀ R ϑ =
      mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) ϑ) (dirLoss (jointStat L₀ R) (θ - ϑ))
          1 0 1 -
        ∑ j, θ j * (meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 ϑ j -
          meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ j) := by
  rw [relEntropy_eq hπm hπi hπ hπpos hL₀m hL₀ hR, relEntropy_eq hπm hπi hπ hπpos hL₀m hL₀ hR,
    natKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR ϑ θ]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **The featureless point is the maximum-relative-entropy member at its loss expectation**:
if `⟨L₀⟩_ϑ = ⟨L₀⟩_{t,0}` then `𝒮(t, 0) − 𝒮(ϑ) = KL(P_ϑ ‖ P_{t,0})`. -/
theorem relEntropy_featureless_sub (t : ℝ) (ϑ : Option ι → ℝ)
    (hE : meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 ϑ none =
      priorExp μ π (affLoss L₀ R 0) L₀ t) :
    relEntropy μ π L₀ R (natCoord t 0) - relEntropy μ π L₀ R ϑ =
      mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) ϑ)
        (dirLoss (jointStat L₀ R) (natCoord t 0 - ϑ)) 1 0 1 := by
  rw [relEntropy_sub_eq hπm hπi hπ hπpos hL₀m hL₀ hR, Fintype.sum_option, natCoord_none,
    meanMap_natCoord_none, hE]
  simp [natCoord_some]

/-- `𝒮(ϑ) ≤ 𝒮(t, 0)` for every member with the same loss expectation as the featureless point. -/
theorem relEntropy_le_featureless (t : ℝ) (ϑ : Option ι → ℝ)
    (hE : meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 ϑ none =
      priorExp μ π (affLoss L₀ R 0) L₀ t) :
    relEntropy μ π L₀ R ϑ ≤ relEntropy μ π L₀ R (natCoord t 0) := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have h := relEntropy_featureless_sub hπm hπi hπ hπpos hL₀m hL₀ hR t ϑ hE
  have hk := famKL_nonneg hπm hπi hπ hπpos measurable_const h0 hS' one_pos ϑ (natCoord t 0)
  unfold famKL at hk
  linarith

section Chart

variable (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  [Nonempty ι] [DecidableEq ι]
include hnd

/-- **Along the temperature path at fixed response the relative entropy decreases at the rate
`t Var(H)`**, `H = L₀ − b·R` the residual. -/
theorem hasDerivAt_relEntropy_temp {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ relEntropy μ π L₀ R (tempPath μ π L₀ R M t))
      (-(t₀ * priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t₀) M))
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t₀) x) t₀)) t₀ := by
  set a := Function.invFun (meanMap μ π L₀ R t₀) M with ha
  set b := regCoeff μ π L₀ R M t₀ with hb
  have hθ : tempPath μ π L₀ R M t₀ = natCoord t₀ a :=
    tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
  have hCb : (featCov μ π L₀ R t₀ a).mulVec b = featObsCov μ π L₀ R t₀ a L₀ :=
    featCov_mulVec_regCoeff hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ M
  have hH : Bdd fun x ↦ L₀ x - dirLoss R b x := Bdd.sub ⟨hL₀m, M₀, hL₀⟩ (bdd_dirLoss hR b)
  have h := hasDerivAt_relEntropy_path hπm hπi hπ hπpos hL₀m hL₀ hR
    (hasDerivAt_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM)
  refine h.congr_deriv ?_
  unfold natForm
  rw [dirLoss_jointStat_velocity hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM, hθ, priorCov_natCoord]
  have hSθ : dirLoss (jointStat L₀ R) (natCoord t₀ a) = fun x ↦ t₀ * affLoss L₀ R a x :=
    funext fun x ↦ dirLoss_jointStat_natCoord L₀ R t₀ a x
  have e : priorCov μ π (affLoss L₀ R a) (fun x ↦ L₀ x - dirLoss R b x) (affLoss L₀ R a) t₀ =
      priorCov μ π (affLoss L₀ R a) (fun x ↦ L₀ x - dirLoss R b x)
        (fun x ↦ L₀ x + dirLoss R a x) t₀ := rfl
  have hL : priorCov μ π (affLoss L₀ R a) (fun x ↦ L₀ x - dirLoss R b x)
        (fun x ↦ L₀ x - dirLoss R b x) t₀ =
      priorCov μ π (affLoss L₀ R a) (fun x ↦ L₀ x - dirLoss R b x) L₀ t₀ := by
    rw [priorCov_sub_right hπm hπi hπ hπpos hL₀m hL₀ hR a ⟨hL₀m, M₀, hL₀⟩ (bdd_dirLoss hR b) hH,
      priorCov_residual_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR a hCb b, sub_zero]
  rw [hSθ, priorCov_const_mul_left, priorCov_comm π _ (affLoss L₀ R a) _ t₀, e,
    priorCov_add_right_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a ⟨hL₀m, M₀, hL₀⟩ (bdd_dirLoss hR a) hH,
    priorCov_residual_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR a hCb a, add_zero, hL]

end Chart

end

end Laplace.Multi
