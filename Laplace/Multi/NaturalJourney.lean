/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ArcsineLength
import Laplace.Multi.RelativeEntropyGeometry
import Laplace.Multi.HalfspaceProjection

/-!
# The journey from the prior to the data

The **natural ray** `s ↦ s θ`, `s ∈ [0, 1]`, joins the prior `π̄` (natural coordinate `0`, the
genuinely featureless distribution of maximal relative entropy) to the member `P_θ`; for the data
member `θ = (t, t a)`. Along it, with `G_s = G_{sθ}(θ, θ)` the Fisher speed squared:

* the information acquired is `KL(P_θ ‖ π̄) = ∫₀¹ s G_s ds` and the relative entropy is its negative
  (`relEntropy_natRay_eq_integral`);
* the relative entropy decreases monotonically, `d/ds 𝒮(sθ) = −s G_s ≤ 0`
  (`hasDerivAt_relEntropy_natRay`, `relEntropy_natRay_antitoneOn`);
* the Fisher length is `∫₀¹ √G_s ds`, and every bounded observable moves by at most `(hi − lo)/2`
  times it (`abs_priorExp_sub_le_natRay`), with the arcsine sharpening (`natRay_ge_arcsin`).

The alternative **two-leg journey** `π̄ → P_{t,0} → P_{t,a}` (anneal to the zero-field member at
temperature `t`, then move the data) accounts for the information as
`𝒮(t, a) = 𝒮(t, 0) − KL(P_{t,a} ‖ P_{t,0}) + t (⟨L₀⟩_{t,a} − ⟨L₀⟩_{t,0})`
(`relEntropy_natCoord_decomp`): the entropy of the data member relative to the prior is that of the
featureless member at the same temperature, minus the information needed to move the data, plus the
temperature times the excess loss of the data over the featureless point. Note `P_{t,0} ≠ π̄` unless
the loss is constant: the featureless point at temperature `t` is not the maximal-entropy prior.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

omit [MeasurableSpace X] in
set_option linter.unusedFintypeInType false in
theorem hasDerivAt_natRay (θ : Option ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ s • θ) θ s := by
  simpa using (hasDerivAt_id s).smul_const θ

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- **The information acquired along the natural ray**: `KL(P_θ ‖ π̄) = ∫₀¹ s G_{sθ}(θ, θ) ds`, i.e.
`𝒮(θ) = −∫₀¹ s G_{sθ}(θ, θ) ds`. -/
theorem relEntropy_natRay_eq_integral (θ : Option ι → ℝ) :
    relEntropy μ π L₀ R θ = -∫ s in (0 : ℝ)..1, s * natForm μ π L₀ R (s • θ) θ θ := by
  have h := natKL_segment_eq_integral hπm hπi hπ hπpos hL₀m hL₀ hR 0 θ
  simp only [zero_add] at h
  unfold relEntropy natForm
  rw [h]

/-- **The relative entropy decreases along the natural ray**: `d/ds 𝒮(sθ) = −s G_{sθ}(θ, θ)`. -/
theorem hasDerivAt_relEntropy_natRay (θ : Option ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ relEntropy μ π L₀ R (s • θ))
      (-(s * natForm μ π L₀ R (s • θ) θ θ)) s := by
  have h := hasDerivAt_relEntropy_path hπm hπi hπ hπpos hL₀m hL₀ hR (hasDerivAt_natRay θ s)
  refine h.congr_deriv ?_
  unfold natForm
  rw [dirLoss_smul, priorCov_const_mul_left]

theorem relEntropy_natRay_antitoneOn (θ : Option ι → ℝ) :
    AntitoneOn (fun s : ℝ ↦ relEntropy μ π L₀ R (s • θ)) (Ici 0) := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · exact (continuous_iff_continuousAt.2 fun s ↦
      (hasDerivAt_relEntropy_natRay hπm hπi hπ hπpos hL₀m hL₀ hR θ s).continuousAt).continuousOn
  · exact fun s _ ↦ (hasDerivAt_relEntropy_natRay hπm hπi hπ hπpos hL₀m hL₀ hR θ
      s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    rw [(hasDerivAt_relEntropy_natRay hπm hπi hπ hπpos hL₀m hL₀ hR θ s).deriv, neg_nonpos]
    exact mul_nonneg (le_of_lt hs)
      (priorCov_self_nonneg' hπm hπi hπ hπpos measurable_const h0 hS' (t := 1) (s • θ)
        (bdd_dirLoss hS' θ))

/-- **Observables move at most `(hi − lo)/2` times the Fisher length of the natural ray.** -/
theorem abs_priorExp_sub_le_natRay (θ : Option ι → ℝ) {φ : X → ℝ} (hφ : Bdd φ) {lo hi : ℝ}
    (hlo : ∀ x, lo ≤ φ x) (hhi : ∀ x, φ x ≤ hi) :
    |priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) φ 1 -
        priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 0) φ 1| ≤
      (hi - lo) / 2 * natLength μ π L₀ R (fun s ↦ s • θ) (fun _ ↦ θ) := by
  have := abs_priorExp_sub_le_natLength hπm hπi hπ hπpos hL₀m hL₀ hR (hasDerivAt_natRay θ)
    continuous_const hφ hlo hhi
  simpa only [one_smul, zero_smul] using this

/-- **The arcsine bound along the natural ray.** -/
theorem natRay_ge_arcsin (θ : Option ι → ℝ) {φ : X → ℝ} (hφ : Bdd φ) {lo hi : ℝ}
    (hlo : ∀ x, lo ≤ φ x) (hhi : ∀ x, φ x ≤ hi)
    (hint : ∀ s : ℝ, lo < priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (s • θ)) φ 1 ∧
      priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (s • θ)) φ 1 < hi) :
    2 * |Real.arcsin (Real.sqrt
        ((priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) φ 1 - lo) / (hi - lo))) -
      Real.arcsin (Real.sqrt
        ((priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 0) φ 1 - lo) / (hi - lo)))|
      ≤ natLength μ π L₀ R (fun s ↦ s • θ) (fun _ ↦ θ) := by
  have := natLength_ge_arcsin hπm hπi hπ hπpos hL₀m hL₀ hR (hasDerivAt_natRay θ) continuous_const
    hφ hlo hhi hint
  simpa only [one_smul, zero_smul] using this

/-- **The two-leg journey**:
`𝒮(t, a) = 𝒮(t, 0) − KL(P_{t,a} ‖ P_{t,0}) + t (⟨L₀⟩_{t,a} − ⟨L₀⟩_{t,0})`. -/
theorem relEntropy_natCoord_decomp (t : ℝ) (a : ι → ℝ) :
    relEntropy μ π L₀ R (natCoord t a) =
      relEntropy μ π L₀ R (natCoord t 0) - famKL μ π L₀ R t a 0 +
        t * (priorExp μ π (affLoss L₀ R a) L₀ t - priorExp μ π (affLoss L₀ R 0) L₀ t) := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have h3 := mixKL_three_point hπm hπi hπ hπpos measurable_const h0 hS' (t := 1) (natCoord t a) 0
    (natCoord t 0)
  rw [Fintype.sum_option] at h3
  simp only [Pi.zero_apply, natCoord_none, natCoord_some, meanMap_natCoord_none, mul_zero,
    sub_zero, zero_sub, zero_mul, Finset.sum_const_zero, add_zero, one_mul] at h3
  have hfam : mixKL μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (natCoord t a))
      (dirLoss (jointStat L₀ R) (natCoord t 0 - natCoord t a)) 1 0 1 = famKL μ π L₀ R t a 0 := by
    rw [natKL_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR]
    rfl
  rw [hfam] at h3
  unfold relEntropy
  simp only [zero_sub]
  linarith

end

end Laplace.Multi
