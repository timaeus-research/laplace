/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FamilyBregman
import Laplace.Multi.HalfspaceProjection
import Laplace.Multi.DualPotential
import Laplace.Multi.DualFlat
import Laplace.Multi.CovarianceFrechet
import Laplace.Multi.ResponseTransport
import Laplace.Multi.StraightPathAtlas

/-!
# The atlas is the natural-gradient flow toward the data

Fix an interior target response `M*` and the loss `L(M) = KL(Q_{M*} ‖ Q_M)` in response coordinates.
Its differential is the Fisher pairing with the displacement, `dL_M[u] = g_M(M − M*, u)`
(`hasFDerivAt_natLoss`, `natLoss_deriv_eq_fisherForm`), so the Fisher (natural) gradient of `L`
is `M − M*`. The negative natural-gradient flow started at the featureless response is the
straight atlas with the time change `s = 1 − e^{−τ}`, `M(τ) = m₀ + (1 − e^{−τ})(M* − m₀)`
(`natFlow`, `hasDerivAt_natFlow`), it converges to the target (`tendsto_natFlow`), and it dissipates
the loss at the squared Fisher speed, `d/dτ L(M(τ)) = −g_{M(τ)}(M(τ) − M*, M(τ) − M*)`
(`hasDerivAt_natLoss_natFlow`): the path from the featureless law to the data is a natural-gradient
learning trajectory.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The log-partition function in natural coordinates. -/
local notation "A" => affLogZ ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

variable (Mt : J → ℝ)

/-- **The natural loss** of a response relative to the target: `L(M) = KL(Q_{M*} ‖ Q_M)`. -/
noncomputable def natLoss (M : J → ℝ) : ℝ := (klDiv (Pfam (θr Mt)) (Pfam (θr M))).toReal

/-- The Bregman form of the natural loss: `L(M) = A(θ(M)) − A(θ*) + ⟨θ(M) − θ*, M*⟩`. -/
theorem natLoss_eq (hrel : Mt ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (M : J → ℝ) :
    natLoss hS ν Mt M = A (θr M : J → ℝ) - A (θr Mt : J → ℝ) +
      dotJ ((θr M : J → ℝ) - (θr Mt : J → ℝ)) Mt := by
  unfold natLoss
  rw [klDiv_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS one_pos,
    ENNReal.toReal_ofReal (famKL_nonneg measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS one_pos _ _),
    famKL_eq measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      measurable_const (M₀ := 0) (fun _ ↦ by simp) hS,
    meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel]
  simp only [one_mul, dotJ, Pi.sub_apply]

/-- **The differential of the natural loss** at an interior response, in the direction space:
`dL_M[u] = ⟨R_M u, M* − M⟩`. -/
theorem hasFDerivAt_natLoss (hrel : Mt ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {M : J → ℝ} (hM : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasFDerivAt (fun z : 𝕍 ↦ natLoss hS ν Mt (M + z))
      ((dotCLM (Mt - M)).comp ((𝕍).subtypeL.comp
        (ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍))) 0 := by
  have hθ := hasFDerivAt_responseTheta_add_coe hS ν hM
  have h0 : M + ((0 : 𝕍) : J → ℝ) = M := by simp
  have hA0 := hasFDerivAt_affLogZ (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ)) (R := S)
    (t := 1) measurable_const (integrable_const 1) (fun _ ↦ zero_le_one) (one_integral_pos ν)
    measurable_const (M₀ := 0) (fun _ ↦ by simp) hS one_pos
    (θr (M + ((0 : 𝕍) : J → ℝ)) : J → ℝ)
  have hA := hA0.comp (0 : 𝕍) hθ
  simp only [h0] at hA
  rw [meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hM] at hA
  have hB := (dotCLM Mt).hasFDerivAt.comp (0 : 𝕍) hθ
  have h := (hA.sub_const (A (θr Mt : J → ℝ))).add (hB.sub_const (dotCLM Mt (θr Mt : J → ℝ)))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)).congr_fderiv ?_
  · rw [natLoss_eq hS ν Mt hrel]
    simp only [Function.comp_def, dotCLM_apply, dotJ, Pi.sub_apply, sub_mul,
      Finset.sum_sub_distrib, Pi.add_apply]
  · ext u
    simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, dotCLM_apply, dotJ,
      Pi.sub_apply, smul_eq_mul, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    simp only [neg_one_mul, Finset.sum_neg_distrib]
    ring

/-- The Fisher form is odd in its second argument. -/
theorem fisherForm_neg_right {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (u w : 𝕍) :
    fisherForm hS ν M u (-w) = -fisherForm hS ν M u w := by
  rw [fisherForm_eq_neg_dotJ hS ν hM, fisherForm_eq_neg_dotJ hS ν hM, Submodule.coe_neg,
    dotJ_comm, dotJ_neg_left, dotJ_comm]

/-- **The natural gradient of the loss is the displacement**: `dL_M[u] = g_M(M − M*, u)`. -/
theorem natLoss_deriv_eq_fisherForm
    (hrel : Mt ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {M : J → ℝ} (hM : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (u : 𝕍) :
    ((dotCLM (Mt - M)).comp ((𝕍).subtypeL.comp
        (ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍))) u =
      fisherForm hS ν M ⟨M - Mt, sub_mem_dirSpan_of_mem_momentBody' hS ν
        (intrinsicInterior_subset hrel) (intrinsicInterior_subset hM)⟩ u := by
  rw [fisherForm_eq_neg_dotJ hS ν hM, dotJ_inverse_chart_symm hS ν hM]
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLM_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [show Mt - M = -(M - Mt) by abel, dotJ_comm, dotJ_neg_left, dotJ_comm]

variable (S) in
/-- **The natural-gradient flow** from the featureless response toward the target:
`M(τ) = m₀ + (1 − e^{−τ})(M* − m₀)`, the straight atlas with the time change `s = 1 − e^{−τ}`. -/
noncomputable def natFlow (τ : ℝ) : J → ℝ := atlasPath S ν Mt (1 - Real.exp (-τ))

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem natFlow_zero : natFlow S ν Mt 0 = m₀ := by
  simp [natFlow, atlasPath]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The flow solves `M' = −(M − M*)`: minus the natural gradient of the loss. -/
theorem hasDerivAt_natFlow (τ : ℝ) :
    HasDerivAt (natFlow S ν Mt) (-(natFlow S ν Mt τ - Mt)) τ := by
  have h1 : HasDerivAt (fun τ ↦ 1 - Real.exp (-τ)) (Real.exp (-τ)) τ := by
    have := ((hasDerivAt_id τ).neg.exp).const_sub (1 : ℝ)
    refine this.congr_deriv ?_
    simp
  have h2 := (hasDerivAt_atlasPath ν (S := S) (M := Mt) (1 - Real.exp (-τ))).scomp τ h1
  refine h2.congr_deriv ?_
  simp only [natFlow, atlasPath]
  module

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The flow converges to the target. -/
theorem tendsto_natFlow : Tendsto (natFlow S ν Mt) atTop (𝓝 Mt) := by
  have h1 : Tendsto (fun τ : ℝ ↦ 1 - Real.exp (-τ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using this
  have h2 := (hasDerivAt_atlasPath ν (S := S) (M := Mt) 1).continuousAt.tendsto.comp h1
  rw [atlasPath_one] at h2
  exact h2

/-- The flow stays in the interior for `τ ≥ 0`. -/
theorem natFlow_mem_intrinsicInterior
    (hrel : Mt ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {τ : ℝ} (hτ : 0 ≤ τ) :
    natFlow S ν Mt τ ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  refine atlas_mem_intrinsicInterior hS ν hfin ?_ ?_
  · have : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  · linarith [Real.exp_pos (-τ)]

/-- **Dissipation along the natural-gradient flow**: for `τ ≥ 0`,
`d/dτ L(M(τ)) = −g_{M(τ)}(M(τ) − M*, M(τ) − M*)`, the squared Fisher speed. -/
theorem hasDerivAt_natLoss_natFlow
    (hrel : Mt ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasDerivAt (fun τ ↦ natLoss hS ν Mt (natFlow S ν Mt τ))
      (-fisherForm hS ν (natFlow S ν Mt τ)
        ⟨natFlow S ν Mt τ - Mt, sub_mem_dirSpan_of_mem_momentBody' hS ν
          (intrinsicInterior_subset hrel)
          (intrinsicInterior_subset (natFlow_mem_intrinsicInterior hS ν Mt hrel hτ))⟩
        ⟨natFlow S ν Mt τ - Mt, sub_mem_dirSpan_of_mem_momentBody' hS ν
          (intrinsicInterior_subset hrel)
          (intrinsicInterior_subset (natFlow_mem_intrinsicInterior hS ν Mt hrel hτ))⟩) τ := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  have hM := natFlow_mem_intrinsicInterior hS ν Mt hrel hτ
  have hV : ∀ s, natFlow S ν Mt s - natFlow S ν Mt τ ∈ 𝕍 := fun s ↦ by
    have h1 := atlasPath_sub_mem_dirSpan hS ν hfin (1 - Real.exp (-s))
    have h2 := atlasPath_sub_mem_dirSpan hS ν hfin (1 - Real.exp (-τ))
    have := (dirSpan ν (fun _ ↦ (1 : ℝ)) S).sub_mem h1 h2
    rwa [sub_sub_sub_cancel_right] at this
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → 𝕍, ∀ s, (γ s : J → ℝ) = natFlow S ν Mt s - natFlow S ν Mt τ :=
    ⟨fun s ↦ ⟨_, hV s⟩, fun s ↦ rfl⟩
  have hmem : -(natFlow S ν Mt τ - Mt) ∈ 𝕍 := by
    have := sub_mem_dirSpan_of_mem_momentBody' hS ν (intrinsicInterior_subset hrel)
      (intrinsicInterior_subset hM)
    exact (dirSpan ν (fun _ ↦ (1 : ℝ)) S).neg_mem this
  have hγd : HasDerivAt γ ⟨-(natFlow S ν Mt τ - Mt), hmem⟩ τ := by
    refine hasDerivAt_subtype_of_hasDerivAt hmem ?_
    simp only [hγ]
    exact (hasDerivAt_natFlow ν Mt τ).sub_const _
  have e : ∀ s, natFlow S ν Mt τ + (γ s : J → ℝ) = natFlow S ν Mt s := fun s ↦ by
    rw [hγ s, add_sub_cancel]
  have hz : γ τ = 0 := by
    apply Subtype.ext
    rw [hγ τ, sub_self]
    rfl
  have h := hasFDerivAt_natLoss hS ν Mt hrel hM
  rw [← hz] at h
  have h2 := h.comp_hasDerivAt τ hγd
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp only [Function.comp_def, e]
  · rw [natLoss_deriv_eq_fisherForm hS ν Mt hrel hM]
    have : (⟨-(natFlow S ν Mt τ - Mt), hmem⟩ : 𝕍) = -⟨natFlow S ν Mt τ - Mt,
        sub_mem_dirSpan_of_mem_momentBody' hS ν (intrinsicInterior_subset hrel)
          (intrinsicInterior_subset hM)⟩ := rfl
    rw [this, fisherForm_neg_right hS ν hM]

end Laplace.Multi
