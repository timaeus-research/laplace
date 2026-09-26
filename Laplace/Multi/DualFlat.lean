/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseTaylor

/-!
# The dual-flat structure of the response map

In response coordinates the rate `𝓘` is a potential for the natural coordinate, `∇𝓘(M) = −θ(M)`
(`hasFDerivAt_genRate_response`), its Hessian is the Fisher metric of the family
`G_M(u,w) = E_Q[ℓ_{M,u} ℓ_{M,w}]` (`hasFDerivAt_neg_dotJ_responseTheta`), and the derivative of
the Fisher metric is minus the cubic score tensor `C_M(u,v,w) = E_Q[ℓ_{M,u} ℓ_{M,v} ℓ_{M,w}]`
(`hasFDerivAt_fisherForm_response`), which is totally symmetric (`cubicScore_symm`). Together with
the
canonical divergence `KL(Π(M)‖Π(M')) = 𝓘(M) − 𝓘(M') + ⟨θ(M'), M − M'⟩` these are the identities of
a dually flat structure: the response chart is the mixture-flat coordinate, the natural
coordinate is the exponential-flat one, and the cubic tensor is the difference of the two affine
connections
(`dual_flat_structure`).
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section DualFlat

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

include hS

/-- **The Fisher form** in response coordinates, `G_M(u,w) = E_{Π(M)}[ℓ_{M,u} ℓ_{M,w}]`. -/
noncomputable def fisherForm (M : J → ℝ) (u w : 𝕍) : ℝ :=
  ∫ x, responseScore hS ν M u x * responseScore hS ν M w x ∂(Pfam (θr M))

/-- **The cubic score tensor** `C_M(u,v,w) = E_{Π(M)}[ℓ_{M,u} ℓ_{M,v} ℓ_{M,w}]`. -/
noncomputable def cubicScore (M : J → ℝ) (u v w : 𝕍) : ℝ :=
  ∫ x, responseScore hS ν M u x * responseScore hS ν M v x * responseScore hS ν M w x
    ∂(Pfam (θr M))

variable {M : J → ℝ}

theorem fisherForm_comm (u w : 𝕍) : fisherForm hS ν M u w = fisherForm hS ν M w u :=
  integral_congr_ae (Eventually.of_forall fun _ ↦ mul_comm _ _)

/-- The cubic tensor is totally symmetric. -/
theorem cubicScore_symm (u v w : 𝕍) :
    cubicScore hS ν M u v w = cubicScore hS ν M v u w ∧
      cubicScore hS ν M u v w = cubicScore hS ν M u w v := by
  constructor
  · exact integral_congr_ae (Eventually.of_forall fun x ↦ by beta_reduce; ring)
  · exact integral_congr_ae (Eventually.of_forall fun x ↦ by beta_reduce; ring)

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- Differential duality in the Fisher form: `G_M(u,w) = −⟨R u, w⟩`. -/
theorem fisherForm_eq_neg_dotJ (u w : 𝕍) :
    fisherForm hS ν M u w = -dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ) w :=
  integral_responseScore_mul hS ν hrel u w

/-- **The rate is a potential for the natural coordinate**: `D𝓘(M)[u] = −⟨θ(M), u⟩`. -/
theorem hasFDerivAt_genRate_response :
    HasFDerivAt (fun z : 𝕍 ↦ (genRate ν S (M + z)).toReal)
      (-(dotCLM (θr M : J → ℝ)).comp (𝕍).subtypeL) 0 := by
  have h := hasFDerivAt_genRate_response_at hS ν (z₀ := 0) (by simpa using hrel)
  simpa using h

/-- **The Hessian of the rate is the Fisher form**: the derivative field `z ↦ −⟨θ(M+z), u⟩` of the
rate has derivative `w ↦ G_M(u,w)` at `0`. -/
theorem hasFDerivAt_neg_dotJ_responseTheta (u : 𝕍) :
    ∃ L : 𝕍 →L[ℝ] ℝ, HasFDerivAt (fun z : 𝕍 ↦ -dotJ (θr (M + z) : J → ℝ) u) L 0 ∧
      ∀ w, L w = fisherForm hS ν M u w := by
  have hΘ := hasFDerivAt_responseTheta_add_coe hS ν hrel
  have h := ((dotCLM (u : J → ℝ)).hasFDerivAt.comp (0 : 𝕍) hΘ).neg
  refine ⟨_, h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_), fun w ↦ ?_⟩
  · simp only [Function.comp_def, dotCLM_apply, Pi.neg_apply]
  · rw [fisherForm_comm, fisherForm_eq_neg_dotJ hS ν hrel]
    simp only [neg_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLM_apply,
      ContinuousLinearEquiv.coe_coe]

/-- The normal part of an observable is orthogonal to every response score. -/
theorem integral_normalProj_mul_responseScore {f : X → ℝ} (hf : Bdd f) (w : 𝕍) :
    ∫ x, normalProj hS ν M hf x * responseScore hS ν M w x ∂(Pfam (θr M)) = 0 := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hj : ∀ j, ∫ x, normalProj hS ν M hf x * S j x ∂(Pfam (θr M)) = 0 := fun j ↦ by
    refine (integral_congr_ae (Eventually.of_forall fun x ↦ ?_)).trans
      (integral_stat_mul_normalProj hS ν hrel hf j)
    exact mul_comm _ _
  simp only [responseScore_apply]
  rw [integral_mul_sub_dirLoss hS _ (bdd_normalProj hS ν hf), integral_normalProj hS ν hrel]
  simp only [hj, mul_zero, Finset.sum_const_zero, sub_zero]

/-- The regression projection is the `L²(Q)`-orthogonal projection onto the tangent scores:
`E_Q[(B_M f) ℓ_{M,w}] = E_Q[f ℓ_{M,w}]`. -/
theorem integral_regProj_mul_responseScore {f : X → ℝ} (hf : Bdd f) (w : 𝕍) :
    ∫ x, regProj hS ν M hf x * responseScore hS ν M w x ∂(Pfam (θr M)) =
      ∫ x, f x * responseScore hS ν M w x ∂(Pfam (θr M)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hN := integral_normalProj_mul_responseScore hS ν hrel hf w
  have h0 := integral_responseScore hS ν hrel w
  have i1 : Integrable (fun x ↦ f x * responseScore hS ν M w x) (Pfam (θr M)) :=
    integrable_of_bdd_prob _ (hf.mul (bdd_responseScore hS ν M w))
  have i2 : Integrable (fun x ↦ (∫ y, f y ∂(Pfam (θr M))) * responseScore hS ν M w x)
      (Pfam (θr M)) := (integrable_of_bdd_prob _ (bdd_responseScore hS ν M w)).const_mul _
  have i3 : Integrable (fun x ↦ regProj hS ν M hf x * responseScore hS ν M w x) (Pfam (θr M)) :=
    integrable_of_bdd_prob _ ((bdd_responseScore hS ν M _).mul (bdd_responseScore hS ν M w))
  have i12 : Integrable (fun x ↦ f x * responseScore hS ν M w x -
      (∫ y, f y ∂(Pfam (θr M))) * responseScore hS ν M w x) (Pfam (θr M)) := i1.sub i2
  have e : (fun x ↦ normalProj hS ν M hf x * responseScore hS ν M w x) = fun x ↦
      (f x * responseScore hS ν M w x - (∫ y, f y ∂(Pfam (θr M))) * responseScore hS ν M w x) -
        regProj hS ν M hf x * responseScore hS ν M w x := by
    funext x
    unfold normalProj
    ring
  rw [e, integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, h0, mul_zero, sub_zero] at hN
  linarith

/-- **The derivative of the Fisher form is minus the cubic tensor**: the field `z ↦ −⟨R_{M+z} u, w⟩`
(the Fisher form `G_{M+z}(u,w)` at interior points) has derivative `v ↦ −C_M(u,v,w)` at `0`. -/
theorem hasFDerivAt_fisherForm_response (u w : 𝕍) :
    ∃ L : 𝕍 →L[ℝ] ℝ,
      HasFDerivAt (fun z : 𝕍 ↦ -dotJ (ContinuousLinearEquiv.symm (CDE (θr (M + z))) u : J → ℝ) w)
        L 0 ∧
      ∀ v, L v = -cubicScore hS ν M u v w := by
  have hR := hasFDerivAt_inverse_response_apply hS ν hrel u
  have hRc := (𝕍).subtypeL.hasFDerivAt.comp 0 hR
  have h := ((dotCLM (w : J → ℝ)).hasFDerivAt.comp (0 : 𝕍) hRc).neg
  refine ⟨_, h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_), fun v ↦ ?_⟩
  · simp only [Function.comp_def, dotCLM_apply, Submodule.subtypeL_apply, Pi.neg_apply]
  · have hb := (bdd_responseScore hS ν M v).mul (bdd_responseScore hS ν M u)
    have hT : thirdOp hS ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) v)
        (ContinuousLinearEquiv.symm (CDE (θr M)) u) =
        ⟨respCov hS ν M (fun x ↦ responseScore hS ν M v x * responseScore hS ν M u x),
          respCov_mem_dirSpan hS ν hb⟩ :=
      Subtype.ext (by rw [thirdOp_coe_apply, thirdVec_eq_respCov hS ν hrel])
    simp only [neg_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLM_apply,
      inverse_response_deriv_apply, hT, Submodule.coe_neg, dotJ_neg_left, neg_neg]
    have hf := fisherForm_eq_neg_dotJ hS ν hrel
      ⟨respCov hS ν M (fun x ↦ responseScore hS ν M v x * responseScore hS ν M u x),
        respCov_mem_dirSpan hS ν hb⟩ w
    have hF : fisherForm hS ν M
        ⟨respCov hS ν M (fun x ↦ responseScore hS ν M v x * responseScore hS ν M u x),
          respCov_mem_dirSpan hS ν hb⟩ w = cubicScore hS ν M u v w := by
      unfold fisherForm cubicScore
      have := integral_regProj_mul_responseScore hS ν hrel hb w
      unfold regProj at this
      rw [this]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by beta_reduce; ring)
    linarith

/-- **The dual-flat structure of the response map**: the rate is a potential for the natural
coordinate, its Hessian is the Fisher form, the derivative of the Fisher form is minus the totally
symmetric cubic tensor, and the canonical divergence is the Bregman divergence of the rate. -/
theorem dual_flat_structure :
    HasFDerivAt (fun z : 𝕍 ↦ (genRate ν S (M + z)).toReal)
        (-(dotCLM (θr M : J → ℝ)).comp (𝕍).subtypeL) 0 ∧
      (∀ u : 𝕍, ∃ L : 𝕍 →L[ℝ] ℝ, HasFDerivAt (fun z : 𝕍 ↦ -dotJ (θr (M + z) : J → ℝ) u) L 0 ∧
        ∀ w, L w = fisherForm hS ν M u w) ∧
      (∀ u w : 𝕍, ∃ L : 𝕍 →L[ℝ] ℝ, HasFDerivAt
        (fun z : 𝕍 ↦ -dotJ (ContinuousLinearEquiv.symm (CDE (θr (M + z))) u : J → ℝ) w) L 0 ∧
        ∀ v, L v = -cubicScore hS ν M u v w) ∧
      (∀ u v w : 𝕍, cubicScore hS ν M u v w = cubicScore hS ν M v u w ∧
        cubicScore hS ν M u v w = cubicScore hS ν M u w v) ∧
      ∀ M' ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S),
        (klDiv (responseProjection hS ν M) (responseProjection hS ν M')).toReal =
          (genRate ν S M).toReal - (genRate ν S M').toReal + dotJ (θr M' : J → ℝ) (M - M') :=
  ⟨hasFDerivAt_genRate_response hS ν hrel, hasFDerivAt_neg_dotJ_responseTheta hS ν hrel,
    hasFDerivAt_fisherForm_response hS ν hrel, cubicScore_symm hS ν, fun _ hM' ↦
      toReal_klDiv_responseProjection_interior hS ν
        (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel) hM'⟩

end DualFlat

end Laplace.Multi
