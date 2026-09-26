/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovarianceFrechet

/-!
# The observable defect to second order

For a bounded observable `φ`, the response map `M ↦ E_{Π(M)} φ` is differentiable in response
coordinates with derivative `u ↦ E_Q[φ ℓ_{M,u}] = Cov_Q(φ, ℓ_{M,u})`
(`hasFDerivAt_integral_response`), and the derivative field `z ↦ E_{Π(M+z)}[φ ℓ_{M+z,w}]` is
differentiable at `z = 0` with derivative

`u ↦ E_Q[φ · N_M(ℓ_{M,u} ℓ_{M,w})]` (`hasFDerivAt_integral_responseScore`):

the second derivative of an observable's response is its pairing with the normal projection of the
product of the two response scores. Since `N_M` kills constants and tangent scores, the second-order
response of `φ` depends only on the normal part of `φ`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Observable

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {M : J → ℝ}

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

/-- The inverse chart derivative at `M`, as a continuous linear map. -/
local notation "RinvL" => (ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍)

include hS

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- `∫ ψ ⟨v,S⟩ = ∑ⱼ vⱼ ∫ ψ Sⱼ`. -/
theorem integral_mul_dirLoss (ρ : Measure X) [IsProbabilityMeasure ρ] {ψ : X → ℝ} (hψ : Bdd ψ)
    (v : J → ℝ) : ∫ x, ψ x * dirLoss S v x ∂ρ = ∑ j, v j * ∫ x, ψ x * S j x ∂ρ := by
  simp only [dirLoss, Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ ↦ ((integrable_of_bdd_prob ρ (hψ.mul (hS j))).const_mul
    (v j)).congr (Eventually.of_forall fun x ↦ by ring)]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- `∫ ψ (a − ⟨v,S⟩) = a ∫ ψ − ∑ⱼ vⱼ ∫ ψ Sⱼ`. -/
theorem integral_mul_sub_dirLoss (ρ : Measure X) [IsProbabilityMeasure ρ] {ψ : X → ℝ}
    (hψ : Bdd ψ) (a : ℝ) (v : J → ℝ) :
    ∫ x, ψ x * (a - dirLoss S v x) ∂ρ = a * (∫ x, ψ x ∂ρ) - ∑ j, v j * ∫ x, ψ x * S j x ∂ρ := by
  have h1 : Integrable (fun x ↦ ψ x * a) ρ := (integrable_of_bdd_prob ρ hψ).mul_const a
  have h2 : Integrable (fun x ↦ ψ x * dirLoss S v x) ρ :=
    integrable_of_bdd_prob ρ (hψ.mul (bdd_dirLoss hS v))
  have e : (fun x ↦ ψ x * (a - dirLoss S v x)) = fun x ↦ ψ x * a - ψ x * dirLoss S v x :=
    funext fun x ↦ by ring
  rw [e, integral_sub h1 h2, integral_mul_const, mul_comm, integral_mul_dirLoss hS ρ hψ v]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem hasFDerivAt_dotCLM_add :
    HasFDerivAt (fun z : 𝕍 ↦ dotCLM (M + (z : J → ℝ))) (dotCLMlin.comp (𝕍).subtypeL) 0 := by
  have := (dotCLMlin.comp (𝕍).subtypeL).hasFDerivAt (x := (0 : 𝕍)) |>.const_add (dotCLM M)
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLMlin_apply, dotCLM_add]

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The response of a bounded observable is differentiable in response coordinates.** -/
theorem hasFDerivAt_integral_response {φ : X → ℝ} (hφ : Bdd φ) :
    HasFDerivAt (fun z : 𝕍 ↦ ∫ x, φ x ∂(Pfam (θr (M + z))))
      ((covCLM S (Pfam (θr M)) φ).comp ((𝕍).subtypeL.comp RinvL)) 0 := by
  have hΘ := hasFDerivAt_responseTheta_add_coe hS ν hrel
  have h := (hasFDerivAt_integral_family hS ν hφ (θr (M + (0 : 𝕍)) : J → ℝ)).comp (0 : 𝕍) hΘ
  have h0 : ((θr (M + (0 : 𝕍)) : J → ℝ)) = (θr M : J → ℝ) := by simp
  rw [h0] at h
  exact h

/-- The first derivative of the response of `φ` is `E_Q[φ ℓ_{M,u}] = Cov_Q(φ, ℓ_{M,u})`. -/
theorem integral_response_deriv_apply {φ : X → ℝ} (hφ : Bdd φ) (u : 𝕍) :
    ((covCLM S (Pfam (θr M)) φ).comp ((𝕍).subtypeL.comp RinvL)) u =
      ∫ x, φ x * responseScore hS ν M u x ∂(Pfam (θr M)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, covCLM_apply hS _ hφ,
    responseScore, ContinuousLinearEquiv.coe_coe]
  rw [integral_mul_sub_dirLoss hS _ hφ, ← integral_mul_dirLoss hS _ hφ]
  unfold lawCov
  rw [integral_dirLoss_responseTheta hS ν hrel]
  ring

/-- The coordinates of the inverse chart derivative applied to a fixed direction are differentiable
in response coordinates, with derivative `u ↦ −(R Cov_Q(S, ℓ_{M,u} ℓ_{M,w}))_j`. -/
theorem hasFDerivAt_inverse_response_coord (w : 𝕍) (j : J) :
    ∃ L : 𝕍 →L[ℝ] ℝ,
      HasFDerivAt (fun z : 𝕍 ↦ (ContinuousLinearEquiv.symm (CDE (θr (M + z))) w : J → ℝ) j) L 0 ∧
      ∀ u, L u = -((ContinuousLinearEquiv.symm (CDE (θr M))
        ⟨respCov hS ν M (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x),
          respCov_mem_dirSpan hS ν ((bdd_responseScore hS ν M u).mul
            (bdd_responseScore hS ν M w))⟩ : J → ℝ) j) := by
  have hR := hasFDerivAt_inverse_response_apply hS ν hrel w
  have hRc := (𝕍).subtypeL.hasFDerivAt.comp 0 hR
  refine ⟨_, ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J ↦ ℝ) j).hasFDerivAt.comp 0
    hRc).congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_), fun u ↦ ?_⟩
  · simp only [Function.comp_def, Submodule.subtypeL_apply, ContinuousLinearMap.proj_apply]
  have hT : thirdOp hS ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) u)
      (ContinuousLinearEquiv.symm (CDE (θr M)) w) =
      ⟨respCov hS ν M (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x),
        respCov_mem_dirSpan hS ν
          ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w))⟩ :=
    Subtype.ext (by rw [thirdOp_coe_apply, thirdVec_eq_respCov hS ν hrel])
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.proj_apply, neg_mulLeftRight_apply,
    ContinuousLinearEquiv.coe_coe, hT, Submodule.coe_neg, Pi.neg_apply]

/-- The pairing `⟨R_{M+z} w, M + z⟩` is differentiable in response coordinates, with derivative
`u ↦ ⟨R w, u⟩ − ⟨R Cov_Q(S, ℓ_{M,u} ℓ_{M,w}), M⟩`. -/
theorem hasFDerivAt_dotJ_inverse_response (w : 𝕍) :
    ∃ L : 𝕍 →L[ℝ] ℝ,
      HasFDerivAt (fun z : 𝕍 ↦ dotJ (ContinuousLinearEquiv.symm (CDE (θr (M + z))) w : J → ℝ)
        (M + z)) L 0 ∧
      ∀ u, L u = dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) w : J → ℝ) u -
        dotJ (ContinuousLinearEquiv.symm (CDE (θr M))
          ⟨respCov hS ν M (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x),
            respCov_mem_dirSpan hS ν ((bdd_responseScore hS ν M u).mul
              (bdd_responseScore hS ν M w))⟩ : J → ℝ) M := by
  have hR := hasFDerivAt_inverse_response_apply hS ν hrel w
  have hRc := (𝕍).subtypeL.hasFDerivAt.comp 0 hR
  have hc := hasFDerivAt_dotCLM_add ν (S := S) (M := M)
  have h1 := hc.clm_apply hRc
  refine ⟨_, h1.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_), fun u ↦ ?_⟩
  · simp only [dotCLM_apply, Function.comp_def, Submodule.subtypeL_apply]
  · have hT : thirdOp hS ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) u)
        (ContinuousLinearEquiv.symm (CDE (θr M)) w) =
        ⟨respCov hS ν M (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x),
          respCov_mem_dirSpan hS ν
            ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w))⟩ :=
      Subtype.ext (by rw [thirdOp_coe_apply, thirdVec_eq_respCov hS ν hrel])
    simp only [add_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      ContinuousLinearMap.flip_apply, Function.comp_def, dotCLM_apply, dotCLMlin_apply,
      Submodule.coe_zero, add_zero, neg_mulLeftRight_apply, ContinuousLinearEquiv.coe_coe, hT,
      Submodule.coe_neg, dotJ_neg_left]
    ring

/-- **The observable defect to second order**: the derivative field `z ↦ E_{Π(M+z)}[φ ℓ_{M+z,w}]`
of the response of a bounded observable is differentiable at `z = 0`, with derivative
`u ↦ E_Q[φ · N_M(ℓ_{M,u} ℓ_{M,w})]`. -/
theorem hasFDerivAt_integral_responseScore {φ : X → ℝ} (hφ : Bdd φ) (w : 𝕍) :
    ∃ L : 𝕍 →L[ℝ] ℝ,
      HasFDerivAt (fun z : 𝕍 ↦ ∫ x, φ x * responseScore hS ν (M + z) w x ∂(Pfam (θr (M + z))))
        L 0 ∧
      ∀ u, L u = ∫ x, φ x * normalProj hS ν M
        ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w)) x ∂(Pfam (θr M)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  -- the field as a finite combination of differentiable scalars
  have hfun : ∀ z : 𝕍, ∫ x, φ x * responseScore hS ν (M + z) w x ∂(Pfam (θr (M + z))) =
      dotJ (ContinuousLinearEquiv.symm (CDE (θr (M + z))) w : J → ℝ) (M + z) *
        (∫ x, φ x ∂(Pfam (θr (M + z)))) -
      ∑ j, (ContinuousLinearEquiv.symm (CDE (θr (M + z))) w : J → ℝ) j *
        ∫ x, φ x * S j x ∂(Pfam (θr (M + z))) := fun z ↦ by
    have := isProbabilityMeasure_family hS ν (θr (M + z) : J → ℝ)
    simp only [responseScore]
    rw [integral_mul_sub_dirLoss hS _ hφ]
  obtain ⟨LA, hA, hAv⟩ := hasFDerivAt_dotJ_inverse_response hS ν hrel w
  have hE := hasFDerivAt_integral_response hS ν hrel hφ
  have hEj : ∀ j, HasFDerivAt (fun z : 𝕍 ↦ ∫ x, φ x * S j x ∂(Pfam (θr (M + z))))
      ((covCLM S (Pfam (θr M)) (fun x ↦ φ x * S j x)).comp ((𝕍).subtypeL.comp RinvL)) 0 :=
    fun j ↦ hasFDerivAt_integral_response hS ν hrel (hφ.mul (hS j))
  choose LR hRj hRv using hasFDerivAt_inverse_response_coord hS ν hrel w
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ ↦ (hRj j).mul (hEj j)
  have h := (hA.mul hE).sub hsum
  refine ⟨_, h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ hfun z), fun u ↦ ?_⟩
  -- evaluate the derivative
  have hEv := integral_response_deriv_apply hS ν hrel hφ
  have hEjv := fun j u ↦ integral_response_deriv_apply hS ν hrel (hφ.mul (hS j)) u
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, sum_apply, hAv, hRv, hEv, hEjv,
    Submodule.coe_zero, add_zero]
  -- the target as a combination of integrals
  have hsym : dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) w : J → ℝ) u =
      dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ) w := by
    have a := integral_responseScore_mul hS ν hrel w u
    have b := integral_responseScore_mul hS ν hrel u w
    have e : ∫ y, responseScore hS ν M w y * responseScore hS ν M u y ∂(Pfam (θr M)) =
        ∫ y, responseScore hS ν M u y * responseScore hS ν M w y ∂(Pfam (θr M)) :=
      integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)
    linarith
  have hb := (bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w)
  have hN : ∫ x, φ x * normalProj hS ν M hb x ∂(Pfam (θr M)) =
      (∫ x, (φ x * responseScore hS ν M u x) * responseScore hS ν M w x ∂(Pfam (θr M))) -
      (∫ x, responseScore hS ν M u x * responseScore hS ν M w x ∂(Pfam (θr M))) *
        (∫ x, φ x ∂(Pfam (θr M))) -
      ∫ x, φ x * regProj hS ν M hb x ∂(Pfam (θr M)) := by
    have i1 : Integrable (fun x ↦ (φ x * responseScore hS ν M u x) * responseScore hS ν M w x)
        (Pfam (θr M)) := integrable_of_bdd_prob _ ((hφ.mul (bdd_responseScore hS ν M u)).mul
          (bdd_responseScore hS ν M w))
    have i2 : Integrable (fun x ↦ φ x * ∫ y, responseScore hS ν M u y * responseScore hS ν M w y
        ∂(Pfam (θr M))) (Pfam (θr M)) := (integrable_of_bdd_prob _ hφ).mul_const _
    have i3 : Integrable (fun x ↦ φ x * regProj hS ν M hb x) (Pfam (θr M)) :=
      integrable_of_bdd_prob _ (hφ.mul (bdd_responseScore hS ν M _))
    have i12 : Integrable (fun x ↦ (φ x * responseScore hS ν M u x) * responseScore hS ν M w x -
        φ x * ∫ y, responseScore hS ν M u y * responseScore hS ν M w y ∂(Pfam (θr M)))
        (Pfam (θr M)) := i1.sub i2
    have e : (fun x ↦ φ x * normalProj hS ν M hb x) = fun x ↦
        (φ x * responseScore hS ν M u x) * responseScore hS ν M w x -
        φ x * (∫ y, responseScore hS ν M u y * responseScore hS ν M w y ∂(Pfam (θr M))) -
        φ x * regProj hS ν M hb x := by
      funext x
      unfold normalProj
      ring
    rw [e, integral_sub i12 i3, integral_sub i1 i2, integral_mul_const]
    ring
  -- expand the two remaining integrals against the scores
  have hT1 : ∫ x, (φ x * responseScore hS ν M u x) * responseScore hS ν M w x ∂(Pfam (θr M)) =
      dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) w : J → ℝ) M *
        (∫ x, φ x * responseScore hS ν M u x ∂(Pfam (θr M))) -
      ∑ j, (ContinuousLinearEquiv.symm (CDE (θr M)) w : J → ℝ) j *
        ∫ x, (φ x * S j x) * responseScore hS ν M u x ∂(Pfam (θr M)) := by
    conv_lhs => simp only [responseScore_apply hS ν (M := M) w]
    rw [integral_mul_sub_dirLoss hS _ (hφ.mul (bdd_responseScore hS ν M u))]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have hT2 : ∫ x, φ x * regProj hS ν M hb x ∂(Pfam (θr M)) =
      dotJ (ContinuousLinearEquiv.symm (CDE (θr M))
          ⟨respCov hS ν M (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x),
            respCov_mem_dirSpan hS ν hb⟩ : J → ℝ) M * (∫ x, φ x ∂(Pfam (θr M))) -
      ∑ j, (∫ x, φ x * S j x ∂(Pfam (θr M))) * (ContinuousLinearEquiv.symm (CDE (θr M))
          ⟨respCov hS ν M (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x),
            respCov_mem_dirSpan hS ν hb⟩ : J → ℝ) j := by
    unfold regProj
    conv_lhs => simp only [responseScore_apply hS ν (M := M)
      ⟨respCov hS ν M (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x),
        respCov_mem_dirSpan hS ν hb⟩]
    rw [integral_mul_sub_dirLoss hS _ hφ]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  rw [hN, hT1, hT2, integral_responseScore_mul hS ν hrel u w, hsym]
  simp only [mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

end Observable

end Laplace.Multi
