/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ReconstructionDerivative
import Laplace.Multi.BoundaryTaylor
import Laplace.Multi.DualFlat

/-!
# The reconstruction as an `L¹`-differential retraction

The reconstruction density `p(M) = [q_M] ∈ L¹(ν)` is Fréchet differentiable at every interior
response, with derivative `u ↦ [q_M ℓ_{M,u}]` (`hasFDerivAt_reconstructionL1`); the derivative is
realised as a continuous linear map on the direction subspace (`reconstructionDeriv`). Composed
with the feature moment map `H(h) = ∫ S h dν` the derivative transmits exactly the moment
perturbation, `H(q_M ℓ_{M,u}) = u` (`moment_famDens_mul_responseScore`), and for a centred
relative perturbation `q_M g` the composite `P_M = Dp_M ∘ H` is the regression projection,
`P_M(q_M g) = q_M B_M g` (`famDens_mul_regProj_eq`): the derivative of the reconstruction keeps
the feature-visible component of a perturbation and discards the invisible one. Since `H ∘ Dp_M =
id`, `P_M` is idempotent (`famDens_mul_responseScore_moment_eq`).
-/

open MeasureTheory Filter Topology Set Asymptotics

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
include hS

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

/-- The response score is additive in the direction. -/
theorem responseScore_add (u v : 𝕍) (x : X) :
    responseScore hS ν M (u + v) x = responseScore hS ν M u x + responseScore hS ν M v x := by
  unfold responseScore
  rw [map_add, Submodule.coe_add, dotJ_add_left, dirLoss_add]
  ring

/-- `q_M ℓ_{M,u}` is integrable. -/
theorem integrable_famDens_mul_responseScore (u : 𝕍) :
    Integrable (fun x ↦ famDens S ν (θr M) x * responseScore hS ν M u x) ν := by
  obtain ⟨hm, B, hB⟩ := bdd_responseScore hS ν M u
  exact (integrable_famDens hS ν _).mul_bdd hm.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

/-- The reconstruction density as an element of `L¹(ν)`. -/
noncomputable def reconstructionL1 (M : J → ℝ) : X →₁[ν] ℝ :=
  (integrable_famDens hS ν (θr M)).toL1 _

/-- The candidate derivative `u ↦ [q_M ℓ_{M,u}]`, as a linear map on the direction subspace. -/
noncomputable def reconstructionDerivLin (M : J → ℝ) : 𝕍 →ₗ[ℝ] (X →₁[ν] ℝ) where
  toFun u := (integrable_famDens_mul_responseScore hS ν (M := M) u).toL1 _
  map_add' u v := by
    rw [← Integrable.toL1_add]
    congr 1
    funext x
    simp only [Pi.add_apply, responseScore_add]
    ring
  map_smul' c u := by
    rw [RingHom.id_apply, ← Integrable.toL1_smul']
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, responseScore_smul]
    ring

/-- The derivative of the reconstruction density at `M`, as a continuous linear map. -/
noncomputable def reconstructionDeriv (M : J → ℝ) : 𝕍 →L[ℝ] (X →₁[ν] ℝ) :=
  LinearMap.toContinuousLinearMap (reconstructionDerivLin hS ν M)

theorem reconstructionDeriv_apply (M : J → ℝ) (u : 𝕍) :
    reconstructionDeriv hS ν M u = (integrable_famDens_mul_responseScore hS ν (M := M) u).toL1 _ :=
  rfl

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The reconstruction density is `L¹`-Fréchet differentiable at every interior response**, with
derivative `u ↦ [q_M ℓ_{M,u}]`. -/
theorem hasFDerivAt_reconstructionL1 :
    HasFDerivAt (fun z : 𝕍 ↦ reconstructionL1 hS ν (M + z)) (reconstructionDeriv hS ν M) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, ← isLittleO_norm_left, ← isLittleO_norm_right]
  have h := isLittleO_reconstruction_density_remainder hS ν hrel
  refine h.congr_left fun z ↦ ?_
  rw [zero_add, Submodule.coe_zero, add_zero, reconstructionDeriv_apply]
  unfold reconstructionL1
  rw [← Integrable.toL1_sub, ← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rfl

/-- **The moment map inverts the derivative**: `∫ S_j q_M ℓ_{M,u} dν = u_j`. -/
theorem moment_famDens_mul_responseScore (u : 𝕍) (j : J) :
    ∫ x, S j x * (famDens S ν (θr M) x * responseScore hS ν M u x) ∂ν = (u : J → ℝ) j := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have h := lawCov_stat_responseScore hS ν (M := M) u j
  unfold lawCov at h
  rw [integral_responseScore hS ν hrel, mul_zero, sub_zero] at h
  rw [← h, integral_famDens_mul hS ν]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  ring

omit hrel in
/-- **The composite `P_M = Dp_M ∘ H` on a centred relative perturbation is the regression
projection**: for bounded `g` with `E_Q g = 0`, the direction `H(q_M g) = Cov_Q(S, g)` lies in
`𝕍` and
`q_M ℓ_{M, H(q_M g)} = q_M B_M g`. -/
theorem famDens_mul_regProj_eq {g : X → ℝ} (hg : Bdd g)
    (hg0 : ∫ x, g x ∂(Pfam (θr M)) = 0) (x : X) :
    famDens S ν (θr M) x *
        responseScore hS ν M ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩ x =
      famDens S ν (θr M) x * regProj hS ν M hg x ∧
    respCov hS ν M g = fun j ↦ ∫ x, S j x * (famDens S ν (θr M) x * g x) ∂ν := by
  refine ⟨rfl, ?_⟩
  funext j
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  unfold respCov lawCov
  rw [hg0, mul_zero, sub_zero, integral_famDens_mul hS ν]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  ring

/-- **Idempotence**: applying the moment map to the derivative and feeding the result back gives the
same direction, `H(Dp_M u) = u`, so `P_M = Dp_M ∘ H` satisfies `P_M ∘ P_M = P_M`. -/
theorem famDens_mul_responseScore_moment_eq (u : 𝕍) :
    (fun j ↦ ∫ x, S j x * (famDens S ν (θr M) x * responseScore hS ν M u x) ∂ν) = (u : J → ℝ) :=
  funext fun j ↦ moment_famDens_mul_responseScore hS ν hrel u j

end Laplace.Multi
