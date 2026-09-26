/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteResponse
import Laplace.Multi.EmpiricalProjection

/-!
# The accounting identity up to the boundary

The finite-response Taylor identity of `FiniteResponse` is stated for interior responses on the
whole atlas `[0, 1]`. For a finite-rate response `M` on the relative boundary the atlas
`M_t = m₀ + t(M − m₀)` stays interior for `t < 1`, and the identity holds on `[0, t]` for every
`t < 1` (`integral_atlas_taylor_of_lt`):

`E_{Q_t}φ − E_νφ = t E_ν[φ ℓ_0] + ∫₀ᵗ (t − u) E_{Q_u}[φ N_{M_u}(ℓ_u²)] du`.

The proof is a reparametrisation: `M_t` is interior, its atlas is `s ↦ M_{st}`, its scores are
`t ℓ_{st}` and its normal parts `t² N(ℓ_{st}²)`, so the interior identity for `M_t` at `s = 1`
becomes the identity for `M` at `t` after the change of variables `u = st`. Consequently,
whenever the responses `E_{Q_t}φ` converge as `t ↑ 1` (in particular under total-variation
convergence of the atlas to an endpoint law), the triangular-kernel accounting expression
converges to the endpoint response (`tendsto_atlas_taylor_endpoint`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Scaling

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] (M : J → ℝ)
include hS

/-- The response score is linear in the direction. -/
theorem responseScore_smul (c : ℝ) (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) (x : X) :
    responseScore hS ν M (c • u) x = c * responseScore hS ν M u x := by
  unfold responseScore
  rw [map_smul, Submodule.coe_smul, dotJ_smul_left, dirLoss_smul]
  ring

variable {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) {c : ℝ} (hfg : ∀ x, f x = c * g x)
include hfg

/-- The covariance vector scales with the observable. -/
theorem respCov_congr_smul : respCov hS ν M f = c • respCov hS ν M g := by
  funext j
  simp only [respCov, lawCov, Pi.smul_apply, smul_eq_mul, hfg, mul_left_comm _ c,
    integral_const_mul]
  ring

include hf hg in
/-- The regression part scales with the observable. -/
theorem regProj_congr_smul (x : X) : regProj hS ν M hf x = c * regProj hS ν M hg x := by
  unfold regProj
  have e : (⟨respCov hS ν M f, respCov_mem_dirSpan hS ν hf⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) =
      c • ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩ := by
    ext
    simp only [Submodule.coe_smul, respCov_congr_smul hS ν M hfg]
  rw [e, responseScore_smul]

include hf hg in
/-- The normal part scales with the observable. -/
theorem normalProj_congr_smul (x : X) : normalProj hS ν M hf x = c * normalProj hS ν M hg x := by
  unfold normalProj
  rw [regProj_congr_smul hS ν M hf hg hfg]
  simp only [hfg, integral_const_mul]
  ring

end Scaling

section Reparam

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS

/-- The reconstruction at the atlas point `s`. -/
local notation "Qat" s => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
  (atlasTheta hS ν M s)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The atlas of an atlas point is the reparametrised atlas. -/
theorem atlasPath_atlasPath (t s : ℝ) :
    atlasPath S ν (atlasPath S ν M t) s = atlasPath S ν M (s * t) := by
  unfold atlasPath
  module

/-- The natural coordinates of the reparametrised atlas. -/
theorem atlasTheta_atlasPath (t s : ℝ) :
    atlasTheta hS ν (atlasPath S ν M t) s = atlasTheta hS ν M (s * t) := by
  unfold atlasTheta
  rw [atlasPath_atlasPath]

include hfin

/-- The velocity of the reparametrised atlas is `t` times the velocity at `st`. -/
theorem atlasVel_atlasPath (t s : ℝ) (hfin' : genRate ν S (atlasPath S ν M t) ≠ ⊤) :
    atlasVel hS ν hfin' s = t • atlasVel hS ν hfin (s * t) := by
  unfold atlasVel
  rw [atlasTheta_atlasPath hS ν t s, ← map_smul]
  congr 1
  refine Subtype.ext ?_
  simp only [Submodule.coe_smul]
  unfold atlasPath
  module

/-- The score of the reparametrised atlas is `t` times the score at `st`. -/
theorem atlasScore_atlasPath (t s : ℝ) (hfin' : genRate ν S (atlasPath S ν M t) ≠ ⊤) (x : X) :
    atlasScore hS ν hfin' s x = t * atlasScore hS ν hfin (s * t) x := by
  unfold atlasScore
  rw [atlasVel_atlasPath hS ν hfin t s hfin', atlasPath_atlasPath, Submodule.coe_smul,
    dotJ_smul_left, dirLoss_smul]
  ring

/-- The normal second-order field of the reparametrised atlas is `t²` times the field at `st`. -/
theorem integral_normalProj_atlasPath (t s : ℝ) (hfin' : genRate ν S (atlasPath S ν M t) ≠ ⊤)
    {φ : X → ℝ} :
    ∫ x, φ x * normalProj hS ν (atlasPath S ν (atlasPath S ν M t) s)
        (bdd_atlasScore_sq hS ν hfin' (s := s)) x
        ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          (atlasTheta hS ν (atlasPath S ν M t) s) =
      t ^ 2 * ∫ x, φ x * normalProj hS ν (atlasPath S ν M (s * t))
        (bdd_atlasScore_sq hS ν hfin (s := s * t)) x ∂(Qat (s * t)) := by
  rw [atlasTheta_atlasPath hS ν t s, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [atlasPath_atlasPath, normalProj_congr_smul hS ν _ (bdd_atlasScore_sq hS ν hfin' (s := s))
    (bdd_atlasScore_sq hS ν hfin (s := s * t)) (c := t ^ 2) fun y ↦ by
      rw [atlasScore_atlasPath hS ν hfin t s hfin']
      ring]
  ring

/-- **The accounting identity on `[0, t]` for every `t < 1`**, for a finite-rate response that may
lie on the relative boundary of the moment body:
`E_{Q_t}φ − E_νφ = t E_ν[φ ℓ_0] + ∫₀ᵗ (t − u) E_{Q_u}[φ N_{M_u}(ℓ_u²)] du`. -/
theorem integral_atlas_taylor_of_lt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {φ : X → ℝ}
    (hφ : Bdd φ) :
    (∫ x, φ x ∂(Qat t)) - (∫ x, φ x ∂ν) =
      t * (∫ x, φ x * atlasScore hS ν hfin 0 x ∂ν) +
        ∫ u in (0 : ℝ)..t, (t - u) * ∫ x, φ x * normalProj hS ν (atlasPath S ν M u)
          (bdd_atlasScore_sq hS ν hfin (s := u)) x ∂(Qat u) := by
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · rw [atlas_zero_eq hS ν]
    simp
  have hrel' := atlas_mem_intrinsicInterior hS ν hfin ht0 ht1
  have hfin' := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel'
  have h := integral_atlas_taylor hS ν hfin' hrel' hφ
  rw [atlas_zero_eq hS ν, atlasTheta_atlasPath hS ν t 1, one_mul] at h
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun u ↦ ∫ x, φ x * normalProj hS ν (atlasPath S ν M u)
      (bdd_atlasScore_sq hS ν hfin (s := u)) x ∂(Qat u) := ⟨_, rfl⟩
  have hFs : ∀ s, ∫ x, φ x * normalProj hS ν (atlasPath S ν (atlasPath S ν M t) s)
      (bdd_atlasScore_sq hS ν hfin' (s := s)) x
      ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν (atlasPath S ν M t) s) = t ^ 2 * F (s * t) := fun s ↦ by
    rw [hF, integral_normalProj_atlasPath hS ν hfin t s hfin']
  have e1 : ∫ x, φ x * atlasScore hS ν hfin' 0 x ∂ν =
      t * ∫ x, φ x * atlasScore hS ν hfin 0 x ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [atlasScore_atlasPath hS ν hfin t 0 hfin', zero_mul]
    ring
  have e2 : (∫ s in (0 : ℝ)..1, (1 - s) * ∫ x, φ x * normalProj hS ν
      (atlasPath S ν (atlasPath S ν M t) s) (bdd_atlasScore_sq hS ν hfin' (s := s)) x
      ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν (atlasPath S ν M t) s)) =
      ∫ u in (0 : ℝ)..t, (t - u) * F u := by
    calc (∫ s in (0 : ℝ)..1, (1 - s) * ∫ x, φ x * normalProj hS ν
          (atlasPath S ν (atlasPath S ν M t) s) (bdd_atlasScore_sq hS ν hfin' (s := s)) x
          ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
            (atlasTheta hS ν (atlasPath S ν M t) s))
        = ∫ s in (0 : ℝ)..1, (fun u ↦ t * ((t - u) * F u)) (s * t) := by
          refine intervalIntegral.integral_congr fun s _ ↦ ?_
          simp only [hFs]
          ring
      _ = t⁻¹ • ∫ u in (0 : ℝ) * t..1 * t, t * ((t - u) * F u) :=
          intervalIntegral.integral_comp_mul_right (fun u ↦ t * ((t - u) * F u)) ht0'.ne'
      _ = ∫ u in (0 : ℝ)..t, (t - u) * F u := by
          rw [zero_mul, one_mul, smul_eq_mul, intervalIntegral.integral_const_mul, ← mul_assoc,
            inv_mul_cancel₀ ht0'.ne', one_mul]
  rw [e1, e2] at h
  rw [h, hF]

/-- **The triangular-kernel accounting identity at the boundary**: whenever the responses `E_{Q_t}φ`
converge as `t ↑ 1` (for instance under total-variation convergence of the atlas to an endpoint
law), the accounting expression `t E_ν[φℓ_0] + ∫₀ᵗ (t − u) E_{Q_u}[φ N(ℓ_u²)] du` converges to
the endpoint response minus the featureless response. -/
theorem tendsto_atlas_taylor_endpoint {φ : X → ℝ} (hφ : Bdd φ) {L : ℝ}
    (hL : Tendsto (fun t ↦ ∫ x, φ x ∂(Qat t)) (𝓝[<] (1 : ℝ)) (𝓝 L)) :
    Tendsto (fun t ↦ t * (∫ x, φ x * atlasScore hS ν hfin 0 x ∂ν) +
        ∫ u in (0 : ℝ)..t, (t - u) * ∫ x, φ x * normalProj hS ν (atlasPath S ν M u)
          (bdd_atlasScore_sq hS ν hfin (s := u)) x ∂(Qat u))
      (𝓝[<] (1 : ℝ)) (𝓝 (L - ∫ x, φ x ∂ν)) := by
  refine (hL.sub_const _).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
  exact integral_atlas_taylor_of_lt hS ν hfin ht.1.le ht.2 hφ

end Reparam

end Laplace.Multi
