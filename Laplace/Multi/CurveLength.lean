/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ReconstructionC1
import Laplace.Multi.ReconstructionLipschitz

/-!
# Total-variation length is bounded by Fisher length along interior curves

Along a `C¹` curve `t ↦ M + γ(t)` of interior responses, the reconstruction density moves in `L¹`
with speed `‖Dp_{M+γ(t)} γ'(t)‖₁ = E_{Q_t}|ℓ_{γ'(t)}| ≤ √g_{M+γ(t)}(γ'(t), γ'(t))`
(`norm_reconstructionDeriv_apply_le`), so

`∫ |q_{M+γ(1)} − q_{M+γ(0)}| dν ≤ ∫₀¹ √g_{M+γ(t)}(γ'(t), γ'(t)) dt`
(`integral_abs_famDens_curve_le`):

total-variation length is at most Fisher–Rao length, for every interior `C¹` curve and not only for
the straight atlas. The proof is the chain rule for the `L¹`-differential of the reconstruction, the
fundamental theorem of calculus in `L¹`, and the pointwise speed bound.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The `L¹` speed of the reconstruction is at most the Fisher speed**:
`‖Dp_M u‖₁ ≤ √g_M(u, u)`. -/
theorem norm_reconstructionDeriv_apply_le (M : J → ℝ) (u : 𝕍) :
    ‖reconstructionDeriv hS ν M u‖ ≤ √(fisherForm hS ν M u u) := by
  rw [reconstructionDeriv_apply, L1.norm_of_fun_eq_integral_norm]
  have h := integral_abs_responseScore_le_sqrt hS ν (M := M) u
  rw [integral_famDens_mul hS ν] at h
  refine le_trans (le_of_eq ?_) h
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (famDens_nonneg hS ν _ x)]

/-- The chain rule: along a differentiable curve of interior responses, the reconstruction density
is differentiable in `L¹` with derivative `Dp_{M+γ(t)} γ'(t)`. -/
theorem hasDerivAt_reconstructionL1_curve {M : J → ℝ} {γ : ℝ → 𝕍} {γ' : ℝ → 𝕍} {t : ℝ}
    (hγ : HasDerivAt γ (γ' t) t)
    (hint : M + (γ t : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasDerivAt (fun s ↦ reconstructionL1 hS ν (M + (γ s : J → ℝ)))
      (reconstructionDeriv hS ν (M + (γ t : J → ℝ)) (γ' t)) t := by
  have h := hasFDerivAt_reconstructionL1 hS ν hint
  have h2 : HasDerivAt (fun s ↦ γ s - γ t) (γ' t) t := hγ.sub_const _
  have h3 : HasDerivAt (fun s ↦ γ s - γ t) (γ' t) t := h2
  rw [show (0 : 𝕍) = γ t - γ t by simp] at h
  have h4 := h.comp_hasDerivAt t h3
  refine h4.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
  simp only [Function.comp_def, Submodule.coe_sub]
  congr 1
  abel

/-- **Total-variation length is at most Fisher length** along a `C¹` curve of interior responses:
`∫ |q_{M+γ(1)} − q_{M+γ(0)}| dν ≤ ∫₀¹ √g_{M+γ(t)}(γ'(t), γ'(t)) dt`. -/
theorem integral_abs_famDens_curve_le {M : J → ℝ} {γ γ' : ℝ → 𝕍}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc (0 : ℝ) 1))
    (hint : ∀ t ∈ Icc (0 : ℝ) 1,
      M + (γ t : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∫ x, |famDens S ν (θr (M + (γ 1 : J → ℝ))) x - famDens S ν (θr (M + (γ 0 : J → ℝ))) x| ∂ν ≤
      ∫ t in (0 : ℝ)..1, √(fisherForm hS ν (M + (γ t : J → ℝ)) (γ' t) (γ' t)) := by
  -- the derivative along the curve
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ reconstructionL1 hS ν (M + (γ s : J → ℝ)))
      (reconstructionDeriv hS ν (M + (γ t : J → ℝ)) (γ' t)) t := fun t ht ↦ by
    rw [uIcc_of_le zero_le_one] at ht
    exact hasDerivAt_reconstructionL1_curve hS ν (hγ t ht) (hint t ht)
  -- continuity of the derivative on `[0, 1]`
  have hγc : ContinuousOn γ (Icc (0 : ℝ) 1) := fun t ht ↦
    (hγ t ht).continuousAt.continuousWithinAt
  have hpath : ContinuousOn (fun t ↦ M + (γ t : J → ℝ)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.add (continuous_subtype_val.comp_continuousOn hγc)
  have hD : ContinuousOn (fun t ↦ reconstructionDeriv hS ν (M + (γ t : J → ℝ))) (Icc (0 : ℝ) 1) :=
    fun t ht ↦ ContinuousWithinAt.comp (g := fun M' ↦ reconstructionDeriv hS ν M')
      (f := fun t ↦ M + (γ t : J → ℝ)) (continuousWithinAt_reconstructionDeriv hS ν (hint t ht))
      (hpath t ht) fun s hs ↦ hint s hs
  have hDγ : ContinuousOn (fun t ↦ reconstructionDeriv hS ν (M + (γ t : J → ℝ)) (γ' t))
      (Icc (0 : ℝ) 1) := hD.clm_apply hγ'
  have hint1 : IntervalIntegrable (fun t ↦ reconstructionDeriv hS ν (M + (γ t : J → ℝ)) (γ' t))
      volume 0 1 := hDγ.intervalIntegrable_of_Icc zero_le_one
  -- the Fisher speed is continuous, hence integrable
  have hR : ContinuousOn (fun t ↦ (ContinuousLinearEquiv.symm (chartDerivEquiv measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (θr (M + (γ t : J → ℝ)))) :
        𝕍 →L[ℝ] 𝕍)) (Icc (0 : ℝ) 1) := fun t ht ↦
    ContinuousWithinAt.comp (g := fun M' : J → ℝ ↦ (ContinuousLinearEquiv.symm (chartDerivEquiv
      measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (θr M')) :
        𝕍 →L[ℝ] 𝕍)) (f := fun t ↦ M + (γ t : J → ℝ))
      ((continuousOn_inverse_chart hS ν) _ (hint t ht)) (hpath t ht) fun s hs ↦ hint s hs
  have hg : ContinuousOn (fun t ↦ fisherForm hS ν (M + (γ t : J → ℝ)) (γ' t) (γ' t))
      (Icc (0 : ℝ) 1) := by
    have e : ∀ t ∈ Icc (0 : ℝ) 1, fisherForm hS ν (M + (γ t : J → ℝ)) (γ' t) (γ' t) =
        -dotJ ((ContinuousLinearEquiv.symm (chartDerivEquiv measurable_const
          (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
            (θr (M + (γ t : J → ℝ)))) : 𝕍 →L[ℝ] 𝕍) (γ' t) : J → ℝ) (γ' t) := fun t ht ↦
      fisherForm_eq_neg_dotJ hS ν (hint t ht) _ _
    refine ContinuousOn.congr ?_ e
    refine ContinuousOn.neg ?_
    have h1 : ContinuousOn (fun t ↦ ((ContinuousLinearEquiv.symm (chartDerivEquiv measurable_const
        (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
          (θr (M + (γ t : J → ℝ)))) : 𝕍 →L[ℝ] 𝕍) (γ' t) : J → ℝ)) (Icc (0 : ℝ) 1) :=
      continuous_subtype_val.comp_continuousOn (hR.clm_apply hγ')
    have h2 : ContinuousOn (fun t ↦ (γ' t : J → ℝ)) (Icc (0 : ℝ) 1) :=
      continuous_subtype_val.comp_continuousOn hγ'
    unfold dotJ
    exact continuousOn_finsetSum _ fun j _ ↦
      ((continuous_apply j).comp_continuousOn h1).mul ((continuous_apply j).comp_continuousOn h2)
  have hgint : IntervalIntegrable (fun t ↦ √(fisherForm hS ν (M + (γ t : J → ℝ)) (γ' t) (γ' t)))
      volume 0 1 :=
    (Real.continuous_sqrt.comp_continuousOn hg).intervalIntegrable_of_Icc zero_le_one
  -- the fundamental theorem of calculus in `L¹`
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint1
  have hnorm : ∫ x, |famDens S ν (θr (M + (γ 1 : J → ℝ))) x -
      famDens S ν (θr (M + (γ 0 : J → ℝ))) x| ∂ν =
      ‖reconstructionL1 hS ν (M + (γ 1 : J → ℝ)) - reconstructionL1 hS ν (M + (γ 0 : J → ℝ))‖ := by
    unfold reconstructionL1
    rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [hnorm, ← hftc]
  calc ‖∫ t in (0 : ℝ)..1, reconstructionDeriv hS ν (M + (γ t : J → ℝ)) (γ' t)‖
      ≤ ∫ t in (0 : ℝ)..1, ‖reconstructionDeriv hS ν (M + (γ t : J → ℝ)) (γ' t)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, √(fisherForm hS ν (M + (γ t : J → ℝ)) (γ' t) (γ' t)) :=
        intervalIntegral.integral_mono_on zero_le_one hint1.norm hgint fun t _ ↦
          norm_reconstructionDeriv_apply_le hS ν _ _

end Laplace.Multi
