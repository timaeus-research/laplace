/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDualConnections
import Laplace.Multi.SmoothFamily

/-!
# The curvature of the `α`-connections of the response chart

In the natural chart the `α`-Christoffel operator is `Γ^α_θ = ((1−α)/2) C_θ` with
`C_θ = A_θ⁻¹ T_θ` the mixture Christoffel operator. Its derivative along a line is
`∂_u C_θ(v,w) = −C_θ(u, C_θ(v,w)) + A_θ⁻¹ Q_θ(u,v,w)` (`hasDerivAt_mChristoffel_line`), where the
fourth-order operator `Q_θ = ∂ T_θ` (`fourthOp`, the third Fréchet derivative of the chart) is
symmetric in its first two slots (`fourthOp_symm`). The curvature operator of the `α`-connection on
constant fields of the chart,

  `R^α(u,v)w = ∂_u Γ^α(v,w) − ∂_v Γ^α(u,w) + Γ^α(u,Γ^α(v,w)) − Γ^α(v,Γ^α(u,w))`
  (`alphaCurvature`),

therefore loses its fourth-order terms and is the quadratic expression

  `R^α_θ(u,v)w = −((1−α²)/4) (C_θ(u,C_θ(v,w)) − C_θ(v,C_θ(u,w)))`   (`alphaCurvature_eq`).

In particular the exponential and mixture connections are flat (`alphaCurvature_one`,
`alphaCurvature_neg_one`) and the Levi-Civita curvature is `−¼` of the commutator of the mixture
Christoffel operator (`alphaCurvature_zero`): the family of laws reached by the response map is
dually flat, and its Riemannian curvature is entirely carried by the third cumulants.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Fourth

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The intrinsic chart `θ ↦ m(θ) − m(0)`. -/
local notation "chV" => chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a function of the base point is the Fréchet derivative of the chart. -/
theorem chartDeriv_eq_fderiv_chartV : (fun θ : 𝕍 ↦ CD θ) = fderiv ℝ chV :=
  funext fun θ ↦ ((hasStrictFDerivAt_chartV measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS θ).hasFDerivAt.fderiv).symm

/-- The third-cumulant operator is the Fréchet derivative of the covariance operator. -/
theorem thirdOp_eq_fderiv_chartDeriv : (fun θ : 𝕍 ↦ thirdOp hS ν θ) = fderiv ℝ (fun θ : 𝕍 ↦ CD θ) :=
  funext fun θ ↦ ((hasFDerivAt_chartDeriv hS ν θ).fderiv).symm

/-- **The third-cumulant operator is `C^∞` in the natural coordinates.** -/
theorem contDiff_thirdOp : ContDiff ℝ ∞ (fun θ : 𝕍 ↦ thirdOp hS ν θ) := by
  rw [thirdOp_eq_fderiv_chartDeriv hS ν]
  exact (contDiff_infty_iff_fderiv.1 (contDiff_chartDeriv hS ν)).2

/-- **The fourth-order operator** `Q_θ = ∂T_θ`: the Fréchet derivative of the third-cumulant
operator, `Q_θ(u,v,w) = ∂_u T_θ(v,w)`. -/
noncomputable def fourthOp (θ : 𝕍) : 𝕍 →L[ℝ] (𝕍 →L[ℝ] (𝕍 →L[ℝ] 𝕍)) :=
  fderiv ℝ (fun θ : 𝕍 ↦ thirdOp hS ν θ) θ

theorem hasFDerivAt_thirdOp (θ₀ : 𝕍) :
    HasFDerivAt (fun θ : 𝕍 ↦ thirdOp hS ν θ) (fourthOp hS ν θ₀) θ₀ :=
  ((contDiff_thirdOp hS ν).differentiable (by simp) θ₀).hasFDerivAt

/-- **The fourth-order operator is symmetric in its first two slots** (symmetry of the second
Fréchet derivative of the covariance operator). -/
theorem fourthOp_symm (θ u v : 𝕍) : fourthOp hS ν θ u v = fourthOp hS ν θ v u := by
  have h := (contDiff_chartDeriv hS ν).contDiffAt.isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact natCast_le_infty 2) (x := θ)
  unfold fourthOp
  rw [thirdOp_eq_fderiv_chartDeriv hS ν]
  exact h u v

/-- The third-cumulant operator along a line. -/
theorem hasDerivAt_thirdOp_line (θ u v w : 𝕍) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ thirdOp hS ν (θ + t • u) v w)
      (fourthOp hS ν (θ + t₀ • u) u v w) t₀ := by
  have h0 := (hasFDerivAt_thirdOp hS ν (θ + t₀ • u)).comp_hasDerivAt t₀
    (hasDerivAt_natLine ν θ u t₀)
  have h1 : HasDerivAt (fun t : ℝ ↦ thirdOp hS ν (θ + t • u)) (fourthOp hS ν (θ + t₀ • u) u) t₀ :=
    h0
  have h2 := (h1.clm_apply (hasDerivAt_const t₀ v)).clm_apply (hasDerivAt_const t₀ w)
  refine h2.congr_deriv ?_
  simp

/-- **The inverse covariance operator is differentiable in the natural coordinates**, with
derivative `u ↦ −A⁻¹ T_θ(u) A⁻¹`. -/
theorem hasFDerivAt_inverse_natural (θ₀ : 𝕍) :
    HasFDerivAt (fun θ : 𝕍 ↦ (ContinuousLinearEquiv.symm (CDE θ) : 𝕍 →L[ℝ] 𝕍))
      ((-ContinuousLinearMap.mulLeftRight ℝ _ (ContinuousLinearEquiv.symm (CDE θ₀) : 𝕍 →L[ℝ] 𝕍)
        (ContinuousLinearEquiv.symm (CDE θ₀) : 𝕍 →L[ℝ] 𝕍)).comp (thirdOp hS ν θ₀)) θ₀ := by
  have hG := hasFDerivAt_chartDeriv hS ν θ₀
  have hu : IsUnit (CD θ₀) := by
    rw [← coe_chartDerivEquiv]
    exact ((ContinuousLinearEquiv.unitsEquiv ℝ (𝕍)).symm (CDE θ₀)).isUnit
  obtain ⟨u, hu⟩ := hu
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at h
  have h2 := h.comp θ₀ hG
  have hinv : ((u⁻¹ : (𝕍 →L[ℝ] 𝕍)ˣ) : 𝕍 →L[ℝ] 𝕍) =
      (ContinuousLinearEquiv.symm (CDE θ₀) : 𝕍 →L[ℝ] 𝕍) := by
    rw [coe_chartDerivEquiv_symm, ← hu, Ring.inverse_unit]
  rw [hinv] at h2
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun θ ↦ ?_)
  simp only [Function.comp_def]
  exact coe_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ

/-- The inverse covariance operator along a line. -/
theorem hasDerivAt_inverse_line (θ u : 𝕍) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (ContinuousLinearEquiv.symm (CDE (θ + t • u)) : 𝕍 →L[ℝ] 𝕍))
      ((-ContinuousLinearMap.mulLeftRight ℝ _
        (ContinuousLinearEquiv.symm (CDE (θ + t₀ • u)) : 𝕍 →L[ℝ] 𝕍)
        (ContinuousLinearEquiv.symm (CDE (θ + t₀ • u)) : 𝕍 →L[ℝ] 𝕍))
          (thirdOp hS ν (θ + t₀ • u) u)) t₀ := by
  have h := (hasFDerivAt_inverse_natural hS ν (θ + t₀ • u)).comp_hasDerivAt t₀
    (hasDerivAt_natLine ν θ u t₀)
  exact h

theorem mChristoffel_smul_right (θ u : 𝕍) (c : ℝ) (x : 𝕍) :
    mChristoffel hS ν θ u (c • x) = c • mChristoffel hS ν θ u x := by
  unfold mChristoffel
  rw [map_smul, map_smul]

theorem mChristoffel_sub_right (θ u x y : 𝕍) :
    mChristoffel hS ν θ u (x - y) = mChristoffel hS ν θ u x - mChristoffel hS ν θ u y := by
  unfold mChristoffel
  rw [map_sub, map_sub]

/-- **The derivative of the mixture Christoffel operator along a line**:
`∂_u C_θ(v,w) = −C_θ(u, C_θ(v,w)) + A_θ⁻¹ Q_θ(u,v,w)`. -/
theorem hasDerivAt_mChristoffel_line (θ u v w : 𝕍) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ mChristoffel hS ν (θ + t • u) v w)
      (-mChristoffel hS ν (θ + t₀ • u) u (mChristoffel hS ν (θ + t₀ • u) v w) +
        ContinuousLinearEquiv.symm (CDE (θ + t₀ • u)) (fourthOp hS ν (θ + t₀ • u) u v w)) t₀ := by
  have h := (hasDerivAt_inverse_line hS ν θ u t₀).clm_apply
    (hasDerivAt_thirdOp_line hS ν θ u v w t₀)
  refine h.congr_deriv ?_
  rfl

/-- The derivative of the `α`-Christoffel operator along a line. -/
theorem hasDerivAt_alphaChristoffel_line (α : ℝ) (θ u v w : 𝕍) :
    HasDerivAt (fun t : ℝ ↦ alphaChristoffel hS ν α (θ + t • u) v w)
      (((1 - α) / 2) • (-mChristoffel hS ν θ u (mChristoffel hS ν θ v w) +
        ContinuousLinearEquiv.symm (CDE θ) (fourthOp hS ν θ u v w))) 0 := by
  have h := (hasDerivAt_mChristoffel_line hS ν θ u v w 0).const_smul ((1 - α) / 2)
  rw [zero_smul, add_zero] at h
  exact h

/-- **The curvature operator of the `α`-connection** on constant fields of the natural chart:
`R^α_θ(u,v)w = ∂_u Γ^α(v,w) − ∂_v Γ^α(u,w) + Γ^α(u,Γ^α(v,w)) − Γ^α(v,Γ^α(u,w))`. -/
noncomputable def alphaCurvature (α : ℝ) (θ u v w : 𝕍) : 𝕍 :=
  deriv (fun t : ℝ ↦ alphaChristoffel hS ν α (θ + t • u) v w) 0 -
    deriv (fun t : ℝ ↦ alphaChristoffel hS ν α (θ + t • v) u w) 0 +
    alphaChristoffel hS ν α θ u (alphaChristoffel hS ν α θ v w) -
    alphaChristoffel hS ν α θ v (alphaChristoffel hS ν α θ u w)

/-- **The curvature of the `α`-connection is quadratic in the mixture Christoffel operator**:
`R^α_θ(u,v)w = −((1−α²)/4) (C_θ(u,C_θ(v,w)) − C_θ(v,C_θ(u,w)))`. -/
theorem alphaCurvature_eq (α : ℝ) (θ u v w : 𝕍) :
    alphaCurvature hS ν α θ u v w =
      (-((1 - α ^ 2) / 4)) •
        (mChristoffel hS ν θ u (mChristoffel hS ν θ v w) -
          mChristoffel hS ν θ v (mChristoffel hS ν θ u w)) := by
  unfold alphaCurvature
  rw [(hasDerivAt_alphaChristoffel_line hS ν α θ u v w).deriv,
    (hasDerivAt_alphaChristoffel_line hS ν α θ v u w).deriv, fourthOp_symm hS ν θ v u]
  simp only [alphaChristoffel, mChristoffel_smul_right]
  module

/-- The exponential connection is flat. -/
theorem alphaCurvature_one (θ u v w : 𝕍) : alphaCurvature hS ν 1 θ u v w = 0 := by
  rw [alphaCurvature_eq hS ν]
  norm_num

/-- The mixture connection is flat. -/
theorem alphaCurvature_neg_one (θ u v w : 𝕍) : alphaCurvature hS ν (-1) θ u v w = 0 := by
  rw [alphaCurvature_eq hS ν]
  norm_num

/-- **The Riemannian curvature of the Fisher metric** in the natural chart:
`R⁰_θ(u,v)w = −¼ (C_θ(u,C_θ(v,w)) − C_θ(v,C_θ(u,w)))`. -/
theorem alphaCurvature_zero (θ u v w : 𝕍) :
    alphaCurvature hS ν 0 θ u v w =
      (-(1 / 4 : ℝ)) • (mChristoffel hS ν θ u (mChristoffel hS ν θ v w) -
        mChristoffel hS ν θ v (mChristoffel hS ν θ u w)) := by
  rw [alphaCurvature_eq hS ν]
  norm_num

/-- The `α` and `−α` curvatures coincide (duality preserves flatness and curvature). -/
theorem alphaCurvature_neg (α : ℝ) (θ u v w : 𝕍) :
    alphaCurvature hS ν (-α) θ u v w = alphaCurvature hS ν α θ u v w := by
  rw [alphaCurvature_eq hS ν, alphaCurvature_eq hS ν, neg_sq]

/-- The curvature operator is antisymmetric in `(u,v)`. -/
theorem alphaCurvature_antisymm (α : ℝ) (θ u v w : 𝕍) :
    alphaCurvature hS ν α θ v u w = -alphaCurvature hS ν α θ u v w := by
  rw [alphaCurvature_eq hS ν, alphaCurvature_eq hS ν, ← smul_neg, neg_sub]

end Fourth

end Laplace.Multi
