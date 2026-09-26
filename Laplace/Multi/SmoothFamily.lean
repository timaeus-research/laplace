/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AtlasHessian
import Laplace.Multi.CovarianceFrechet
import Laplace.Multi.DataRetraction

/-!
# Smoothness of the exponential family in its natural parameter

For every bounded observable `g` the weighted normaliser `N_g(θ) = ∫ g e^{−⟨θ,S⟩} dν` is `C^∞` in
`θ` (`contDiff_famNum`): its derivative is `−⟨·, (N_{g S_j}(θ))_j⟩`, again of the same form, so
smoothness follows by induction with `contDiff_succ_iff_fderiv` and no differentiation under the
integral beyond first order. Consequently the normaliser, the mean map, its Jacobian, the
intrinsic chart `chartV`, the chart derivative and its inverse are all `C^∞`
(`contDiff_famZ`, `contDiff_meanMap`, `contDiff_meanMapDeriv`, `contDiff_chartV`,
`contDiff_chartDeriv`, `contDiff_chartDerivEquiv_symm`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

omit hS in
variable (S) in
/-- The weighted normaliser `N_g(θ) = ∫ g e^{−⟨θ,S⟩} dν`. -/
noncomputable def famNum (g : X → ℝ) (θ : J → ℝ) : ℝ := ∫ x, g x * famWeight S θ x ∂ν

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem famZ_eq_famNum : famZ S ν = famNum S ν (fun _ ↦ 1) := by
  funext θ
  simp [famZ, famNum]

omit [Nonempty X] [Nonempty J] in
/-- A bounded observable times the family weight is integrable. -/
theorem integrable_mul_famWeight {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) :
    Integrable (fun x ↦ g x * famWeight S θ x) ν :=
  (integrable_famWeight hS ν θ).bdd_mul hg.1.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hg.2.choose_spec x)

omit [Nonempty X] [Nonempty J] in
/-- `∫ g ⟨η, S⟩ e^{−⟨θ,S⟩} dν = ⟨η, (N_{g S_j}(θ))_j⟩`. -/
theorem integral_mul_dirLoss_mul_famWeight {g : X → ℝ} (hg : Bdd g) (θ η : J → ℝ) :
    ∫ x, g x * dirLoss S η x * famWeight S θ x ∂ν =
      dotJ η (fun j ↦ famNum S ν (fun x ↦ g x * S j x) θ) := by
  have e : ∀ x, g x * dirLoss S η x * famWeight S θ x =
      ∑ j, η j * (g x * S j x * famWeight S θ x) := fun x ↦ by
    simp only [dirLoss, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ ↦ (integrable_mul_famWeight hS ν (hg.mul (hS j)) θ).const_mul _]
  simp only [integral_const_mul, dotJ, famNum]

omit [Nonempty J] in
/-- **The weighted normaliser is differentiable**, with derivative `−⟨·, (N_{g S_j}(θ))_j⟩`. -/
theorem hasFDerivAt_famNum {g : X → ℝ} (hg : Bdd g) (θ₀ : J → ℝ) :
    HasFDerivAt (famNum S ν g) (-dotCLM (fun j ↦ famNum S ν (fun x ↦ g x * S j x) θ₀)) θ₀ := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  obtain ⟨B, hB⟩ := hg.2
  obtain ⟨hint, hD⟩ := hasFDerivAt_affNum (μ := ν) (π := fun _ ↦ (1 : ℝ))
    (L₀ := fun _ ↦ (0 : ℝ)) measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
    measurable_const h0 hS (φ := g) hg.1 (Mφ := B) hB one_pos θ₀
  have e : (fun a : J → ℝ ↦ ∫ x, g x *
      Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S a x)) * (fun _ : X ↦ (1 : ℝ)) x ∂ν) =
      famNum S ν g := by
    funext a
    simp [famNum, famWeight, affLoss, dirLoss]
  rw [e] at hD
  refine hD.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun η ↦ ?_
  rw [ContinuousLinearMap.integral_apply hint η]
  have e2 : ∀ x, ((-(1 * (g x * Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ₀ x)) *
      (fun _ : X ↦ (1 : ℝ)) x))) • dirCLM S x) η =
      -(g x * dirLoss S η x * famWeight S θ₀ x) := fun x ↦ by
    rw [smul_apply, dirCLM_apply, smul_eq_mul]
    simp only [famWeight, affLoss, dirLoss, zero_add, one_mul, mul_one]
    ring
  simp_rw [e2]
  rw [integral_neg, integral_mul_dirLoss_mul_famWeight hS ν hg, neg_apply,
    dotCLM_apply]

omit [Nonempty J] in
/-- **The weighted normaliser is `C^n` for every `n`**, by induction: its derivative is a
weighted normaliser again. -/
theorem contDiff_famNum (n : ℕ) : ∀ {g : X → ℝ}, Bdd g → ContDiff ℝ n (famNum S ν g) := by
  induction n with
  | zero =>
    intro g hg
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun θ ↦
      (hasFDerivAt_famNum hS ν hg θ).continuousAt)
  | succ n ih =>
    intro g hg
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv.2 ⟨fun θ ↦ (hasFDerivAt_famNum hS ν hg θ).differentiableAt,
      fun h ↦ absurd h (WithTop.natCast_ne_top n), ?_⟩
    have e : fderiv ℝ (famNum S ν g) =
        fun θ ↦ -dotCLMlin (fun j ↦ famNum S ν (fun x ↦ g x * S j x) θ) := by
      funext θ
      rw [(hasFDerivAt_famNum hS ν hg θ).fderiv, dotCLMlin_apply]
    rw [e]
    exact ((dotCLMlin (J := J)).contDiff.comp (contDiff_pi.2 fun j ↦ ih (hg.mul (hS j)))).neg

omit [Nonempty J] in
/-- The weighted normaliser is `C^∞`. -/
theorem contDiff_infty_famNum {g : X → ℝ} (hg : Bdd g) : ContDiff ℝ ∞ (famNum S ν g) :=
  contDiff_infty.2 fun n ↦ contDiff_famNum hS ν n hg

omit [Nonempty J] in
/-- The normaliser is `C^∞`. -/
theorem contDiff_famZ : ContDiff ℝ ∞ (famZ S ν) := by
  rw [famZ_eq_famNum ν]
  exact contDiff_infty_famNum hS ν (Bdd.const 1)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The mean map in weighted-normaliser form: `m_j(θ) = N_{S_j}(θ) / N_1(θ)`. -/
theorem famMean_eq_famNum_div (θ : J → ℝ) (j : J) :
    famMean S ν θ j = famNum S ν (S j) θ / famZ S ν θ := by
  simp only [famMean, famDens, famNum]
  rw [← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [mul_div_assoc]

omit [Nonempty J] in
/-- **The mean map is `C^∞`.** -/
theorem contDiff_famMean : ContDiff ℝ ∞ (famMean S ν) := by
  refine contDiff_pi.2 fun j ↦ ?_
  have e : (fun θ ↦ famMean S ν θ j) = fun θ ↦ famNum S ν (S j) θ / famZ S ν θ := by
    funext θ
    exact famMean_eq_famNum_div ν θ j
  rw [e]
  exact (contDiff_infty_famNum hS ν (hS j)).div (contDiff_famZ hS ν) fun θ ↦ (famZ_pos hS ν θ).ne'

omit [Nonempty J] in
/-- **The mean map is `C^∞`** (in the seabed's `meanMap` form). -/
theorem contDiff_meanMap : ContDiff ℝ ∞ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1) := by
  have e : meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 = famMean S ν := by
    funext θ
    exact (famMean_eq_meanMap hS ν θ).symm
  rw [e]
  exact contDiff_famMean hS ν

omit [Nonempty J] in
/-- The Jacobian of the mean map is its Fréchet derivative. -/
theorem meanMapDeriv_eq_fderiv (θ : J → ℝ) :
    meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ =
      fderiv ℝ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1) θ := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hZ : priorZ ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 ≠ 0 := by
    rw [← famZ_eq_priorZ ν]
    exact (famZ_pos hS ν θ).ne'
  exact (hasFDerivAt_meanMap measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
    measurable_const h0 hS one_pos hZ).fderiv.symm

omit [Nonempty J] in
/-- **The Jacobian of the mean map is `C^∞`.** -/
theorem contDiff_meanMapDeriv :
    ContDiff ℝ ∞ (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1) := by
  have e : meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 =
      fderiv ℝ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1) := by
    funext θ
    exact meanMapDeriv_eq_fderiv hS ν θ
  rw [e]
  exact (contDiff_infty_iff_fderiv.1 (contDiff_meanMap hS ν)).2

/-- **The intrinsic chart `chartV : 𝕍 → 𝕍` is `C^∞`.** -/
theorem contDiff_chartV :
    ContDiff ℝ ∞ (chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS) := by
  have e : chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS =
      fun θ : 𝕍 ↦ dirProjL S ν (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ - m₀) := by
    funext θ
    refine Subtype.ext ?_
    rw [chartV_apply, dirProjL_of_mem ν (meanMap_sub_mem_dirSpan measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS _ _)]
  rw [e]
  exact (dirProjL S ν).contDiff.comp
    (((contDiff_meanMap hS ν).comp (𝕍).subtypeL.contDiff).sub contDiff_const)

/-- The chart derivative in projected form: `chartDeriv θ v = π (Dm(θ) v)`. -/
theorem chartDeriv_eq_dirProjL (θ : 𝕍) (v : 𝕍) :
    chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS θ v =
      dirProjL S ν (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ v) := by
  refine Subtype.ext ?_
  rw [dirProjL_of_mem ν (meanMapDeriv_mem_dirSpan measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS θ v)]
  rfl

/-- **The chart derivative is `C^∞`** as a map `𝕍 → (𝕍 →L 𝕍)`. -/
theorem contDiff_chartDeriv :
    ContDiff ℝ ∞ (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS) := by
  refine contDiff_clm_apply_iff.2 fun v ↦ ?_
  have e : (fun θ : 𝕍 ↦ chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ v) = fun θ : 𝕍 ↦ dirProjL S ν
        (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ v) := by
    funext θ
    exact chartDeriv_eq_dirProjL hS ν θ v
  rw [e]
  exact (dirProjL S ν).contDiff.comp
    (((contDiff_meanMapDeriv hS ν).comp (𝕍).subtypeL.contDiff).clm_apply contDiff_const)

/-- **The inverse chart derivative is `C^∞`**: `θ ↦ (Dm(θ)|_𝕍)⁻¹`. -/
theorem contDiff_chartDerivEquiv_symm :
    ContDiff ℝ ∞ (fun θ : 𝕍 ↦ ((CDE θ).symm : 𝕍 →L[ℝ] 𝕍)) := by
  refine contDiff_iff_contDiffAt.2 fun θ₀ ↦ ?_
  have e : (fun θ : 𝕍 ↦ ((CDE θ).symm : 𝕍 →L[ℝ] 𝕍)) = fun θ : 𝕍 ↦
      ContinuousLinearMap.inverse (chartDeriv measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (one_integral_pos ν) hS θ) := by
    funext θ
    rw [← coe_chartDerivEquiv, ContinuousLinearMap.inverse_equiv]
  rw [e]
  have h1 := contDiffAt_map_inverse (n := ∞) (CDE θ₀)
  rw [coe_chartDerivEquiv] at h1
  exact h1.comp θ₀ (contDiff_chartDeriv hS ν).contDiffAt

end Laplace.Multi
