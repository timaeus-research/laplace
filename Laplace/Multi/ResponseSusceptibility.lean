/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.IntrinsicLegendre
import Laplace.Multi.DualPotential
import Laplace.Multi.DataResponseMap
import Laplace.Multi.ConditioningChainRule
import Laplace.Multi.MeanSegment

/-!
# The differential of the data-to-response map

The intrinsic Legendre chart (`IntrinsicLegendre`) gives the natural coordinates `θ(M) ∈ 𝕍` of
every response `M` in the relative interior, differentiably. This file differentiates the rate
and follows a data path through the chart:

* `hasFDerivAt_famKL_zero`: `D_θ 𝓘(m(θ))[w] = −⟨θ, Dm(θ) w⟩` (the envelope identity: the
  log-partition gradient cancels against the response).
* `hasFDerivAt_rateFun_chart` / `hasFDerivAt_genRate_chart`: **the intrinsic gradient of the rate is
  the natural coordinate**, `D_M 𝓘(M)[u] = −⟨θ(M), u⟩` for `u ∈ 𝕍` (in the seabed's sign
  convention `P_θ ∝ e^{−⟨θ,S⟩} ν`).
* Along the data path `D_s = ν.tilted (s h)` with responses `M(s)`: `pathV` is `M(s) − m₀ ∈ 𝕍`,
  `dataCov s = Cov_{D_s}(S, h)` its velocity (`hasDerivAt_pathV`), `dataTheta s = θ(M(s))` the
  natural coordinates, with **`hasDerivAt_dataTheta`**:
  `θ'(s) = (Dm(θ(s))|_𝕍)⁻¹ Cov_{D_s}(S, h)` — the data-side forcing `Cov_{D_s}(S, h)` composed with
  the response-side susceptibility — and **`hasDerivAt_genRate_dataPath`**:
  `d/ds 𝓘(M(s)) = −⟨θ(M(s)), Cov_{D_s}(S, h)⟩`.

Velocities of paths in a closed subspace stay in the subspace (`mem_of_hasDerivAt_subtype`), so no
further invisibility argument is needed for the data velocity.
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal

namespace Laplace.Multi

section Subtype

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The velocity of a differentiable path in a closed subspace lies in the subspace. -/
theorem mem_of_hasDerivAt_subtype {V : Submodule ℝ E} (hV : IsClosed (V : Set E)) {γ : ℝ → V}
    {w : E} {s₀ : ℝ} (h : HasDerivAt (fun s ↦ (γ s : E)) w s₀) : w ∈ V := by
  rw [hasDerivAt_iff_tendsto_slope] at h
  refine hV.mem_of_tendsto h (Eventually.of_forall fun s ↦ ?_)
  simp only [slope_def_module, SetLike.mem_coe]
  exact V.smul_mem _ (V.sub_mem (γ s).2 (γ s₀).2)

/-- A path into a submodule is differentiable as soon as its composite with the inclusion is. -/
theorem hasDerivAt_subtype_of_hasDerivAt {V : Submodule ℝ E} {γ : ℝ → V} {w : E} (hw : w ∈ V)
    {s₀ : ℝ} (h : HasDerivAt (fun s ↦ (γ s : E)) w s₀) : HasDerivAt γ ⟨w, hw⟩ s₀ := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  rw [← isLittleO_norm_left] at h ⊢
  refine h.congr_left fun s ↦ ?_
  rw [Submodule.coe_norm, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul]

end Subtype

section Chart

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : Type*} [Fintype J] [Nonempty J]
variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hπm hπi hπ hπpos hS

omit [Nonempty J] in
/-- **The envelope identity**: `D_θ 𝓘(m(θ))[w] = −⟨θ, Dm(θ) w⟩`. -/
theorem hasFDerivAt_famKL_zero (θ₀ : J → ℝ) :
    HasFDerivAt (fun θ ↦ famKL μ π (fun _ ↦ (0 : ℝ)) S 1 θ 0)
      (-(dotCLM θ₀).comp (meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀)) θ₀ := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hA := hasFDerivAt_affLogZ hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS one_pos
    θ₀
  have hm := (hasStrictFDerivAt_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS
    one_pos θ₀).hasFDerivAt
  have hfun : (fun θ ↦ famKL μ π (fun _ ↦ (0 : ℝ)) S 1 θ 0) = fun θ ↦
      affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 0 - affLogZ μ π (fun _ ↦ (0 : ℝ)) S 1 θ +
        1 * ∑ i, ((0 : J → ℝ) i - θ i) * meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ i :=
    funext fun θ ↦ famKL_eq hπm hπi hπ hπpos measurable_const h0 hS θ 0
  rw [hfun]
  have hsum : HasFDerivAt
      (fun θ ↦ ∑ i, ((0 : J → ℝ) i - θ i) * meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ i)
      (∑ i, (((0 : J → ℝ) i - θ₀ i) •
          (ContinuousLinearMap.proj i).comp (meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀) +
        meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ i • (0 - ContinuousLinearMap.proj i))) θ₀ := by
    refine HasFDerivAt.fun_sum fun i _ ↦ ?_
    exact ((hasFDerivAt_const _ _).sub (hasFDerivAt_apply i θ₀)).mul (hasFDerivAt_pi'.1 hm i)
  refine (((hasFDerivAt_const _ _).sub hA).add (hsum.const_mul 1)).congr_fderiv ?_
  ext w
  simp only [add_apply, smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.proj_apply, dotCLM_apply, dotJ, smul_eq_mul, Pi.zero_apply, zero_sub,
    neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, one_mul]
  have e1 : ∑ i, meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ i * w i =
      ∑ i, w i * meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ i :=
    Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have e2 : ∑ i, meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ w i * θ₀ i =
      ∑ i, θ₀ i * meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ w i :=
    Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [e1, e2]
  ring

/-- The chart is strictly differentiable with derivative the equivalence `chartDerivEquiv`. -/
theorem hasStrictFDerivAt_chartV_equiv (θ₀ : dirSpan μ π S) :
    HasStrictFDerivAt (chartV hπm hπi hπ hπpos hS)
      (chartDerivEquiv hπm hπi hπ hπpos hS θ₀ : dirSpan μ π S →L[ℝ] dirSpan μ π S) θ₀ := by
  rw [coe_chartDerivEquiv]
  exact hasStrictFDerivAt_chartV hπm hπi hπ hπpos hS θ₀

/-- The image of the chart is a neighbourhood of each of its points. -/
theorem eventually_mem_intrinsicInterior_chartV (θ₀ : dirSpan μ π S) :
    ∀ᶠ v : dirSpan μ π S in 𝓝 (chartV hπm hπi hπ hπpos hS θ₀),
      meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + (v : J → ℝ) ∈
        intrinsicInterior ℝ (momentBody μ π S) := by
  filter_upwards [(hasStrictFDerivAt_chartV_equiv hπm hπi hπ hπpos hS θ₀).eventually_right_inverse]
    with v hv
  rw [← hv, chartV_apply, add_sub_cancel,
    ← range_meanMap_eq_intrinsicInterior_momentBody hπm hπi hπ hπpos hS]
  exact ⟨_, rfl⟩

/-- On the image of the chart, the rate is `famKL` of the natural coordinates. -/
theorem rateFun_eq_famKL_chartVInv {v : dirSpan μ π S}
    (hv : meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + (v : J → ℝ) ∈
      intrinsicInterior ℝ (momentBody μ π S)) :
    (rateFun μ π (fun _ ↦ (0 : ℝ)) S 1 (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + v)).toReal =
      famKL μ π (fun _ ↦ (0 : ℝ)) S 1 (chartVInv hπm hπi hπ hπpos hS v) 0 := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have h := congrArg Subtype.val (chartV_chartVInv hπm hπi hπ hπpos hS hv)
  rw [chartV_apply] at h
  have hM : meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + (v : J → ℝ) =
      meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 (chartVInv hπm hπi hπ hπpos hS v) := by
    rw [← h]
    abel
  rw [hM, rateFun_meanMap hπm hπi hπ hπpos measurable_const h0 hS one_pos,
    ENNReal.toReal_ofReal (famKL_nonneg hπm hπi hπ hπpos measurable_const h0 hS one_pos _ _)]

/-- **The intrinsic gradient of the rate is the natural coordinate**:
`D_M 𝓘(M)[u] = −⟨θ(M), u⟩` for `u ∈ 𝕍`, at `M = m(θ₀)` in chart coordinates. -/
theorem hasFDerivAt_rateFun_chart (θ₀ : dirSpan μ π S) :
    HasFDerivAt (fun v : dirSpan μ π S ↦
        (rateFun μ π (fun _ ↦ (0 : ℝ)) S 1 (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + v)).toReal)
      (-(dotCLM (θ₀ : J → ℝ)).comp (dirSpan μ π S).subtypeL) (chartV hπm hπi hπ hπpos hS θ₀) := by
  have hinv := (hasStrictFDerivAt_chartVInv hπm hπi hπ hπpos hS θ₀).hasFDerivAt
  have hval : HasFDerivAt (fun v : dirSpan μ π S ↦ (chartVInv hπm hπi hπ hπpos hS v : J → ℝ))
      ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S))
      (chartV hπm hπi hπ hπpos hS θ₀) :=
    (dirSpan μ π S).subtypeL.hasFDerivAt.comp _ hinv
  have hF := hasFDerivAt_famKL_zero hπm hπi hπ hπpos hS (θ₀ : J → ℝ)
  have e : ((chartVInv hπm hπi hπ hπpos hS (chartV hπm hπi hπ hπpos hS θ₀) : dirSpan μ π S) :
      J → ℝ) = θ₀ := by
    rw [chartVInv_chartV]
  have hF' : HasFDerivAt (fun θ ↦ famKL μ π (fun _ ↦ (0 : ℝ)) S 1 θ 0)
      (-(dotCLM (θ₀ : J → ℝ)).comp (meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀))
      ((chartVInv hπm hπi hπ hπpos hS (chartV hπm hπi hπ hπpos hS θ₀) : dirSpan μ π S) :
        J → ℝ) := by
    rw [e]
    exact hF
  have hcomp := hF'.comp (chartV hπm hπi hπ hπpos hS θ₀) hval
  refine (hcomp.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · filter_upwards [eventually_mem_intrinsicInterior_chartV hπm hπi hπ hπpos hS θ₀] with v hv
    exact rateFun_eq_famKL_chartVInv hπm hπi hπ hπpos hS hv
  · ext u
    have hcd : ∀ w,
        chartDerivEquiv hπm hπi hπ hπpos hS θ₀ w = chartDeriv hπm hπi hπ hπpos hS θ₀ w :=
      fun w ↦ by
        rw [← coe_chartDerivEquiv hπm hπi hπ hπpos hS θ₀]
        rfl
    have hu : meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm u) = u := by
      rw [← chartDeriv_apply hπm hπi hπ hπpos hS θ₀, ← hcd, ContinuousLinearEquiv.apply_symm_apply]
    simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearEquiv.coe_coe,
      Submodule.subtypeL_apply, hu]

end Chart

section Law

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Nonempty J] hS in
/-- The featureless natural coordinate responds with the mean of the law. -/
theorem meanMap_zero_eq_mean :
    meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 = fun i ↦ ∫ x, S i x ∂ν := by
  funext i
  simp [meanMap, priorExp, priorZ, affLoss]

/-- **The intrinsic gradient of the rate of a law is the natural coordinate**:
`D_M 𝓘_ν(M)[u] = −⟨θ(M), u⟩` for `u ∈ 𝕍`. -/
theorem hasFDerivAt_genRate_chart (θ₀ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    HasFDerivAt (fun v : dirSpan ν (fun _ ↦ (1 : ℝ)) S ↦
        (genRate ν S (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 + v)).toReal)
      (-(dotCLM (θ₀ : J → ℝ)).comp (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL)
      (chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (by simp) hS θ₀) := by
  simp_rw [genRate_eq_rateFun]
  exact hasFDerivAt_rateFun_chart measurable_const (integrable_const 1) (fun _ ↦ one_pos) (by simp)
    hS θ₀

omit [Nonempty X] [Nonempty J] in
variable (S) in
/-- The data-side forcing: `Cov_{D_s}(S, h)` along `D_s = ν.tilted (s h)`. -/
noncomputable def dataCov (h : X → ℝ) (s : ℝ) : J → ℝ := fun i ↦
  ∫ x, S i x * h x ∂ν.tilted (fun x ↦ s * h x) -
    (∫ x, S i x ∂ν.tilted (fun x ↦ s * h x)) * ∫ x, h x ∂ν.tilted (fun x ↦ s * h x)

variable {h : X → ℝ} (hh : Bdd h)
include hh

/-- **The data path in the direction subspace**: `M(s) − m₀` for `D_s = ν.tilted (s h)`. -/
noncomputable def pathV (s : ℝ) : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  ⟨(fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x)) -
      meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0, by
    have h1 := AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ (intrinsicInterior_subset
        (mean_tilted_mem_intrinsicInterior hS ν (Bdd.const_mul s hh))))
      (mem_affineSpan ℝ (meanMap_mem_momentBody measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (by simp) hS 0))
    rwa [vsub_eq_sub] at h1⟩

theorem pathV_apply (s : ℝ) :
    (pathV hS ν hh s : J → ℝ) = (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x)) -
      meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 := rfl

/-- The ambient velocity of the data response is the covariance with `h`. -/
theorem hasDerivAt_pathV_val (s₀ : ℝ) :
    HasDerivAt (fun s ↦ (pathV hS ν hh s : J → ℝ)) (dataCov S ν h s₀) s₀ := by
  have hpi : HasDerivAt (fun s ↦ fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x))
      (dataCov S ν h s₀) s₀ :=
    hasDerivAt_pi.2 fun i ↦ hasDerivAt_dataResponsePath hS ν hh i s₀
  exact hpi.sub_const _

set_option linter.unusedFintypeInType false in
/-- The data velocity lies in the direction subspace. -/
theorem dataCov_mem_dirSpan (s₀ : ℝ) : dataCov S ν h s₀ ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  mem_of_hasDerivAt_subtype (Submodule.closed_of_finiteDimensional _)
    (hasDerivAt_pathV_val hS ν hh s₀)

/-- **The velocity of the data path is `Cov_{D_s}(S, h)`.** -/
theorem hasDerivAt_pathV (s₀ : ℝ) :
    HasDerivAt (pathV hS ν hh) ⟨dataCov S ν h s₀, dataCov_mem_dirSpan hS ν hh s₀⟩ s₀ :=
  hasDerivAt_subtype_of_hasDerivAt _ (hasDerivAt_pathV_val hS ν hh s₀)

/-- **The natural coordinates of the data response** `θ(M(s))`. -/
noncomputable def dataTheta (s : ℝ) : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (by simp) hS (pathV hS ν hh s)

theorem chartV_dataTheta (s : ℝ) :
    chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (by simp) hS
      (dataTheta hS ν hh s) = pathV hS ν hh s := by
  apply chartV_chartVInv
  rw [pathV_apply, add_sub_cancel]
  exact mean_tilted_mem_intrinsicInterior hS ν (Bdd.const_mul s hh)

/-- **The natural coordinates move by the susceptibility applied to the data forcing**:
`θ'(s) = (Dm(θ(s))|_𝕍)⁻¹ Cov_{D_s}(S, h)`. -/
theorem hasDerivAt_dataTheta (s₀ : ℝ) :
    HasDerivAt (dataTheta hS ν hh)
      ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (by simp) hS
          (dataTheta hS ν hh s₀)).symm
        ⟨dataCov S ν h s₀, dataCov_mem_dirSpan hS ν hh s₀⟩) s₀ := by
  have hinv := (hasStrictFDerivAt_chartVInv measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (by simp) hS (dataTheta hS ν hh s₀)).hasFDerivAt
  rw [chartV_dataTheta] at hinv
  exact hinv.comp_hasDerivAt s₀ (hasDerivAt_pathV hS ν hh s₀)

/-- **The rate along the data path**: `d/ds 𝓘_ν(M(s)) = −⟨θ(M(s)), Cov_{D_s}(S, h)⟩`. -/
theorem hasDerivAt_genRate_dataPath (s₀ : ℝ) :
    HasDerivAt (fun s ↦ (genRate ν S (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x))).toReal)
      (-dotJ (dataTheta hS ν hh s₀ : J → ℝ) (dataCov S ν h s₀)) s₀ := by
  have hF := hasFDerivAt_genRate_chart hS ν (dataTheta hS ν hh s₀)
  rw [chartV_dataTheta] at hF
  have hc := hF.comp_hasDerivAt s₀ (hasDerivAt_pathV hS ν hh s₀)
  refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp only [Function.comp, pathV_apply, add_sub_cancel]
  · simp only [ContinuousLinearMap.comp_apply, neg_apply, Submodule.subtypeL_apply, dotCLM_apply]
    rw [dotJ_comm]

end Law

end Laplace.Multi
