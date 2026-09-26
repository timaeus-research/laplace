/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.InvisibleInformation
import Laplace.Multi.DataQuotient

/-!
# The response differential for arbitrary response paths and arbitrary observables

`ResponseSusceptibility` followed the exponential data path. The differential of the response map
depends only on the path of responses: for any path `M : ℝ → J → ℝ` in the moment body,
differentiable at `s₀` with `M s₀` in the relative interior,

* `hasDerivAt_pathTheta`: `θ'(s₀) = (Dm(θ(s₀))|_𝕍)⁻¹ M'(s₀)`;
* `hasDerivAt_rateFun_path` / `hasDerivAt_genRate_path`: `d/ds 𝓘(M(s)) = −⟨θ(M(s₀)), M'(s₀)⟩`.

Every bounded observable has a differential over the response manifold, not only the selected
statistics: with `obsV φ v = E_{P_{θ(v)}} φ`,

* `hasFDerivAt_obsV`: `D(obsV φ)(v)[u] = −Cov_{θ(v)}(φ, ⟨(Dm|_𝕍)⁻¹ u, S⟩)`
  (in the convention `P_θ ∝ e^{−⟨θ,S⟩}ν`, `Dm = −C`, this is `Cov_θ(φ, ⟨C⁻¹u, S⟩)`);
* `responseProjection_eq_familyMeasure_chartVInv` identifies the canonical representative with the
  family member at the chart coordinates, so `hasDerivAt_integral_responseProjection_path` reads
  `d/ds E_{Π(M(s))} φ = −Cov_{Π(M(s₀))}(φ, ⟨θ'(s₀), S⟩)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Chart

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : Type*} [Fintype J] [Nonempty J]
variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hπm hπi hπ hπpos hS

open Classical in
variable (μ π S) in
/-- A response translated to the direction subspace (zero when the difference is not visible). -/
noncomputable def toV (M : J → ℝ) : dirSpan μ π S :=
  if h : M - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 ∈ dirSpan μ π S then ⟨_, h⟩ else 0

omit [Nonempty J] [Nonempty X] hπm hπi hπ hπpos hS in
theorem toV_apply {M : J → ℝ} (hM : M - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 ∈ dirSpan μ π S) :
    (toV μ π S M : J → ℝ) = M - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 := by
  unfold toV
  rw [dif_pos hM]

/-- Points of the moment body have visible differences from the featureless response. -/
theorem sub_mem_dirSpan_of_mem_momentBody {M : J → ℝ} (hM : M ∈ momentBody μ π S) :
    M - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 ∈ dirSpan μ π S := by
  have h := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hM)
    (mem_affineSpan ℝ (meanMap_mem_momentBody hπm hπi hπ hπpos hS 0))
  rwa [vsub_eq_sub] at h

/-- The natural coordinates of a response, `θ(M)`. -/
noncomputable def responseTheta (M : J → ℝ) : dirSpan μ π S :=
  chartVInv hπm hπi hπ hπpos hS (toV μ π S M)

theorem chartV_responseTheta {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody μ π S)) :
    chartV hπm hπi hπ hπpos hS (responseTheta hπm hπi hπ hπpos hS M) =
      toV μ π S M := by
  apply chartV_chartVInv
  rw [toV_apply
    (sub_mem_dirSpan_of_mem_momentBody hπm hπi hπ hπpos hS (intrinsicInterior_subset hrel)),
    add_sub_cancel]
  exact hrel

/-- The chart coordinates recover the response: `m(θ(M)) = M` on the relative interior. -/
theorem meanMap_responseTheta {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody μ π S)) :
    meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 (responseTheta hπm hπi hπ hπpos hS M) = M := by
  have h := congrArg Subtype.val (chartV_responseTheta hπm hπi hπ hπpos hS hrel)
  rw [chartV_apply, toV_apply
    (sub_mem_dirSpan_of_mem_momentBody hπm hπi hπ hπpos hS (intrinsicInterior_subset hrel))] at h
  exact sub_left_inj.1 h

variable {M : ℝ → J → ℝ} (hV : ∀ s, M s - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 ∈ dirSpan μ π S)
include hV

omit [Nonempty J] [Nonempty X] hπm hπi hπ hπpos hS in
/-- The velocity of a visible response path lies in the direction subspace. -/
theorem deriv_mem_dirSpan_of_path {M' : J → ℝ} {s₀ : ℝ} (hM' : HasDerivAt M M' s₀) :
    M' ∈ dirSpan μ π S :=
  mem_of_hasDerivAt_subtype (Submodule.closed_of_finiteDimensional _)
    (γ := fun s ↦ toV μ π S (M s)) (by
      have e : (fun s ↦ (toV μ π S (M s) : J → ℝ)) =
          fun s ↦ M s - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 :=
        funext fun s ↦ toV_apply (hV s)
      rw [e]
      exact hM'.sub_const _)

omit [Nonempty J] [Nonempty X] hπm hπi hπ hπpos hS in
theorem hasDerivAt_toV_path {M' : J → ℝ} {s₀ : ℝ} (hM' : HasDerivAt M M' s₀) :
    HasDerivAt (fun s ↦ toV μ π S (M s))
      ⟨M', deriv_mem_dirSpan_of_path hV hM'⟩ s₀ :=
  hasDerivAt_subtype_of_hasDerivAt _ (by
    have e : (fun s ↦ (toV μ π S (M s) : J → ℝ)) =
        fun s ↦ M s - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 :=
      funext fun s ↦ toV_apply (hV s)
    rw [e]
    exact hM'.sub_const _)

/-- **The natural coordinates move by the susceptibility applied to the response velocity**:
`θ'(s₀) = (Dm(θ(s₀))|_𝕍)⁻¹ M'(s₀)` along any differentiable response path. -/
theorem hasDerivAt_responseTheta_path {M' : J → ℝ} {s₀ : ℝ}
    (hrel : M s₀ ∈ intrinsicInterior ℝ (momentBody μ π S)) (hM' : HasDerivAt M M' s₀) :
    HasDerivAt (fun s ↦ responseTheta hπm hπi hπ hπpos hS (M s))
      ((chartDerivEquiv hπm hπi hπ hπpos hS (responseTheta hπm hπi hπ hπpos hS (M s₀))).symm
        ⟨M', deriv_mem_dirSpan_of_path hV hM'⟩) s₀ := by
  have hinv := (hasStrictFDerivAt_chartVInv hπm hπi hπ hπpos hS
    (responseTheta hπm hπi hπ hπpos hS (M s₀))).hasFDerivAt
  rw [chartV_responseTheta hπm hπi hπ hπpos hS hrel] at hinv
  exact hinv.comp_hasDerivAt s₀ (hasDerivAt_toV_path hV hM')

/-- **The rate along any response path**: `d/ds 𝓘(M(s)) = −⟨θ(M(s₀)), M'(s₀)⟩`. -/
theorem hasDerivAt_rateFun_path {M' : J → ℝ} {s₀ : ℝ}
    (hrel : M s₀ ∈ intrinsicInterior ℝ (momentBody μ π S)) (hM' : HasDerivAt M M' s₀) :
    HasDerivAt (fun s ↦ (rateFun μ π (fun _ ↦ (0 : ℝ)) S 1 (M s)).toReal)
      (-dotJ (responseTheta hπm hπi hπ hπpos hS (M s₀) : J → ℝ) M') s₀ := by
  have hF := hasFDerivAt_rateFun_chart hπm hπi hπ hπpos hS
    (responseTheta hπm hπi hπ hπpos hS (M s₀))
  rw [chartV_responseTheta hπm hπi hπ hπpos hS hrel] at hF
  have hc := hF.comp_hasDerivAt s₀ (hasDerivAt_toV_path hV hM')
  refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp only [Function.comp, toV_apply (hV s), add_sub_cancel]
  · simp only [ContinuousLinearMap.comp_apply, neg_apply, Submodule.subtypeL_apply, dotCLM_apply]
    rw [dotJ_comm]

omit hV in
/-- A bounded observable as a function of the chart coordinates: `obsV φ v = E_{P_{θ(v)}} φ`. -/
noncomputable def obsV (φ : X → ℝ) (v : dirSpan μ π S) : ℝ :=
  priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) S (chartVInv hπm hπi hπ hπpos hS v)) φ 1

omit hV in
/-- **The differential of every bounded observable over the response manifold**:
`D(obsV φ)(v)[u] = −Cov_{θ(v)}(φ, ⟨(Dm|_𝕍)⁻¹ u, S⟩)`. -/
theorem hasFDerivAt_obsV {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
    (θ₀ : dirSpan μ π S) :
    HasFDerivAt (obsV hπm hπi hπ hπpos hS φ)
      ((obsMapDeriv μ π (fun _ ↦ (0 : ℝ)) φ S 1 θ₀).comp ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S)))
      (chartV hπm hπi hπ hπpos hS θ₀) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hinv := (hasStrictFDerivAt_chartVInv hπm hπi hπ hπpos hS θ₀).hasFDerivAt
  have hval : HasFDerivAt (fun v : dirSpan μ π S ↦ (chartVInv hπm hπi hπ hπpos hS v : J → ℝ))
      ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S))
      (chartV hπm hπi hπ hπpos hS θ₀) :=
    (dirSpan μ π S).subtypeL.hasFDerivAt.comp _ hinv
  have e : ((chartVInv hπm hπi hπ hπpos hS (chartV hπm hπi hπ hπpos hS θ₀) : dirSpan μ π S) :
      J → ℝ) = θ₀ := by
    rw [chartVInv_chartV]
  have hobs : HasFDerivAt (fun a ↦ priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) S a) φ 1)
      (obsMapDeriv μ π (fun _ ↦ (0 : ℝ)) φ S 1 θ₀)
      ((chartVInv hπm hπi hπ hπpos hS (chartV hπm hπi hπ hπpos hS θ₀) : dirSpan μ π S) :
        J → ℝ) := by
    rw [e]
    exact hasFDerivAt_obsMap hπm hπi hπ hπpos measurable_const h0 hS hφm hφ one_pos θ₀
  exact hobs.comp (chartV hπm hπi hπ hπpos hS θ₀) hval

omit hV in
/-- The observable differential in covariance form. -/
theorem obsV_deriv_apply {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
    (θ₀ u : dirSpan μ π S) :
    ((obsMapDeriv μ π (fun _ ↦ (0 : ℝ)) φ S 1 θ₀).comp ((dirSpan μ π S).subtypeL.comp
        ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S))) u =
      -priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) φ
        (dirLoss S ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm u)) 1 := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Submodule.subtypeL_apply]
  rw [obsMapDeriv_apply hπm hπi hπ hπpos measurable_const h0 hS hφm hφ one_pos]
  ring

end Chart

section Law

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The canonical representative of a relative-interior response is the family member at its
chart coordinates.** -/
theorem responseProjection_eq_familyMeasure_responseTheta {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    responseProjection hS ν M = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS M) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hmean := meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel
  have hfin : genRate ν S M ≠ ⊤ := by
    rw [genRate_eq_rateFun, ← hmean, rateFun_meanMap measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const h0 hS one_pos]
    exact ENNReal.ofReal_ne_top
  obtain ⟨hP, hM, hkl, -⟩ := responseProjection_spec hS ν hfin
  have := hP
  have hmean' : (fun i ↦ ∫ x, S i x ∂responseProjection hS ν M) =
      meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS M) := by
    rw [hM, hmean]
  refine (klDiv_eq_rateFun_iff measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) measurable_const h0 hS one_pos _ _ hmean').1 ?_
  rw [familyMeasure_one_zero, hkl, genRate_eq_rateFun, hmean]

/-- The expectation of an observable under the canonical representative, in chart form. -/
theorem integral_responseProjection_eq {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (φ : X → ℝ) :
    ∫ x, φ x ∂responseProjection hS ν M =
      obsV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS φ
        (toV ν (fun _ ↦ (1 : ℝ)) S M) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hrel]
  exact integral_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) measurable_const h0 hS _ φ

omit [Nonempty X] [Nonempty J] in
/-- The family covariance is the covariance under the family member. -/
theorem priorCov_eq_lawCov_familyMeasure (θ : J → ℝ) (φ ψ : X → ℝ) :
    priorCov ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S θ) φ ψ 1 =
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) φ ψ := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  unfold priorCov lawCov
  rw [integral_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const h0 hS θ (fun x ↦ φ x * ψ x),
    integral_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const h0 hS θ φ,
    integral_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const h0 hS θ ψ]

/-- **The rate of a law along any response path**: `d/ds 𝓘_ν(M(s)) = −⟨θ(M(s₀)), M'(s₀)⟩`. -/
theorem hasDerivAt_genRate_path {M : ℝ → J → ℝ}
    (hV : ∀ s, M s - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈
      dirSpan ν (fun _ ↦ (1 : ℝ)) S) {M' : J → ℝ} {s₀ : ℝ}
    (hrel : M s₀ ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hM' : HasDerivAt M M' s₀) :
    HasDerivAt (fun s ↦ (genRate ν S (M s)).toReal)
      (-dotJ (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (M s₀) : J → ℝ) M') s₀ := by
  simp_rw [genRate_eq_rateFun]
  exact hasDerivAt_rateFun_path measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hV hrel hM'

/-- **Every bounded observable responds along any response path**:
`d/ds E_{Π(M(s))} φ = −Cov_{Π(M(s₀))}(φ, ⟨θ'(s₀), S⟩)` with `θ'(s₀) = (Dm|_𝕍)⁻¹ M'(s₀)`. -/
theorem hasDerivAt_integral_responseProjection_path {M : ℝ → J → ℝ}
    (hV : ∀ s, M s - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈
      dirSpan ν (fun _ ↦ (1 : ℝ)) S) {M' : J → ℝ} {s₀ : ℝ}
    (hrel : ∀ᶠ s in 𝓝 s₀, M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hM' : HasDerivAt M M' s₀) {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ}
    (hφ : ∀ x, |φ x| ≤ Mφ) :
    HasDerivAt (fun s ↦ ∫ x, φ x ∂responseProjection hS ν (M s))
      (-lawCov (responseProjection hS ν (M s₀)) φ (dirLoss S
        ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1)
            (fun _ ↦ one_pos) (one_integral_pos ν) hS (M s₀))).symm
          ⟨M', deriv_mem_dirSpan_of_path hV hM'⟩))) s₀ := by
  have hrel₀ := hrel.self_of_nhds
  have hF := hasFDerivAt_obsV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hφm hφ
    (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS (M s₀))
  rw [chartV_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel₀] at hF
  have hc := hF.comp_hasDerivAt s₀ (hasDerivAt_toV_path hV hM')
  refine (hc.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hrel] with s hs
    exact integral_responseProjection_eq hS ν hs φ
  · rw [obsV_deriv_apply measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hφm hφ, priorCov_eq_lawCov_familyMeasure hS ν,
      ← responseProjection_eq_familyMeasure_responseTheta hS ν hrel₀]

end Law

end Laplace.Multi
