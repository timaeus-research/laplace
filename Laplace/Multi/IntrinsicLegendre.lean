/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.IntrinsicChart
import Laplace.Multi.MeanMapChart

/-!
# The intrinsic chart is a strictly differentiable Legendre equivalence

`IntrinsicChart` shows that the mean map restricted to the direction subspace `𝕍 = dirSpan μ π S`
is a bijection onto the relative interior of the moment body. This file adds the differential
structure, in the coordinates of `𝕍` (Astra's intrinsic formulation):

* `chartV θ = m(θ) − m(0)` is the chart in `𝕍`-coordinates, `chartVInv` its global inverse;
* `chartDeriv θ₀ : 𝕍 →L[ℝ] 𝕍` is the covariance operator restricted to `𝕍`
  (`dotJ_chartDeriv`: `⟨e, Dm(θ₀) v⟩ = −Cov_{θ₀}(⟨e, S⟩, ⟨v, S⟩)`), which maps into `𝕍`
  (`meanMapDeriv_mem_dirSpan`) and is injective on `𝕍` (`meanMapDeriv_eq_zero_of_mem_dirSpan`)
  with no nondegeneracy hypothesis: an invisible direction in `𝕍` is zero;
* `hasStrictFDerivAt_chartV`: the chart is strictly differentiable with derivative `chartDeriv`;
* `hasStrictFDerivAt_chartVInv`: **the inverse chart is strictly differentiable with derivative the
  inverse covariance operator on `𝕍`** — the response-side susceptibility.

The membership `Dm(θ₀) v ∈ 𝕍` is proved through the dual annihilator: every functional vanishing on
`𝕍` is `dotJ e` for an invisible `e`, and the covariance of an a.e. constant vanishes.
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal

namespace Laplace.Multi

section Subtype

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A map into a submodule is strictly differentiable as soon as its composite with the inclusion
is, with the derivative read off from the ambient one. -/
theorem hasStrictFDerivAt_of_subtypeL_comp {V W : Submodule ℝ E} {f : V → W} {f' : V →L[ℝ] W}
    {x : V} (h : HasStrictFDerivAt (fun v ↦ (f v : E)) (W.subtypeL.comp f') x) :
    HasStrictFDerivAt f f' x := by
  rw [hasStrictFDerivAt_iff_isLittleO] at h ⊢
  rw [← isLittleO_norm_left] at h ⊢
  refine h.congr_left fun p ↦ ?_
  rw [Submodule.coe_norm, Submodule.coe_sub, Submodule.coe_sub]
  rfl

end Subtype

section Chart

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : Type*} [Fintype J] [Nonempty J]
variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hπm hπi hπ hπpos hS

/-- Every response of the family lies in the moment body. -/
theorem meanMap_mem_momentBody (θ : J → ℝ) :
    meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ ∈ momentBody μ π S :=
  intrinsicInterior_subset (by
    rw [← range_meanMap_eq_intrinsicInterior_momentBody hπm hπi hπ hπpos hS]
    exact ⟨θ, rfl⟩)

/-- Differences of responses lie in the direction subspace. -/
theorem meanMap_sub_mem_dirSpan (θ θ' : J → ℝ) :
    meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ' ∈ dirSpan μ π S := by
  have h := AffineSubspace.vsub_mem_direction
    (mem_affineSpan ℝ (meanMap_mem_momentBody hπm hπi hπ hπpos hS θ))
    (mem_affineSpan ℝ (meanMap_mem_momentBody hπm hπi hπ hπpos hS θ'))
  rwa [vsub_eq_sub] at h

omit [Nonempty J] in
/-- The Jacobian paired with a direction is minus a covariance:
`⟨e, Dm(θ₀) v⟩ = −Cov_{θ₀}(⟨e, S⟩, ⟨v, S⟩)`. -/
theorem dotJ_meanMapDeriv (θ₀ e v : J → ℝ) :
    dotJ e (meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ v) =
      -priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) (dirLoss S e) (dirLoss S v) 1 := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS θ₀ v 1
  have hZ : priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) 1 ≠ 0 := h.ν_pos.ne'
  simp only [dotJ]
  simp_rw [meanMapDeriv_apply hπm hπi (fun x ↦ (hπ x).le) measurable_const h0 hS one_pos hZ v]
  rw [← sum_mul_priorCov_eq h.ν_int hS (bdd_dirLoss hS v) e, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

omit hπm hπi hπ hπpos hS [Nonempty X] [Nonempty J] in
/-- The covariance with an a.e. constant vanishes. -/
theorem priorCov_eq_zero_of_ae_eq_const {L φ ψ : X → ℝ} {t c : ℝ} (hφ : ∀ᵐ x ∂μ, φ x = c) :
    priorCov μ π L φ ψ t = 0 := by
  have h1 : ∫ x, (φ x * ψ x) * Real.exp (-(t * L x)) * π x ∂μ =
      c * ∫ x, ψ x * Real.exp (-(t * L x)) * π x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hφ] with x hx
    rw [hx]
    ring
  have h2 : ∫ x, φ x * Real.exp (-(t * L x)) * π x ∂μ = c * priorZ μ π L t := by
    unfold priorZ
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hφ] with x hx
    rw [hx]
    ring
  simp only [priorCov, priorExp]
  rw [h1, h2]
  by_cases hZ : priorZ μ π L t = 0
  · simp [hZ]
  · field_simp
    ring

/-- A functional vanishing on the direction subspace is an invisible direction. -/
theorem mem_invisibleSet_of_dotJ_eq_zero_on_dirSpan (e : J → ℝ)
    (he : ∀ v ∈ dirSpan μ π S, dotJ e v = 0) : e ∈ invisibleSet μ S := by
  refine ⟨dotJ e (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0), ?_⟩
  filter_upwards [ae_statPoint_mem_essRange hπm hπ hS] with x hx
  have hx' := essRange_subset_momentBody S hx
  have hmem := meanMap_mem_momentBody hπm hπi hπ hπpos hS 0
  have hv := he _ (AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx') (mem_affineSpan ℝ hmem))
  rw [vsub_eq_sub, (isLinearMap_dotJ e).map_sub, sub_eq_zero] at hv
  exact hv

/-- **The Jacobian maps into the direction subspace.** -/
theorem meanMapDeriv_mem_dirSpan (θ₀ v : J → ℝ) :
    meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ v ∈ dirSpan μ π S := by
  classical
  refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (dirSpan μ π S) _).1
    fun φ hφ ↦ ?_
  obtain ⟨e, he⟩ : ∃ e : J → ℝ, ∀ w, φ w = dotJ e w := by
    refine ⟨fun j ↦ φ (Pi.single j 1), fun w ↦ ?_⟩
    have hw : w = ∑ j, w j • Pi.single j 1 := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotJ]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  rw [he]
  obtain ⟨c, hc⟩ := mem_invisibleSet_of_dotJ_eq_zero_on_dirSpan hπm hπi hπ hπpos hS e
    fun v hv ↦ by
      rw [← he]
      exact (Submodule.mem_dualAnnihilator φ).1 hφ v hv
  rw [dotJ_meanMapDeriv hπm hπi hπ hπpos hS θ₀ e v, priorCov_eq_zero_of_ae_eq_const hc, neg_zero]

omit [Nonempty J] in
/-- **The variance of a nonzero visible contrast is positive.** -/
theorem priorCov_dirLoss_self_pos (θ₀ : J → ℝ) {v : J → ℝ} (hv : v ∈ dirSpan μ π S) (hv0 : v ≠ 0) :
    0 < priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) (dirLoss S v) (dirLoss S v) 1 := by
  have hinv : v ∉ invisibleSet μ S := fun hin ↦
    hv0 (eq_zero_of_invisible_of_mem_dirSpan hπm hπ hS hin hv)
  have hnd : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss S v x = c := fun ⟨c, hc⟩ ↦
    hinv ⟨c, hc.mono fun x hx ↦ hx (hπ x).ne'⟩
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  obtain ⟨M, hT⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS θ₀ v 1
  have hpos := hT.mixCov_self_pos hnd 0
  have e0 : mixCov μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) (dirLoss S v) (dirLoss S v)
      (dirLoss S v) 1 0 =
      priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) (dirLoss S v) (dirLoss S v) 1 := by
    unfold mixCov
    rw [show pathLoss (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) (dirLoss S v) 0 =
        affLoss (fun _ ↦ (0 : ℝ)) S θ₀ from funext fun x ↦ by simp [pathLoss]]
  rwa [e0] at hpos

omit [Nonempty J] in
/-- **The Jacobian is injective on the direction subspace** (no nondegeneracy hypothesis). -/
theorem meanMapDeriv_eq_zero_of_mem_dirSpan {θ₀ v : J → ℝ} (hv : v ∈ dirSpan μ π S)
    (h : meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ v = 0) : v = 0 := by
  by_contra hv0
  have hpos := priorCov_dirLoss_self_pos hπm hπi hπ hπpos hS θ₀ hv hv0
  have := dotJ_meanMapDeriv hπm hπi hπ hπpos hS θ₀ v v
  rw [h] at this
  simp only [dotJ, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at this
  linarith

/-- **The intrinsic chart in the coordinates of the direction subspace**: `θ ↦ m(θ) − m(0)`. -/
noncomputable def chartV (θ : dirSpan μ π S) : dirSpan μ π S :=
  ⟨meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0,
    meanMap_sub_mem_dirSpan hπm hπi hπ hπpos hS θ 0⟩

theorem chartV_apply (θ : dirSpan μ π S) :
    (chartV hπm hπi hπ hπpos hS θ : J → ℝ) =
      meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 := rfl

/-- **The derivative of the chart**: the covariance operator restricted to the direction
subspace. -/
noncomputable def chartDeriv (θ₀ : dirSpan μ π S) : dirSpan μ π S →L[ℝ] dirSpan μ π S :=
  ((meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀).comp (dirSpan μ π S).subtypeL).codRestrict
    (dirSpan μ π S) fun v ↦ meanMapDeriv_mem_dirSpan hπm hπi hπ hπpos hS θ₀ v

theorem chartDeriv_apply (θ₀ v : dirSpan μ π S) :
    (chartDeriv hπm hπi hπ hπpos hS θ₀ v : J → ℝ) =
      meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀ v := rfl

/-- `⟨e, Dm(θ₀) v⟩ = −Cov_{θ₀}(⟨e, S⟩, ⟨v, S⟩)` for the restricted derivative. -/
theorem dotJ_chartDeriv (θ₀ : dirSpan μ π S) (e : J → ℝ) (v : dirSpan μ π S) :
    dotJ e (chartDeriv hπm hπi hπ hπpos hS θ₀ v) =
      -priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) S θ₀) (dirLoss S e) (dirLoss S v) 1 :=
  dotJ_meanMapDeriv hπm hπi hπ hπpos hS θ₀ e v

/-- **The restricted derivative is negative definite**: `⟨v, Dm(θ₀) v⟩ < 0` for `v ≠ 0` in `𝕍`. -/
theorem dotJ_chartDeriv_self_neg (θ₀ : dirSpan μ π S) {v : dirSpan μ π S} (hv : v ≠ 0) :
    dotJ (v : J → ℝ) (chartDeriv hπm hπi hπ hπpos hS θ₀ v : J → ℝ) < 0 := by
  rw [dotJ_chartDeriv, neg_lt_zero]
  exact priorCov_dirLoss_self_pos hπm hπi hπ hπpos hS θ₀ v.2 fun h ↦ hv (Subtype.ext h)

theorem chartDeriv_injective (θ₀ : dirSpan μ π S) :
    Function.Injective (chartDeriv hπm hπi hπ hπpos hS θ₀) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_
  exact Subtype.ext (meanMapDeriv_eq_zero_of_mem_dirSpan hπm hπi hπ hπpos hS v.2
    (congrArg Subtype.val hv))

/-- The restricted derivative as a continuous linear equivalence of `𝕍`. -/
noncomputable def chartDerivEquiv (θ₀ : dirSpan μ π S) : dirSpan μ π S ≃L[ℝ] dirSpan μ π S :=
  (LinearEquiv.ofInjectiveEndo
    (chartDeriv hπm hπi hπ hπpos hS θ₀ : dirSpan μ π S →ₗ[ℝ] dirSpan μ π S)
    (chartDeriv_injective hπm hπi hπ hπpos hS θ₀)).toContinuousLinearEquiv

theorem coe_chartDerivEquiv (θ₀ : dirSpan μ π S) :
    (chartDerivEquiv hπm hπi hπ hπpos hS θ₀ : dirSpan μ π S →L[ℝ] dirSpan μ π S) =
      chartDeriv hπm hπi hπ hπpos hS θ₀ := by
  ext v
  simp only [chartDerivEquiv, ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_ofInjectiveEndo,
    ContinuousLinearMap.coe_coe]

/-- **The chart is strictly differentiable with derivative the restricted covariance operator.** -/
theorem hasStrictFDerivAt_chartV (θ₀ : dirSpan μ π S) :
    HasStrictFDerivAt (chartV hπm hπi hπ hπpos hS) (chartDeriv hπm hπi hπ hπpos hS θ₀) θ₀ := by
  refine hasStrictFDerivAt_of_subtypeL_comp ?_
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have h := ((hasStrictFDerivAt_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS
    one_pos (θ₀ : J → ℝ)).comp θ₀ (dirSpan μ π S).subtypeL.hasStrictFDerivAt).sub_const
    (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0)
  rw [show (dirSpan μ π S).subtypeL.comp (chartDeriv hπm hπi hπ hπpos hS θ₀) =
      (meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) S 1 θ₀).comp (dirSpan μ π S).subtypeL from
    ContinuousLinearMap.ext fun v ↦ rfl]
  exact h

open Classical in
/-- **The inverse chart** in the coordinates of the direction subspace (zero off the image). -/
noncomputable def chartVInv (v : dirSpan μ π S) : dirSpan μ π S :=
  if h : meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + (v : J → ℝ) ∈
      intrinsicInterior ℝ (momentBody μ π S) then
    (intrinsicChart hπm hπi hπ hπpos hS).symm ⟨_, h⟩
  else 0

theorem chartVInv_chartV (θ : dirSpan μ π S) :
    chartVInv hπm hπi hπ hπpos hS (chartV hπm hπi hπ hπpos hS θ) = θ := by
  unfold chartVInv
  have hmem : meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + (chartV hπm hπi hπ hπpos hS θ : J → ℝ) ∈
      intrinsicInterior ℝ (momentBody μ π S) := by
    rw [chartV_apply, add_sub_cancel, ← range_meanMap_eq_intrinsicInterior_momentBody hπm hπi hπ
      hπpos hS]
    exact ⟨θ, rfl⟩
  rw [dif_pos hmem]
  apply (intrinsicChart hπm hπi hπ hπpos hS).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + (chartV hπm hπi hπ hπpos hS θ : J → ℝ) = _
  rw [intrinsicChart_apply, chartV_apply, add_sub_cancel]

theorem chartV_chartVInv {v : dirSpan μ π S}
    (hv : meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 + (v : J → ℝ) ∈
      intrinsicInterior ℝ (momentBody μ π S)) :
    chartV hπm hπi hπ hπpos hS (chartVInv hπm hπi hπ hπpos hS v) = v := by
  unfold chartVInv
  rw [dif_pos hv]
  apply Subtype.ext
  rw [chartV_apply, meanMap_intrinsicChart_symm]
  exact add_sub_cancel_left _ _

/-- **The inverse chart is strictly differentiable, with derivative the inverse covariance operator
on the direction subspace.** -/
theorem hasStrictFDerivAt_chartVInv (θ₀ : dirSpan μ π S) :
    HasStrictFDerivAt (chartVInv hπm hπi hπ hπpos hS)
      ((chartDerivEquiv hπm hπi hπ hπpos hS θ₀).symm : dirSpan μ π S →L[ℝ] dirSpan μ π S)
      (chartV hπm hπi hπ hπpos hS θ₀) := by
  have h : HasStrictFDerivAt (chartV hπm hπi hπ hπpos hS)
      (chartDerivEquiv hπm hπi hπ hπpos hS θ₀ : dirSpan μ π S →L[ℝ] dirSpan μ π S) θ₀ := by
    rw [coe_chartDerivEquiv]
    exact hasStrictFDerivAt_chartV hπm hπi hπ hπpos hS θ₀
  exact h.to_local_left_inverse
    (Eventually.of_forall fun θ ↦ chartVInv_chartV hπm hπi hπ hπpos hS θ)

/-- The derivative of the inverse chart at a response `M` of the relative interior, in the
coordinates `M − m(0)` of the direction subspace. -/
theorem hasStrictFDerivAt_chartVInv_response (M : intrinsicInterior ℝ (momentBody μ π S)) :
    HasStrictFDerivAt (chartVInv hπm hπi hπ hπpos hS)
      ((chartDerivEquiv hπm hπi hπ hπpos hS ((intrinsicChart hπm hπi hπ hπpos hS).symm M)).symm :
        dirSpan μ π S →L[ℝ] dirSpan μ π S)
      ⟨(M : J → ℝ) - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0, by
        rw [← meanMap_intrinsicChart_symm hπm hπi hπ hπpos hS M]
        exact meanMap_sub_mem_dirSpan hπm hπi hπ hπpos hS _ 0⟩ := by
  have h := hasStrictFDerivAt_chartVInv hπm hπi hπ hπpos hS
    ((intrinsicChart hπm hπi hπ hπpos hS).symm M)
  convert h using 1
  apply Subtype.ext
  change (M : J → ℝ) - meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 0 = _
  rw [chartV_apply, meanMap_intrinsicChart_symm]

end Chart

end Laplace.Multi
