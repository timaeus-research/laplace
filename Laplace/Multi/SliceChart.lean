/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MultiConstrainedResponse
import Laplace.Multi.TemperatureSlice
import Laplace.Multi.MeanMapChart
import Laplace.Multi.ObservableRegression

/-!
# The slice chart `(t, β) ↦ (t, ⟨R⟩)` and the temperature paths at fixed feature response

In the natural coordinates `θ = (t, β)` of the joint family `e^{−tL₀ − ⟨β,R⟩}π`, the map
`sliceMap θ = (θ_none, ⟨R⟩_θ)` is strictly differentiable with a block-triangular derivative
(`hasStrictFDerivAt_sliceMap`), injective on `{θ_none > 0}` (`sliceMap_injOn`, from the slice
bijection) and its derivative is injective under feature nondegeneracy alone
(`sliceMapDeriv_injective`); no joint nondegeneracy is needed. Its partial inverse `sliceInv` is
therefore strictly differentiable (`hasStrictFDerivAt_sliceInv`), and the *temperature path*
`tempPath M t = sliceInv (t, M)`, the point of the temperature-`t` slice with feature response `M`,
is differentiable in `t` (`hasDerivAt_tempPath`) with a velocity whose temperature component is `1`
(`tempPath_velocity_none`). The path is identified with the `a`-chart of the slice
(`tempPath_eq_natCoord`), so that `t ↦ obsMean φ t M` is the observable read along it
(`obsMean_eq_tempPath`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The point `(t, M)` of the joint response space. -/
def jointPoint (t : ℝ) (M : ι → ℝ) : Option ι → ℝ := fun j ↦ j.elim t M

omit [Fintype ι] in
@[simp] theorem jointPoint_none (t : ℝ) (M : ι → ℝ) : jointPoint t M none = t := rfl

omit [Fintype ι] in
@[simp] theorem jointPoint_some (t : ℝ) (M : ι → ℝ) (i : ι) : jointPoint t M (some i) = M i :=
  rfl

/-- The slice map `θ ↦ (θ_none, ⟨R⟩_θ)` in the natural coordinates of the joint family. -/
noncomputable def sliceMap (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ : Option ι → ℝ) :
    Option ι → ℝ :=
  fun j ↦ j.elim (θ none) fun i ↦ meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ (some i)

@[simp] theorem sliceMap_none (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ : Option ι → ℝ) :
    sliceMap μ π L₀ R θ none = θ none := rfl

@[simp] theorem sliceMap_some (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ : Option ι → ℝ) (i : ι) :
    sliceMap μ π L₀ R θ (some i) = meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ (some i) :=
  rfl

/-- The derivative of the slice map: identity in the temperature slot, the joint mean-map
Jacobian in the feature slots. -/
noncomputable def sliceMapDeriv (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (θ₀ : Option ι → ℝ) : (Option ι → ℝ) →L[ℝ] (Option ι → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ j.elim
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option ι ↦ ℝ) none) fun i ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option ι ↦ ℝ) (some i)).comp
      (meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ₀)

@[simp] theorem sliceMapDeriv_none (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ₀ u : Option ι → ℝ) :
    sliceMapDeriv μ π L₀ R θ₀ u none = u none := rfl

@[simp] theorem sliceMapDeriv_some (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ₀ u : Option ι → ℝ) (i : ι) :
    sliceMapDeriv μ π L₀ R θ₀ u (some i) =
      meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ₀ u (some i) := rfl

/-- The partial inverse of the slice map on positive temperatures. -/
noncomputable def sliceInv (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) :
    (Option ι → ℝ) → (Option ι → ℝ) :=
  Function.invFunOn (sliceMap μ π L₀ R) {θ : Option ι → ℝ | 0 < θ none}

/-- The temperature path at fixed feature response `M`: the point of the temperature-`t` slice
with feature response `M`. -/
noncomputable def tempPath (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (M : ι → ℝ) (t : ℝ) :
    Option ι → ℝ :=
  sliceInv μ π L₀ R (jointPoint t M)

omit [Fintype ι] in
theorem natCoord_of_pos (θ : Option ι → ℝ) (hθ : 0 < θ none) :
    natCoord (θ none) (fun i ↦ θ (some i) / θ none) = θ := by
  funext j
  cases j with
  | none => rfl
  | some i =>
    simp only [natCoord, Option.elim]
    field_simp

theorem sliceMap_natCoord (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) :
    sliceMap μ π L₀ R (natCoord t a) = jointPoint t (meanMap μ π L₀ R t a) := by
  funext j
  cases j with
  | none => rfl
  | some i => exact meanMap_natCoord_some π L₀ R t a i

set_option linter.unusedFintypeInType false in
theorem hasDerivAt_jointPoint [DecidableEq ι] (M : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t ↦ jointPoint t M) (Pi.single none 1) t := by
  have e : (fun t ↦ jointPoint t M) = fun t : ℝ ↦ jointPoint 0 M + t • Pi.single none 1 := by
    funext t j
    cases j with
    | none => simp
    | some i => simp
  rw [e]
  simpa using ((hasDerivAt_id t).smul_const (Pi.single none (1 : ℝ) : Option ι → ℝ)).const_add
    (jointPoint 0 M)

/-- The velocity decomposes as the temperature direction plus feature directions. -/
theorem velocity_decomp [DecidableEq ι] (u : Option ι → ℝ) (hu : u none = 1) :
    u = Pi.single none 1 + ∑ k, u (some k) • (Pi.single (some k) 1 : Option ι → ℝ) := by
  funext j
  cases j with
  | none => simp [hu, Finset.sum_apply]
  | some i => simp [Finset.sum_apply, Pi.single_apply]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- **Strict differentiability of the slice map.** -/
theorem hasStrictFDerivAt_sliceMap (θ₀ : Option ι → ℝ) :
    HasStrictFDerivAt (sliceMap μ π L₀ R) (sliceMapDeriv μ π L₀ R θ₀) θ₀ := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hm := hasStrictFDerivAt_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS'
    one_pos θ₀
  refine hasStrictFDerivAt_pi'.2 fun j ↦ ?_
  cases j with
  | none =>
    exact (hasStrictFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Option ι ↦ ℝ) none θ₀).congr_fderiv
      (by ext u; rfl)
  | some i =>
    exact ((hasStrictFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Option ι ↦ ℝ) (some i) _).comp θ₀
      hm).congr_fderiv (by ext u; rfl)

/-- **The derivative of the slice map is injective under feature nondegeneracy alone.** -/
theorem sliceMapDeriv_injective
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
    (θ₀ : Option ι → ℝ) : Function.Injective (sliceMapDeriv μ π L₀ R θ₀) := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  refine (injective_iff_map_eq_zero _).mpr fun u hu ↦ ?_
  have hnone : u none = 0 := by simpa using congrFun hu none
  have hsome : ∀ i, meanMapDeriv μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ₀ u (some i) = 0 :=
    fun i ↦ by simpa using congrFun hu (some i)
  have hu' : u = dataDir (fun i ↦ u (some i)) := by
    funext j
    cases j with
    | none => simpa [dataDir] using hnone
    | some i => rfl
  have hZ : priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ₀) 1 ≠ 0 :=
    (affZ_pos hπm hπi hπ hπpos measurable_const h0 hS' (t := 1) θ₀).ne'
  have hν : Integrable (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ₀) 1) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS' θ₀ θ₀
      1).choose_spec.ν_int
  have hcov : ∀ i, priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ₀)
      (jointStat L₀ R (some i)) (dirLoss (jointStat L₀ R) u) 1 = 0 := fun i ↦ by
    have := hsome i
    rw [meanMapDeriv_apply hπm hπi (fun x ↦ (hπ x).le) measurable_const h0 hS' one_pos hZ u
      (some i)] at this
    linarith
  have hvar : priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ₀)
      (dirLoss (jointStat L₀ R) u) (dirLoss (jointStat L₀ R) u) 1 = 0 := by
    rw [← sum_mul_priorCov_eq hν hS' (bdd_dirLoss hS' u) u, Fintype.sum_option, hnone, zero_mul,
      zero_add]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [hcov i, mul_zero]
  have hform : responseForm μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ₀ 1 u u = 0 := by
    unfold responseForm
    rw [hvar, mul_zero]
  obtain ⟨c, hc⟩ := (responseForm_self_eq_zero_iff hπm hπi hπ hπpos measurable_const h0 hS'
    one_pos θ₀ u).1 hform
  have hv : (fun i ↦ u (some i)) = 0 := by
    by_contra hne
    refine hnd _ hne ⟨c, hc.mono fun x hx _ ↦ ?_⟩
    rw [← dirLoss_jointStat_dataDir L₀ R, ← hu']
    exact hx
  funext j
  cases j with
  | none => exact hnone
  | some i => exact congrFun hv i

variable (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hnd

/-- The derivative of the slice map as a continuous linear equivalence. -/
noncomputable def sliceMapEquiv (θ₀ : Option ι → ℝ) : (Option ι → ℝ) ≃L[ℝ] (Option ι → ℝ) :=
  (LinearEquiv.ofInjectiveEndo (sliceMapDeriv μ π L₀ R θ₀ : (Option ι → ℝ) →ₗ[ℝ] (Option ι → ℝ))
    (sliceMapDeriv_injective hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀)).toContinuousLinearEquiv

theorem coe_sliceMapEquiv (θ₀ : Option ι → ℝ) :
    (sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀ : (Option ι → ℝ) →L[ℝ] (Option ι → ℝ)) =
      sliceMapDeriv μ π L₀ R θ₀ := by
  ext v
  simp only [sliceMapEquiv, ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_ofInjectiveEndo,
    ContinuousLinearMap.coe_coe]

theorem hasStrictFDerivAt_sliceMap_equiv (θ₀ : Option ι → ℝ) :
    HasStrictFDerivAt (sliceMap μ π L₀ R)
      (sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀ : (Option ι → ℝ) →L[ℝ] (Option ι → ℝ))
      θ₀ := by
  rw [coe_sliceMapEquiv]
  exact hasStrictFDerivAt_sliceMap hπm hπi hπ hπpos hL₀m hL₀ hR θ₀

/-- The slice map is injective on the half-space of positive temperatures. -/
theorem sliceMap_injOn : InjOn (sliceMap μ π L₀ R) {θ : Option ι → ℝ | 0 < θ none} := by
  intro θ hθ θ' hθ' h
  obtain ⟨t, a, rfl⟩ : ∃ t a, θ = natCoord t a := ⟨θ none, _, (natCoord_of_pos θ hθ).symm⟩
  obtain ⟨t', a', rfl⟩ : ∃ t a, θ' = natCoord t a := ⟨θ' none, _, (natCoord_of_pos θ' hθ').symm⟩
  have ht : 0 < t := hθ
  rw [sliceMap_natCoord, sliceMap_natCoord] at h
  have htt : t = t' := congrFun h none
  subst htt
  have hm : meanMap μ π L₀ R t a = meanMap μ π L₀ R t a' := funext fun i ↦ congrFun h (some i)
  rw [meanMap_injective hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd hm]

variable [Nonempty ι]

/-- Every `(t, M)` with `t > 0` and `M` in the interior of the moment body is attained. -/
theorem sliceMap_surj {t : ℝ} (ht : 0 < t) {M : ι → ℝ} (hM : M ∈ interior (momentBody μ π R)) :
    ∃ θ ∈ {θ : Option ι → ℝ | 0 < θ none}, sliceMap μ π L₀ R θ = jointPoint t M := by
  obtain ⟨a, _, ha⟩ := (bijOn_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd).surjOn hM
  refine ⟨natCoord t a, ht, ?_⟩
  rw [sliceMap_natCoord, ha]

omit [Nonempty ι] in
theorem sliceInv_sliceMap {θ : Option ι → ℝ} (hθ : 0 < θ none) :
    sliceInv μ π L₀ R (sliceMap μ π L₀ R θ) = θ :=
  (sliceMap_injOn hπm hπi hπ hπpos hL₀m hL₀ hR hnd).leftInvOn_invFunOn hθ

theorem sliceMap_sliceInv {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    sliceMap μ π L₀ R (sliceInv μ π L₀ R (jointPoint t M)) =
      jointPoint t M :=
  Function.invFunOn_eq (sliceMap_surj hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM)

theorem sliceInv_none_pos {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    0 < sliceInv μ π L₀ R (jointPoint t M) none :=
  Function.invFunOn_mem (sliceMap_surj hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM)

omit [Nonempty ι] in
/-- **Strict differentiability of the partial inverse** at every positive-temperature point. -/
theorem hasStrictFDerivAt_sliceInv {θ₀ : Option ι → ℝ} (hθ₀ : 0 < θ₀ none) :
    HasStrictFDerivAt (sliceInv μ π L₀ R)
      ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀).symm :
        (Option ι → ℝ) →L[ℝ] (Option ι → ℝ))
      (sliceMap μ π L₀ R θ₀) := by
  refine (hasStrictFDerivAt_sliceMap_equiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
    θ₀).to_local_left_inverse ?_
  have hopen : IsOpen {θ : Option ι → ℝ | 0 < θ none} :=
    isOpen_lt continuous_const (continuous_apply none)
  filter_upwards [hopen.mem_nhds hθ₀] with θ hθ
  exact sliceInv_sliceMap hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ

theorem tempPath_none {t : ℝ} (ht : 0 < t) {M : ι → ℝ} (hM : M ∈ interior (momentBody μ π R)) :
    tempPath μ π L₀ R M t none = t :=
  congrFun (sliceMap_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM) none

theorem tempPath_response {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (i : ι) :
    meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
      (tempPath μ π L₀ R M t) (some i) = M i :=
  congrFun (sliceMap_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM) (some i)

/-- **The temperature path is identified with the `a`-chart of the slice**:
`tempPath M t = Θ(t, m_t⁻¹(M))`. -/
theorem tempPath_eq_natCoord {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    tempPath μ π L₀ R M t =
      natCoord t (Function.invFun (meanMap μ π L₀ R t) M) := by
  have hMr : M ∈ Set.range (meanMap μ π L₀ R t) := by
    rwa [range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]
  have h1 : sliceMap μ π L₀ R (natCoord t (Function.invFun (meanMap μ π L₀ R t) M)) =
      jointPoint t M := by
    rw [sliceMap_natCoord, meanMap_invFun hMr]
  have h2 := sliceMap_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
  exact (sliceMap_injOn hπm hπi hπ hπpos hL₀m hL₀ hR hnd)
    (sliceInv_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM) ht (h2.trans h1.symm)

/-- `t ↦ ⟨φ⟩` at fixed feature response, read along the temperature path. -/
theorem obsMean_eq_tempPath {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (φ : X → ℝ) :
    obsMean μ π L₀ φ R t M =
      priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R)
        (tempPath μ π L₀ R M t)) φ 1 := by
  rw [tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM, priorExp_natCoord]
  rfl

section Path

variable [DecidableEq ι]

/-- **The temperature path is differentiable**, with velocity `(DF)⁻¹ e_t`. -/
theorem hasDerivAt_tempPath {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (tempPath μ π L₀ R M)
      ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
        (tempPath μ π L₀ R M t)).symm (Pi.single none 1)) t := by
  have h := hasStrictFDerivAt_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
    (sliceInv_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM)
  rw [sliceMap_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM] at h
  exact h.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_jointPoint M t)

omit [Nonempty ι] in
/-- The temperature component of the velocity is `1`. -/
theorem tempPath_velocity_none (θ₀ : Option ι → ℝ) :
    (sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀).symm (Pi.single none 1) none = 1 := by
  set u := (sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀).symm (Pi.single none 1) with hu
  have h : sliceMapDeriv μ π L₀ R θ₀ u = Pi.single none 1 := by
    rw [← coe_sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀, hu]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have := congrFun h none
  simpa using this

end Path

end

end Laplace.Multi
