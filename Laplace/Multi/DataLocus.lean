/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.DataReachability
import Laplace.Multi.RelativeEntropyGeometry
import Laplace.Multi.ThirdCumulant
import Laplace.Multi.EffectiveFeatures

/-!
# The data-to-posterior arrow on the reachable locus

Data enter the family through the mixture weights `w` of finitely many data distributions whose
losses are feature-affine: the coefficient of the mixture is the **linear** map
`dataCoeff a w = ∑ⱼ wⱼ aⱼ` (`dataCoeff`), and the posterior response is
`dataResponse w = m_t(dataCoeff a w)`. Along the data polytope:

* the response is differentiable with differential `D m_t ∘ dataCoeff`, i.e.
  `D(dataResponse)[h]ᵢ = −t Cov(Rᵢ, R_{Lh})` (`hasFDerivAt_dataResponse`,
  `dataResponse_deriv_apply`);
* the **invisible data directions** are exactly the kernel: `D(dataResponse)[h] = 0` iff `Lh` is
  an invisible feature direction (`dataResponse_deriv_eq_zero_iff`), and the response is constant
  along them (`dataResponse_add_of_invisible`); weights are identifiable only modulo
  `L⁻¹(N)`;
* the pulled-back Fisher metric is `t² Cov(R_{Lh}, R_{Lk})` (`dataMetric`), semidefinite with the
  same null directions (`dataMetric_self_eq_zero_iff`);
* the pulled-back loss `⟨L₀⟩_{t, Lw}` has gradient `−t Cov(L₀, R_{Lh})` (`hasFDerivAt_dataLoss`)
  and **exponential-coordinate Hessian** `t² κ₃(L₀, R_{Lh}, R_{Lk})`
  (`hasDerivAt_dataLossGrad_line`) — the data polytope lives in the exponential coordinates, so
  no residual appears here;
* the pulled-back relative entropy `𝒮(t, Lw)` has gradient `−t² Cov(L_w, R_{Lh})`, `L_w` the
  mixture loss (`hasDerivAt_dataEntropy_line`).

This is the programme's arrow: data → coefficients → canonical Gibbs distribution → loss,
entropy and information geometry, with the local laws of the seabed holding along the reachable
locus.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι] {J : Type*}
  [Fintype J]

/-- The coefficient map of finite mixtures, `w ↦ ∑ⱼ wⱼ aⱼ`, as a continuous linear map. -/
noncomputable def dataCoeff (a : J → ι → ℝ) : (J → ℝ) →L[ℝ] (ι → ℝ) :=
  ∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J ↦ ℝ) j).smulRight (a j)

omit [MeasurableSpace X] [Fintype ι] in
@[simp] theorem dataCoeff_apply (a : J → ι → ℝ) (w : J → ℝ) : dataCoeff a w = ∑ j, w j • a j := by
  simp [dataCoeff]

omit [MeasurableSpace X] [Fintype ι] in
theorem dataCoeff_mem_reachableCoeff (a : J → ι → ℝ) {w : J → ℝ} (hw : w ∈ stdSimplex ℝ J) :
    dataCoeff a w ∈ reachableCoeff a := by
  rw [dataCoeff_apply]
  exact mem_reachableCoeff_of_mem_stdSimplex a hw

/-- The posterior response of the mixture `w`. -/
noncomputable def dataResponse (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a : J → ι → ℝ) (w : J → ℝ) : ι → ℝ :=
  meanMap μ π L₀ R t (dataCoeff a w)

/-- The pulled-back Fisher metric on data directions: `t² Cov(R_{Lh}, R_{Lk})`. -/
noncomputable def dataMetric (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a : J → ι → ℝ) (w h k : J → ℝ) : ℝ :=
  responseForm μ π L₀ R (dataCoeff a w) t (dataCoeff a h) (dataCoeff a k)

/-- The pulled-back loss surface `⟨L₀⟩_{t, Lw}`. -/
noncomputable def dataLoss' (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a : J → ι → ℝ) (w : J → ℝ) : ℝ :=
  priorExp μ π (affLoss L₀ R (dataCoeff a w)) L₀ t

/-- The gradient of the pulled-back loss against a data direction: `−t Cov(L₀, R_{Lh})`. -/
noncomputable def dataLossGrad (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a : J → ι → ℝ) (w h : J → ℝ) : ℝ :=
  -t * priorCov μ π (affLoss L₀ R (dataCoeff a w)) L₀ (dirLoss R (dataCoeff a h)) t

/-- The pulled-back relative entropy `𝒮(t, Lw)`. -/
noncomputable def dataEntropy (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a : J → ι → ℝ) (w : J → ℝ) : ℝ :=
  relEntropy μ π L₀ R (natCoord t (dataCoeff a w))

omit [MeasurableSpace X] [Fintype ι] in
theorem hasDerivAt_natCoord_line (t : ℝ) (b v : ι → ℝ) :
    HasDerivAt (fun s : ℝ ↦ natCoord t (b + s • v)) (natTangent t b 0 v) 0 := by
  refine hasDerivAt_pi.2 fun j ↦ ?_
  cases j with
  | none =>
    simp only [natCoord, Option.elim, natTangent]
    exact hasDerivAt_const _ _
  | some i =>
    simp only [natCoord, Option.elim, natTangent, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (b i) |>.const_mul t
    refine h.congr_deriv ?_
    simp

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- **The response is differentiable along the data polytope**, with differential
`D m_t ∘ dataCoeff`. -/
theorem hasFDerivAt_dataResponse (a : J → ι → ℝ) (w : J → ℝ) :
    HasFDerivAt (dataResponse μ π L₀ R t a)
      ((meanMapDeriv μ π L₀ R t (dataCoeff a w)).comp (dataCoeff a)) w := by
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) (dataCoeff a w)).ne'
  exact (hasFDerivAt_meanMap hπm hπi (fun x ↦ (hπ x).le) hL₀m hL₀ hR ht hZ).comp w
    (dataCoeff a).hasFDerivAt

/-- `D(dataResponse)[h]ᵢ = −t Cov(Rᵢ, R_{Lh})`. -/
theorem dataResponse_deriv_apply (a : J → ι → ℝ) (w h : J → ℝ) (i : ι) :
    ((meanMapDeriv μ π L₀ R t (dataCoeff a w)).comp (dataCoeff a)) h i =
      -t * priorCov μ π (affLoss L₀ R (dataCoeff a w)) (R i) (dirLoss R (dataCoeff a h)) t := by
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) (dataCoeff a w)).ne'
  rw [ContinuousLinearMap.comp_apply]
  exact meanMapDeriv_apply hπm hπi (fun x ↦ (hπ x).le) hL₀m hL₀ hR ht hZ _ i

/-- **Invisible data directions**: the response differential vanishes on `h` iff `Lh` is an
invisible feature direction. -/
theorem dataResponse_deriv_eq_zero_iff (a : J → ι → ℝ) (w h : J → ℝ) :
    ((meanMapDeriv μ π L₀ R t (dataCoeff a w)).comp (dataCoeff a)) h = 0 ↔
      dataCoeff a h ∈ invisibleSubmodule μ R := by
  rw [← featCov_mulVec_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht (dataCoeff a w)]
  constructor
  · intro h0
    funext i
    have := congrFun h0 i
    rw [dataResponse_deriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR ht, Pi.zero_apply,
      ← featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR] at this
    have ht0 : -t ≠ 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left ht0
  · intro h0
    funext i
    rw [dataResponse_deriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR ht,
      ← featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR, h0]
    simp

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht in
/-- The response is constant along invisible data directions. -/
theorem dataResponse_add_of_invisible (a : J → ι → ℝ) (w : J → ℝ) {h : J → ℝ}
    (hh : dataCoeff a h ∈ invisibleSet μ R) :
    dataResponse μ π L₀ R t a (w + h) = dataResponse μ π L₀ R t a w := by
  unfold dataResponse
  rw [map_add]
  exact meanMap_add_of_invisible _ hh

/-- **The pulled-back metric is degenerate exactly in the invisible data directions.** -/
theorem dataMetric_self_eq_zero_iff (a : J → ι → ℝ) (w h : J → ℝ) :
    dataMetric μ π L₀ R t a w h h = 0 ↔ dataCoeff a h ∈ invisibleSet μ R :=
  responseForm_self_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht _ _

/-- **The pulled-back loss is differentiable**, with gradient `dataLossGrad`. -/
theorem hasFDerivAt_dataLoss (a : J → ι → ℝ) (w : J → ℝ) :
    HasFDerivAt (dataLoss' μ π L₀ R t a)
      ((obsMapDeriv μ π L₀ L₀ R t (dataCoeff a w)).comp (dataCoeff a)) w :=
  (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hL₀m hL₀ ht (dataCoeff a w)).comp w
    (dataCoeff a).hasFDerivAt

theorem dataLoss_deriv_apply (a : J → ι → ℝ) (w h : J → ℝ) :
    ((obsMapDeriv μ π L₀ L₀ R t (dataCoeff a w)).comp (dataCoeff a)) h =
      dataLossGrad μ π L₀ R t a w h := by
  rw [ContinuousLinearMap.comp_apply]
  exact obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hL₀m hL₀ ht _ _

/-- **The exponential-coordinate Hessian of the pulled-back loss**: along `w + s k`,
`d/ds dataLossGrad(w + s k)[h] = t² κ₃(L₀, R_{Lh}, R_{Lk})`. -/
theorem hasDerivAt_dataLossGrad_line (a : J → ι → ℝ) (w h k : J → ℝ) :
    HasDerivAt (fun s : ℝ ↦ dataLossGrad μ π L₀ R t a (w + s • k) h)
      (t ^ 2 * priorCum3 μ π (affLoss L₀ R (dataCoeff a w)) L₀ (dirLoss R (dataCoeff a h))
        (dirLoss R (dataCoeff a k)) t) 0 := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have e : (fun s : ℝ ↦ dataLossGrad μ π L₀ R t a (w + s • k) h) = fun s ↦
      -t * priorCov μ π (affLoss L₀ R (dataCoeff a w + s • dataCoeff a k)) L₀
        (dirLoss R (dataCoeff a h)) t := by
    funext s
    simp only [dataLossGrad, map_add, map_smul]
  rw [e]
  have h := (hasDerivAt_priorCov_line hπm hπi hπ hπpos hL₀m hL₀ hR ht (dataCoeff a w)
    (dataCoeff a k) 0 hL (bdd_dirLoss hR (dataCoeff a h))).const_mul (-t)
  rw [zero_smul, add_zero] at h
  exact h.congr_deriv (by ring)

omit ht in
/-- **The gradient of the pulled-back relative entropy**: along `w + s k`,
`d/ds 𝒮(t, L(w + s k)) = −t² Cov(L_w, R_{Lk})` with `L_w = L₀ + (Lw)·R` the mixture loss. -/
theorem hasDerivAt_dataEntropy_line (a : J → ι → ℝ) (w k : J → ℝ) :
    HasDerivAt (fun s : ℝ ↦ dataEntropy μ π L₀ R t a (w + s • k))
      (-(t ^ 2 * priorCov μ π (affLoss L₀ R (dataCoeff a w)) (affLoss L₀ R (dataCoeff a w))
        (dirLoss R (dataCoeff a k)) t)) 0 := by
  have e : (fun s : ℝ ↦ dataEntropy μ π L₀ R t a (w + s • k)) = fun s ↦
      relEntropy μ π L₀ R (natCoord t (dataCoeff a w + s • dataCoeff a k)) := by
    funext s
    simp only [dataEntropy, map_add, map_smul]
  rw [e]
  have h := hasDerivAt_relEntropy_path hπm hπi hπ hπpos hL₀m hL₀ hR
    (hasDerivAt_natCoord_line t (dataCoeff a w) (dataCoeff a k))
  rw [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  unfold natForm
  rw [priorCov_natCoord]
  have e1 : dirLoss (jointStat L₀ R) (natCoord t (dataCoeff a w)) =
      fun x ↦ t * affLoss L₀ R (dataCoeff a w) x :=
    funext fun x ↦ dirLoss_jointStat_natCoord L₀ R t _ x
  have e2 : dirLoss (jointStat L₀ R) (natTangent t (dataCoeff a w) 0 (dataCoeff a k)) =
      fun x ↦ t * dirLoss R (dataCoeff a k) x := by
    funext x
    rw [dirLoss_jointStat_natTangent]
    ring
  rw [e1, e2, priorCov_const_mul_left, priorCov_const_mul_right']
  ring

end

end Laplace.Multi
