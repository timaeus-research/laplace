/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LossCurvature
import Laplace.Multi.RayLength
import Laplace.Multi.JourneyPotential

/-!
# The Fisher metric in the joint response chart

In the natural coordinates `θ = (t, ta)` of the joint family `P_θ ∝ e^{−θ·S} π`, `S = (L₀, R)`,
the Fisher form is `G_θ(u, v) = Cov_θ(S_u, S_v)` (`natForm`). The slice chart `(t, M) ↦ θ`
(`sliceInv`) pulls it back to a **block-diagonal** form: with `b = C⁻¹c` the regression
coefficients, `H = L₀ − b·R` the residual and `C` the feature covariance at the chart point,

* the chart velocity of `(τ, v)` is `(τ, −τ b − C⁻¹ v)` (`sliceInv_deriv_jointPoint`), whose score
  is `τ H − (C⁻¹v)·R` (`dirLoss_jointStat_sliceInv_deriv`);
* `G((τ, v), (τ', v')) = τ τ' Var(H) + v'ᵀ C⁻¹ v` (`natForm_sliceInv_deriv`);
* in particular **temperature motion at fixed response and response motion at fixed temperature
  are Fisher-orthogonal** (`natForm_temp_response_orth`), the temperature speed is `√Var(H)`
  (`natForm_temp_temp`) and the response block is the inverse feature covariance
  (`natForm_response_response`).

This explains the Schur complement of the constrained responses geometrically and gives the length
integrand for arbitrary journeys in the chart. Along any `C¹` path `η` in natural coordinates, a
bounded observable moves at most `((hi − lo)/2)` times the Fisher length
(`abs_priorExp_sub_le_natLength`), so the Fisher length of any journey is at least
`2|Δ⟨φ⟩|/(hi − lo)` (`natLength_ge`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The Fisher form of the joint family in natural coordinates: `G_θ(u, v) = Cov_θ(S_u, S_v)`. -/
noncomputable def natForm (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ u v : Option ι → ℝ) :
    ℝ :=
  priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (dirLoss (jointStat L₀ R) u)
    (dirLoss (jointStat L₀ R) v) 1

/-- The Fisher length of a path in natural coordinates on `[0, 1]`. -/
noncomputable def natLength (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (η η' : ℝ → Option ι → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, Real.sqrt (natForm μ π L₀ R (η s) (η' s) (η' s))

omit [MeasurableSpace X] in
theorem dirLoss_jointStat_jointPoint (L₀ : X → ℝ) (R : ι → X → ℝ) (τ : ℝ) (ω : ι → ℝ) :
    dirLoss (jointStat L₀ R) (jointPoint τ ω) = fun x ↦ τ * L₀ x + dirLoss R ω x := by
  funext x
  simp [dirLoss, jointStat, jointPoint, Fintype.sum_option, Option.elim]

omit [MeasurableSpace X] in
theorem dirLoss_neg_mul_sub (R : ι → X → ℝ) (τ : ℝ) (b w : ι → ℝ) :
    dirLoss R (fun i ↦ -(τ * b i) - w i) = fun x ↦ -τ * dirLoss R b x - dirLoss R w x := by
  funext x
  simp only [dirLoss, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- The residual `H = L₀ − b·R` is uncorrelated with every feature direction when `C b = c`. -/
theorem priorCov_residual_dirLoss {t : ℝ} (a : ι → ℝ) {b : ι → ℝ}
    (hb : (featCov μ π L₀ R t a).mulVec b = featObsCov μ π L₀ R t a L₀) (u : ι → ℝ) :
    priorCov μ π (affLoss L₀ R a) (fun x ↦ L₀ x - dirLoss R b x) (dirLoss R u) t = 0 := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  have hH : Bdd fun x ↦ L₀ x - dirLoss R b x := Bdd.sub ⟨hL₀m, M₀, hL₀⟩ (bdd_dirLoss hR b)
  rw [priorCov_comm π _ _ (dirLoss R u) t, ← sum_mul_priorCov_eq hν hR hH u]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [priorCov_comm π _ (R i) _ t, priorCov_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR a ⟨hL₀m, M₀, hL₀⟩
    (bdd_dirLoss hR b) (hR i), priorCov_comm π _ (dirLoss R b) (R i) t,
    ← featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a b i, hb]
  simp only [featObsCov]
  rw [priorCov_comm π _ L₀ (R i) t, sub_self, mul_zero]

section Chart

variable (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  [Nonempty ι] [DecidableEq ι]
include hnd

/-- **The chart velocity**: `D sliceInv (τ, v) = (τ, −τ b − C⁻¹ v)`. -/
theorem sliceInv_deriv_jointPoint {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (τ : ℝ) (v : ι → ℝ) :
    (sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t)).symm
        (jointPoint τ v) =
      jointPoint τ (fun i ↦ -(τ * regCoeff μ π L₀ R M t i) -
        (featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M))⁻¹.mulVec v i) := by
  set a := Function.invFun (meanMap μ π L₀ R t) M with ha
  set b := regCoeff μ π L₀ R M t with hb
  set w := (featCov μ π L₀ R t a)⁻¹.mulVec v with hw
  have hθ : tempPath μ π L₀ R M t = natCoord t a :=
    tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hcoe : ∀ u, sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t) u =
      sliceMapDeriv μ π L₀ R (tempPath μ π L₀ R M t) u := fun u ↦ by
    rw [← coe_sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd]
    rfl
  have hZ : priorZ μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t)) 1 ≠ 0 :=
    (affZ_pos hπm hπi hπ hπpos measurable_const h0 hS' (t := 1) _).ne'
  have hCb : (featCov μ π L₀ R t a).mulVec b = featObsCov μ π L₀ R t a L₀ :=
    featCov_mulVec_regCoeff hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht M
  have hCw : (featCov μ π L₀ R t a).mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
      (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a)), Matrix.one_mulVec]
  rw [ContinuousLinearEquiv.symm_apply_eq]
  funext j
  cases j with
  | none => simp [hcoe]
  | some i =>
    rw [hcoe, sliceMapDeriv_some, meanMapDeriv_apply hπm hπi (fun x ↦ (hπ x).le) measurable_const
      h0 hS' one_pos hZ, hθ, priorCov_natCoord]
    simp only [dirLoss_jointStat_jointPoint, dirLoss_neg_mul_sub, jointPoint_some]
    have hRi : jointStat L₀ R (some i) = R i := rfl
    rw [hRi, priorCov_add_right_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a
      (Bdd.const_mul τ ⟨hL₀m, M₀, hL₀⟩) (Bdd.sub (Bdd.const_mul (-τ) (bdd_dirLoss hR b))
        (bdd_dirLoss hR w)) (hR i),
      priorCov_sub_right hπm hπi hπ hπpos hL₀m hL₀ hR a (Bdd.const_mul (-τ) (bdd_dirLoss hR b))
        (bdd_dirLoss hR w) (hR i),
      priorCov_const_mul_right', priorCov_const_mul_right',
      ← featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a b i,
      ← featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a w i, hCb, hCw]
    simp only [featObsCov]
    ring

/-- The score of the chart velocity `(τ, v)` is `τ H − (C⁻¹v)·R`. -/
theorem dirLoss_jointStat_sliceInv_deriv {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (τ : ℝ) (v : ι → ℝ) :
    dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
        (tempPath μ π L₀ R M t)).symm (jointPoint τ v)) =
      fun x ↦ τ * (L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x) -
        dirLoss R
          ((featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M))⁻¹.mulVec v) x := by
  rw [sliceInv_deriv_jointPoint hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]
  simp only [dirLoss_jointStat_jointPoint, dirLoss_neg_mul_sub]
  funext x
  ring

/-- **The Fisher metric in the joint chart is block diagonal**:
`G((τ, v), (τ', v')) = τ τ' Var(H) + v'ᵀ C⁻¹ v`. -/
theorem natForm_sliceInv_deriv {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (τ τ' : ℝ) (v v' : ι → ℝ) :
    natForm μ π L₀ R (tempPath μ π L₀ R M t)
        ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t)).symm
          (jointPoint τ v))
        ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t)).symm
          (jointPoint τ' v')) =
      τ * τ' * priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M))
          (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x)
          (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x) t +
        dotProduct v'
          ((featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M))⁻¹.mulVec v) := by
  set a := Function.invFun (meanMap μ π L₀ R t) M with ha
  set b := regCoeff μ π L₀ R M t with hb
  set w := (featCov μ π L₀ R t a)⁻¹.mulVec v with hw
  set w' := (featCov μ π L₀ R t a)⁻¹.mulVec v' with hw'
  have hθ : tempPath μ π L₀ R M t = natCoord t a :=
    tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
  have hCb : (featCov μ π L₀ R t a).mulVec b = featObsCov μ π L₀ R t a L₀ :=
    featCov_mulVec_regCoeff hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht M
  have hCw' : (featCov μ π L₀ R t a).mulVec w' = v' := by
    rw [hw', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
      (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a)), Matrix.one_mulVec]
  have hH : Bdd fun x ↦ L₀ x - dirLoss R b x := Bdd.sub ⟨hL₀m, M₀, hL₀⟩ (bdd_dirLoss hR b)
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  unfold natForm
  rw [dirLoss_jointStat_sliceInv_deriv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM,
    dirLoss_jointStat_sliceInv_deriv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM, hθ, priorCov_natCoord,
    priorCov_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR a (Bdd.const_mul τ hH) (bdd_dirLoss hR w)
      (Bdd.sub (Bdd.const_mul τ' hH) (bdd_dirLoss hR w')),
    priorCov_sub_right hπm hπi hπ hπpos hL₀m hL₀ hR a (Bdd.const_mul τ' hH) (bdd_dirLoss hR w')
      (Bdd.const_mul τ hH),
    priorCov_sub_right hπm hπi hπ hπpos hL₀m hL₀ hR a (Bdd.const_mul τ' hH) (bdd_dirLoss hR w')
      (bdd_dirLoss hR w),
    priorCov_const_mul_left, priorCov_const_mul_right', priorCov_const_mul_left,
    priorCov_const_mul_right']
  have horth1 := priorCov_residual_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR a hCb w'
  have horth2 :
      priorCov μ π (affLoss L₀ R a) (dirLoss R w) (fun x ↦ L₀ x - dirLoss R b x) t = 0 := by
    rw [priorCov_comm]
    exact priorCov_residual_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR a hCb w
  have hww : priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w') t = dotProduct v' w := by
    rw [← sum_mul_priorCov_eq hν hR (bdd_dirLoss hR w') w, dotProduct_comm]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a w' i, hCw']
  rw [horth1, horth2, hww]
  ring

omit [DecidableEq ι] in
/-- **Temperature and response motions are Fisher-orthogonal in the joint chart.** -/
theorem natForm_temp_response_orth {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (v : ι → ℝ) :
    natForm μ π L₀ R (tempPath μ π L₀ R M t)
        ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t)).symm
          (jointPoint 1 0))
        ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t)).symm
          (jointPoint 0 v)) = 0 := by
  classical
  rw [natForm_sliceInv_deriv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]
  simp

/-- **The temperature speed at fixed response is the residual variance**: `G(∂_t, ∂_t) = Var(H)`. -/
theorem natForm_temp_temp {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    natForm μ π L₀ R (tempPath μ π L₀ R M t)
        ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t)).symm
          (jointPoint 1 0))
        ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t)).symm
          (jointPoint 1 0)) =
      priorCov μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) M))
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x)
        (fun x ↦ L₀ x - dirLoss R (regCoeff μ π L₀ R M t) x) t := by
  rw [natForm_sliceInv_deriv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]
  simp

/-- **The response block of the metric is the inverse feature covariance**:
`G((0, v), (0, v')) = v'ᵀ C⁻¹ v`. -/
theorem natForm_response_response {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (v v' : ι → ℝ) :
    natForm μ π L₀ R (tempPath μ π L₀ R M t)
        ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t)).symm
          (jointPoint 0 v))
        ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd (tempPath μ π L₀ R M t)).symm
          (jointPoint 0 v')) =
      dotProduct v' ((featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M))⁻¹.mulVec v) := by
  rw [natForm_sliceInv_deriv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]
  simp

end Chart

section Path

/-- The velocity of a bounded observable along a path in natural coordinates:
`d/ds ⟨φ⟩_{η s} = −Cov_{η s}(φ, S_{η' s})`. -/
theorem hasDerivAt_priorExp_natPath {η : ℝ → Option ι → ℝ} {η' : Option ι → ℝ} {s : ℝ}
    (hη : HasDerivAt η η' s) {φ : X → ℝ} (hφ : Bdd φ) :
    HasDerivAt (fun s ↦ priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ 1)
      (-priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ
        (dirLoss (jointStat L₀ R) η') 1) s := by
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have h := (hasFDerivAt_obsMap hπm hπi hπ hπpos measurable_const h0 hS' hφm hφb one_pos
    (η s)).comp_hasDerivAt s hη
  refine h.congr_deriv ?_
  rw [obsMapDeriv_apply hπm hπi hπ hπpos measurable_const h0 hS' hφm hφb one_pos]
  ring

/-- Pointwise Cauchy–Schwarz for the joint family: `|Cov(φ, S_u)| ≤ √Var φ · √G(u, u)`. -/
theorem abs_priorCov_le_sqrt_natForm (θ u : Option ι → ℝ) {φ : X → ℝ} (hφ : Bdd φ) :
    |priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) φ (dirLoss (jointStat L₀ R) u) 1|
      ≤ Real.sqrt (priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) φ φ 1) *
        Real.sqrt (natForm μ π L₀ R θ u u) := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  obtain ⟨_, h⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const h0 hS' θ θ 1
  have := h.abs_tiltCov_le (f := φ) (g := dirLoss (jointStat L₀ R) u) hφ (bdd_dirLoss hS' u) 1 0
  rw [← priorCov_eq_tiltCov_zero, ← priorCov_eq_tiltCov_zero, ← priorCov_eq_tiltCov_zero] at this
  exact this

/-- **A bounded observable moves at most `(hi − lo)/2` times the Fisher length of any journey.** -/
theorem abs_priorExp_sub_le_natLength {η η' : ℝ → Option ι → ℝ} (hη : ∀ s, HasDerivAt η (η' s) s)
    (hη' : Continuous η') {φ : X → ℝ} (hφ : Bdd φ) {lo hi : ℝ} (hlo : ∀ x, lo ≤ φ x)
    (hhi : ∀ x, φ x ≤ hi) :
    |priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η 1)) φ 1 -
        priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η 0)) φ 1| ≤
      (hi - lo) / 2 * natLength μ π L₀ R η η' := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hηc : Continuous η := continuous_iff_continuousAt.2 fun s ↦ (hη s).continuousAt
  have hlh : lo ≤ hi := (hlo (Classical.arbitrary X)).trans (hhi _)
  have hr0 : 0 ≤ (hi - lo) / 2 := by linarith
  -- the velocity and its continuity
  have hD : ∀ s, HasDerivAt
      (fun s ↦ priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ 1)
      (-priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ
        (dirLoss (jointStat L₀ R) (η' s)) 1) s := fun s ↦
    hasDerivAt_priorExp_natPath hπm hπi hπ hπpos hL₀m hL₀ hR (hη s) hφ
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  have hcovc : Continuous (fun s ↦ -priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s))
      φ (dirLoss (jointStat L₀ R) (η' s)) 1) := by
    have hc := (continuous_obsMapDeriv hπm hπi hπ hπpos measurable_const h0 hS' hφm hφb
      one_pos).comp hηc |>.clm_apply hη'
    refine hc.congr fun s ↦ ?_
    simp only [Function.comp]
    rw [obsMapDeriv_apply hπm hπi hπ hπpos measurable_const h0 hS' hφm hφb one_pos]
    ring
  have hGc : Continuous (fun s ↦ natForm μ π L₀ R (η s) (η' s) (η' s)) :=
    continuous_natCov_path hπm hπi hπ hπpos hL₀m hL₀ hR hηc hη' hη'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hD s)
    (hcovc.intervalIntegrable 0 1)
  rw [← hftc, natLength, ← intervalIntegral.integral_const_mul]
  calc |∫ s in (0 : ℝ)..1, -priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ
          (dirLoss (jointStat L₀ R) (η' s)) 1|
      ≤ ∫ s in (0 : ℝ)..1, |-priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ
          (dirLoss (jointStat L₀ R) (η' s)) 1| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ _ := by
        refine intervalIntegral.integral_mono_on zero_le_one (hcovc.abs.intervalIntegrable 0 1)
          ((continuous_const.mul hGc.sqrt).intervalIntegrable 0 1) fun s _ ↦ ?_
        rw [abs_neg]
        refine (abs_priorCov_le_sqrt_natForm hπm hπi hπ hπpos hL₀m hL₀ hR (η s) (η' s)
          ⟨hφm, Mφ, hφb⟩).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        calc Real.sqrt (priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η s)) φ φ 1)
            ≤ Real.sqrt (((hi - lo) / 2) ^ 2) :=
              Real.sqrt_le_sqrt (priorCov_self_le_sq_of_bounds hπm hπi hπ hπpos measurable_const h0
                hS' (η s) ⟨hφm, Mφ, hφb⟩ hlo hhi)
          _ = (hi - lo) / 2 := Real.sqrt_sq hr0

/-- **The Fisher length of any journey is at least `2|Δ⟨φ⟩|/(hi − lo)`** for every observable
with values in `[lo, hi]`. -/
theorem natLength_ge {η η' : ℝ → Option ι → ℝ} (hη : ∀ s, HasDerivAt η (η' s) s)
    (hη' : Continuous η') {φ : X → ℝ} (hφ : Bdd φ) {lo hi : ℝ} (hlo : ∀ x, lo ≤ φ x)
    (hhi : ∀ x, φ x ≤ hi) (hlt : lo < hi) :
    2 * |priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η 1)) φ 1 -
        priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (η 0)) φ 1| / (hi - lo) ≤
      natLength μ π L₀ R η η' := by
  have h := abs_priorExp_sub_le_natLength hπm hπi hπ hπpos hL₀m hL₀ hR hη hη' hφ hlo hhi
  rw [div_le_iff₀ (sub_pos.2 hlt)]
  linarith

end Path

end

end Laplace.Multi
