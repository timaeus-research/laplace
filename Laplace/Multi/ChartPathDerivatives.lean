/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.JointChartMetric

/-!
# Regression data along paths in the joint chart

For a point `θ` of the joint family (natural coordinates, `θ none > 0`) let `C_θ = Cov_θ(R, R)`
(`natC`), `c_θ = Cov_θ(R, L₀)` (`natc`), `b_θ = C_θ⁻¹ c_θ` (`natb`) and `H_θ = L₀ − b_θ·R` (`natH`),
the residual of `L₀` on the features. Along any differentiable path `θ(s)` with velocity `θ'`
(score `S_{θ'}`):

* covariances move by the third cumulant, `d/ds Cov_{θ s}(φ, ψ) = −κ₃(φ, ψ, S_{θ'})`
  (`hasDerivAt_natCov_path`);
* the regression coefficients are differentiable, with
  `d/ds b = −C⁻¹ κ₃(R, H, S_{θ'})` (`hasDerivAt_natb_path`), obtained by differentiating the normal
  equations `C b = c` — no derivative of a matrix inverse is computed, only its existence is used;
* the residual variance moves by the residual cumulant, `d/ds Var(H) = −κ₃(H, H, S_{θ'})`
  (`hasDerivAt_natVarH_path`).

These are the ingredients of the unified loss Hessian in `LossHessian`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The data coefficients of a natural-coordinate point: `a_i = θ_i / θ_none`. -/
noncomputable def aOf (θ : Option ι → ℝ) : ι → ℝ := fun i ↦ θ (some i) / θ none

omit [MeasurableSpace X] [Fintype ι] in
theorem natCoord_aOf {θ : Option ι → ℝ} (hθ : 0 < θ none) : natCoord (θ none) (aOf θ) = θ :=
  natCoord_of_pos θ hθ

/-- The feature covariance at a natural-coordinate point. -/
noncomputable def natC (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ : Option ι → ℝ) :
    Matrix ι ι ℝ :=
  Matrix.of fun k l ↦ priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R k) (R l) 1

/-- The feature–loss covariance at a natural-coordinate point. -/
noncomputable def natc (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ : Option ι → ℝ) :
    ι → ℝ :=
  fun k ↦ priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R k) L₀ 1

/-- The regression coefficients `b_θ = C_θ⁻¹ c_θ`. -/
noncomputable def natb [DecidableEq ι] (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (θ : Option ι → ℝ) : ι → ℝ :=
  (natC μ π L₀ R θ)⁻¹.mulVec (natc μ π L₀ R θ)

/-- The residual `H_θ = L₀ − b_θ·R`. -/
noncomputable def natH [DecidableEq ι] (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (θ : Option ι → ℝ) : X → ℝ :=
  fun x ↦ L₀ x - dirLoss R (natb μ π L₀ R θ) x

theorem natC_eq_featCov (π L₀ : X → ℝ) (R : ι → X → ℝ) {θ : Option ι → ℝ} (hθ : 0 < θ none) :
    natC μ π L₀ R θ = featCov μ π L₀ R (θ none) (aOf θ) := by
  ext k l
  simp only [natC, featCov, Matrix.of_apply]
  conv_lhs => rw [← natCoord_aOf hθ]
  rw [priorCov_natCoord]

theorem natc_eq_featObsCov (π L₀ : X → ℝ) (R : ι → X → ℝ) {θ : Option ι → ℝ} (hθ : 0 < θ none) :
    natc μ π L₀ R θ = featObsCov μ π L₀ R (θ none) (aOf θ) L₀ := by
  funext k
  simp only [natc, featObsCov]
  conv_lhs => rw [← natCoord_aOf hθ]
  rw [priorCov_natCoord]

theorem natCov_eq (π L₀ : X → ℝ) (R : ι → X → ℝ) {θ : Option ι → ℝ} (hθ : 0 < θ none)
    (φ ψ : X → ℝ) :
    priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) φ ψ 1 =
      priorCov μ π (affLoss L₀ R (aOf θ)) φ ψ (θ none) := by
  conv_lhs => rw [← natCoord_aOf hθ]
  rw [priorCov_natCoord]

theorem natCum3_eq (π L₀ : X → ℝ) (R : ι → X → ℝ) {θ : Option ι → ℝ} (hθ : 0 < θ none)
    (φ ψ χ : X → ℝ) :
    priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) φ ψ χ 1 =
      priorCum3 μ π (affLoss L₀ R (aOf θ)) φ ψ χ (θ none) := by
  conv_lhs => rw [← natCoord_aOf hθ]
  rw [priorCum3_natCoord]

theorem natC_symm (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ : Option ι → ℝ) (i j : ι) :
    natC μ π L₀ R θ i j = natC μ π L₀ R θ j i := by
  simp only [natC, Matrix.of_apply]
  exact priorCov_comm π _ (R i) (R j) 1

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR hnd

theorem isUnit_natC [DecidableEq ι] {θ : Option ι → ℝ} (hθ : 0 < θ none) :
    IsUnit (natC μ π L₀ R θ) := by
  rw [natC_eq_featCov π L₀ R hθ]
  exact isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ _

/-- The normal equations `C_θ b_θ = c_θ`. -/
theorem natC_mulVec_natb [DecidableEq ι] {θ : Option ι → ℝ} (hθ : 0 < θ none) :
    (natC μ π L₀ R θ).mulVec (natb μ π L₀ R θ) = natc μ π L₀ R θ := by
  unfold natb
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_natC hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ)), Matrix.one_mulVec]

omit [Nonempty X] hnd in
/-- Bilinearity transport: `C_θ *ᵥ u` is the covariance with `R_u`. -/
theorem natC_mulVec_apply {θ : Option ι → ℝ} (hθ : 0 < θ none) (u : ι → ℝ) (i : ι) :
    (natC μ π L₀ R θ).mulVec u i =
      priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R i) (dirLoss R u) 1 := by
  rw [natC_eq_featCov π L₀ R hθ, natCov_eq π L₀ R hθ]
  exact featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR _ u i

/-- The residual is uncorrelated with every feature direction. -/
theorem natCov_natH_dirLoss [DecidableEq ι] {θ : Option ι → ℝ} (hθ : 0 < θ none) (u : ι → ℝ) :
    priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (natH μ π L₀ R θ) (dirLoss R u) 1
      = 0 := by
  have hb := natC_mulVec_natb hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ
  rw [natC_eq_featCov π L₀ R hθ, natc_eq_featObsCov π L₀ R hθ] at hb
  rw [natCov_eq π L₀ R hθ]
  exact priorCov_residual_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR _ hb u

/-- `Var(H_θ) = Var(L₀) − c_θ · b_θ`. -/
theorem natCov_natH_self [DecidableEq ι] {θ : Option ι → ℝ} (hθ : 0 < θ none) :
    priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (natH μ π L₀ R θ)
        (natH μ π L₀ R θ) 1 =
      priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) L₀ L₀ 1 -
        dotProduct (natc μ π L₀ R θ) (natb μ π L₀ R θ) := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  set b := natb μ π L₀ R θ with hb
  have hH : Bdd (fun x ↦ L₀ x - dirLoss R b x) := hL.sub (bdd_dirLoss hR _)
  have h1 : priorCov μ π (affLoss L₀ R (aOf θ)) (fun x ↦ L₀ x - dirLoss R b x) (dirLoss R b)
      (θ none) = 0 := by
    have := natCov_natH_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ b
    rwa [natCov_eq π L₀ R hθ] at this
  have hν : Integrable (baseWeight π (affLoss L₀ R (aOf θ)) (θ none)) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR (aOf θ) (aOf θ)
      (θ none)).choose_spec.ν_int
  change priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ)
    (fun x ↦ L₀ x - dirLoss R b x) (fun x ↦ L₀ x - dirLoss R b x) 1 = _
  rw [natCov_eq π L₀ R hθ, natCov_eq π L₀ R hθ,
    priorCov_sub_right hπm hπi hπ hπpos hL₀m hL₀ hR (aOf θ) hL (bdd_dirLoss hR _) hH, h1,
    sub_zero, priorCov_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR (aOf θ) hL (bdd_dirLoss hR _) hL,
    ← sum_mul_priorCov_eq hν hR hL, dotProduct_comm]
  simp only [dotProduct, natc]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [natCov_eq π L₀ R hθ]

omit hnd in
/-- Trilinearity transport: `κ₃(R_k, H_θ, χ) = κ₃(R_k, L₀, χ) − ∑ⱼ bⱼ κ₃(R_k, Rⱼ, χ)`. -/
theorem natCum3_natH_slot [DecidableEq ι] {θ : Option ι → ℝ} (hθ : 0 < θ none) {χ : X → ℝ}
    (hχ : Bdd χ) (k : ι) :
    priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R k) (natH μ π L₀ R θ) χ 1 =
      priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R k) L₀ χ 1 -
        ∑ j, natb μ π L₀ R θ j *
          priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R k) (R j) χ 1 := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  simp only [natCum3_eq π L₀ R hθ]
  have e : natH μ π L₀ R θ = fun x ↦ L₀ x - dirLoss R (natb μ π L₀ R θ) x := rfl
  rw [e, priorCum3_swap₁₂, priorCum3_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR _ hL (bdd_dirLoss hR _)
    (hR k) hχ, priorCum3_dirLoss_left hπm hπi hπ hπpos hL₀m hL₀ hR _ _ (hR k) hχ,
    priorCum3_swap₁₂ π _ L₀ (R k)]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by rw [priorCum3_swap₁₂ π _ (R j) (R k)]

section Path

variable {θ : ℝ → Option ι → ℝ} {θ' : Option ι → ℝ} {s₀ : ℝ} (hθ : HasDerivAt θ θ' s₀)
include hθ

omit hnd in
/-- **Covariances move by the third cumulant along any path**:
`d/ds Cov_{θ s}(φ, ψ) = −κ₃(φ, ψ, S_{θ'})`. -/
theorem hasDerivAt_natCov_path {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ) :
    HasDerivAt (fun s ↦ priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s)) φ ψ 1)
      (-priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) φ ψ
        (dirLoss (jointStat L₀ R) θ') 1) s₀ := by
  have h := hasDerivAt_cov_of_hasDerivAt_exp (μ := μ) (π := π)
    (L := fun s ↦ affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s)) (τ := fun _ ↦ 1) (c := 1)
    (D := dirLoss (jointStat L₀ R) θ') (s₀ := s₀)
    (fun f hf ↦ (hasDerivAt_priorExp_natPath hπm hπi hπ hπpos hL₀m hL₀ hR hθ hf).congr_deriv
      (by ring)) hφ hψ
  exact h.congr_deriv (by ring)

omit hnd in
theorem hasDerivAt_natC_path (i j : ι) :
    HasDerivAt (fun s ↦ natC μ π L₀ R (θ s) i j)
      (-priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R i) (R j)
        (dirLoss (jointStat L₀ R) θ') 1) s₀ :=
  hasDerivAt_natCov_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ (hR i) (hR j)

omit hnd in
theorem hasDerivAt_natc_path (i : ι) :
    HasDerivAt (fun s ↦ natc μ π L₀ R (θ s) i)
      (-priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R i) L₀
        (dirLoss (jointStat L₀ R) θ') 1) s₀ :=
  hasDerivAt_natCov_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ (hR i) ⟨hL₀m, M₀, hL₀⟩

/-- The regression coefficients are differentiable along the path (existence only, via the
differentiability of the matrix inverse at a unit). -/
theorem differentiableAt_natb_path [DecidableEq ι] (hpos : 0 < θ s₀ none) (i : ι) :
    DifferentiableAt ℝ (fun s ↦ natb μ π L₀ R (θ s) i) s₀ := by
  open scoped Matrix.Norms.Operator in
  have hC : DifferentiableAt ℝ (fun s ↦ natC μ π L₀ R (θ s)) s₀ := by
    have : DifferentiableAt ℝ (fun s ↦ fun i j ↦ natC μ π L₀ R (θ s) i j) s₀ :=
      differentiableAt_pi.2 fun i ↦ differentiableAt_pi.2 fun j ↦
        (hasDerivAt_natC_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ i j).differentiableAt
    exact this
  have hinv : DifferentiableAt ℝ (fun s ↦ Ring.inverse (natC μ π L₀ R (θ s))) s₀ :=
    hC.inverse (isUnit_natC hπm hπi hπ hπpos hL₀m hL₀ hR hnd hpos)
  have hentry : ∀ i j, DifferentiableAt ℝ (fun s ↦ (natC μ π L₀ R (θ s))⁻¹ i j) s₀ := by
    intro i j
    have h1 : DifferentiableAt ℝ (fun A : Matrix ι ι ℝ ↦ A i j)
        (Ring.inverse (natC μ π L₀ R (θ s₀))) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ι → ℝ) i)).differentiableAt
    refine (h1.comp s₀ hinv).congr_of_eventuallyEq ?_
    filter_upwards with s
    have e : (natC μ π L₀ R (θ s))⁻¹ = Ring.inverse (natC μ π L₀ R (θ s)) :=
      Matrix.nonsing_inv_eq_ringInverse _
    simp only [Function.comp, e]
  unfold natb
  simp only [Matrix.mulVec, dotProduct]
  exact DifferentiableAt.fun_sum fun j _ ↦ (hentry i j).mul
    (hasDerivAt_natc_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ j).differentiableAt

/-- **The regression coefficients move by the residual cumulant**:
`d/ds b_{θ s} = −C⁻¹ κ₃(R, H, S_{θ'})`. -/
theorem hasDerivAt_natb_path [DecidableEq ι] (hpos : ∀ s, 0 < θ s none) (i : ι) :
    HasDerivAt (fun s ↦ natb μ π L₀ R (θ s) i)
      (-(natC μ π L₀ R (θ s₀))⁻¹.mulVec (fun k ↦ priorCum3 μ π
        (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R k) (natH μ π L₀ R (θ s₀))
        (dirLoss (jointStat L₀ R) θ') 1) i) s₀ := by
  set b' : ι → ℝ := fun j ↦ deriv (fun s ↦ natb μ π L₀ R (θ s) j) s₀ with hb'
  have hb : ∀ j, HasDerivAt (fun s ↦ natb μ π L₀ R (θ s) j) (b' j) s₀ := fun j ↦
    (differentiableAt_natb_path hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ (hpos s₀) j).hasDerivAt
  -- differentiate the normal equations
  have hid : ∀ s k, ∑ j, natC μ π L₀ R (θ s) k j * natb μ π L₀ R (θ s) j =
      natc μ π L₀ R (θ s) k := fun s k ↦
    congrFun (natC_mulVec_natb hπm hπi hπ hπpos hL₀m hL₀ hR hnd (hpos s)) k
  have hkey : ∀ k, ∑ j, (-priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀))
      (R k) (R j) (dirLoss (jointStat L₀ R) θ') 1 * natb μ π L₀ R (θ s₀) j +
        natC μ π L₀ R (θ s₀) k j * b' j) =
      -priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R k) L₀
        (dirLoss (jointStat L₀ R) θ') 1 := by
    intro k
    have hlhs : HasDerivAt (fun s ↦ ∑ j, natC μ π L₀ R (θ s) k j * natb μ π L₀ R (θ s) j)
        (∑ j, (-priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀))
          (R k) (R j) (dirLoss (jointStat L₀ R) θ') 1 * natb μ π L₀ R (θ s₀) j +
            natC μ π L₀ R (θ s₀) k j * b' j)) s₀ :=
      HasDerivAt.fun_sum fun j _ ↦
        (hasDerivAt_natC_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ k j).mul (hb j)
    have hrhs := hasDerivAt_natc_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ k
    have hfun : (fun s ↦ ∑ j, natC μ π L₀ R (θ s) k j * natb μ π L₀ R (θ s) j) =
        fun s ↦ natc μ π L₀ R (θ s) k := funext fun s ↦ hid s k
    rw [hfun] at hlhs
    exact hlhs.unique hrhs
  -- solve for `b'`
  have hCb' : (natC μ π L₀ R (θ s₀)).mulVec b' = fun k ↦ -priorCum3 μ π
      (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R k) (natH μ π L₀ R (θ s₀))
      (dirLoss (jointStat L₀ R) θ') 1 := by
    funext k
    have h := hkey k
    rw [Finset.sum_add_distrib] at h
    rw [natCum3_natH_slot hπm hπi hπ hπpos hL₀m hL₀ hR (hpos s₀) (bdd_dirLoss
      (bdd_jointStat hL₀m hL₀ hR) θ') k]
    simp only [Matrix.mulVec, dotProduct]
    have e : ∑ j, -priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R k) (R j)
        (dirLoss (jointStat L₀ R) θ') 1 * natb μ π L₀ R (θ s₀) j =
        -∑ j, natb μ π L₀ R (θ s₀) j * priorCum3 μ π
          (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R k) (R j)
          (dirLoss (jointStat L₀ R) θ') 1 := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e] at h
    linarith
  have hunit := (Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_natC hπm hπi hπ hπpos hL₀m hL₀ hR hnd (hpos s₀))
  have hb'eq : b' = -(natC μ π L₀ R (θ s₀))⁻¹.mulVec (fun k ↦ priorCum3 μ π
      (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R k) (natH μ π L₀ R (θ s₀))
      (dirLoss (jointStat L₀ R) θ') 1) := by
    have : (natC μ π L₀ R (θ s₀))⁻¹.mulVec ((natC μ π L₀ R (θ s₀)).mulVec b') = b' := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
    rw [← this, hCb', ← Matrix.mulVec_neg]
    congr 1
  have := hb i
  rw [hb'eq] at this
  exact this

/-- **The residual variance moves by the residual cumulant**:
`d/ds Var_{θ s}(H_{θ s}) = −κ₃(H, H, S_{θ'})`. -/
theorem hasDerivAt_natVarH_path [DecidableEq ι] (hpos : ∀ s, 0 < θ s none) :
    HasDerivAt (fun s ↦ priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s))
        (natH μ π L₀ R (θ s)) (natH μ π L₀ R (θ s)) 1)
      (-priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (natH μ π L₀ R (θ s₀))
        (natH μ π L₀ R (θ s₀)) (dirLoss (jointStat L₀ R) θ') 1) s₀ := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hSθ : Bdd (dirLoss (jointStat L₀ R) θ') := bdd_dirLoss (bdd_jointStat hL₀m hL₀ hR) θ'
  have hfun : (fun s ↦ priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s))
      (natH μ π L₀ R (θ s)) (natH μ π L₀ R (θ s)) 1) = fun s ↦
      priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s)) L₀ L₀ 1 -
        dotProduct (natc μ π L₀ R (θ s)) (natb μ π L₀ R (θ s)) :=
    funext fun s ↦ natCov_natH_self hπm hπi hπ hπpos hL₀m hL₀ hR hnd (hpos s)
  have hbcont : ContinuousAt (fun s ↦ natb μ π L₀ R (θ s)) s₀ :=
    continuousAt_pi.2 fun i ↦ (differentiableAt_natb_path hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ
      (hpos s₀) i).continuousAt
  have hform := hasDerivAt_residual_form
    (v := fun s ↦ priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s)) L₀ L₀ 1)
    (c := fun s ↦ natc μ π L₀ R (θ s)) (C := fun s ↦ natC μ π L₀ R (θ s))
    (b := fun s ↦ natb μ π L₀ R (θ s))
    (c' := fun i ↦ -priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R i) L₀
      (dirLoss (jointStat L₀ R) θ') 1)
    (C' := Matrix.of fun i j ↦ -priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀))
      (R i) (R j) (dirLoss (jointStat L₀ R) θ') 1)
    (hasDerivAt_natCov_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ hL hL)
    (fun i ↦ hasDerivAt_natc_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ i)
    (fun i j ↦ hasDerivAt_natC_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ i j)
    hbcont (fun s i j ↦ natC_symm π L₀ R (θ s) i j)
    (fun s ↦ natC_mulVec_natb hπm hπi hπ hπpos hL₀m hL₀ hR hnd (hpos s))
  rw [hfun]
  refine hform.congr_deriv ?_
  have e : natH μ π L₀ R (θ s₀) = fun x ↦ L₀ x - dirLoss R (natb μ π L₀ R (θ s₀)) x := rfl
  conv_rhs => rw [e, natCum3_eq π L₀ R (hpos s₀),
    priorCum3_residual_expand hπm hπi hπ hπpos hL₀m hL₀ hR _ _ hSθ]
  simp only [← natCum3_eq π L₀ R (hpos s₀)]
  have e1 : dotProduct (natb μ π L₀ R (θ s₀)) (fun i ↦ -priorCum3 μ π
      (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R i) L₀
      (dirLoss (jointStat L₀ R) θ') 1) =
      -∑ i, natb μ π L₀ R (θ s₀) i * priorCum3 μ π
        (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R i) L₀
        (dirLoss (jointStat L₀ R) θ') 1 := by
    simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
  have e2 : dotProduct (natb μ π L₀ R (θ s₀)) ((Matrix.of fun i j ↦ -priorCum3 μ π
      (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R i) (R j)
      (dirLoss (jointStat L₀ R) θ') 1).mulVec (natb μ π L₀ R (θ s₀))) =
      -∑ i, natb μ π L₀ R (θ s₀) i * ∑ j, natb μ π L₀ R (θ s₀) j * priorCum3 μ π
        (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s₀)) (R i) (R j)
        (dirLoss (jointStat L₀ R) θ') 1 := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib,
      mul_neg]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [e1, e2]
  ring

end Path

end

end Laplace.Multi
