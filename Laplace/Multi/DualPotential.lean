/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MeanMapEmbedding
import Laplace.Multi.EntropyDuality
import Laplace.Multi.MomentPolytope

/-!
# The dual potential: the response geometry in mean coordinates

For the affine family `L_a = L₀ + ∑ aᵢRᵢ` at temperature `t` with nondegenerate contrasts, the mean
map `m` is an open embedding (`MeanMapEmbedding`) with global inverse `θ = m⁻¹` on the response
space. The **dual potential** is

  `I(y) = −t ⟨θ(y), y⟩ − A(θ(y))`,   `A = log Z_t`,

the Legendre transform of the free energy written in the response coordinate. This module proves:

* `hasFDerivAt_affLogZ`: `DA(a) = −t ⟨·, m(a)⟩` (the Fréchet form of `hasDerivAt_affLogZ_dir`);
* `mixKL_eq_bregman_dual`: `KL(P_b ‖ P_a) = I(m(b)) − I(m(a)) + t ⟨a, m(b) − m(a)⟩`, the Bregman
  divergence of `I` in mean coordinates (with `∇I(m(a)) = −t a`);
* `hasFDerivAt_dualPotential`: `DI(m(a)) = −t ⟨a, ·⟩` — the gradient of the dual potential is minus
  `t` times the data coordinate;
* `hasFDerivAt_dualGradient`, `dualHessian_apply_cov`: the Hessian of `I` at `m(a)` is
  `−t (Dm(a))⁻¹`, the inverse of the covariance matrix `Cov_a(Rᵢ, Rⱼ)`;
* `dualHessian_quadratic_form`: `⟨ṁ, D²I ṁ⟩ = G_a(v, v)` for `ṁ = Dm(a) v`: the response form is the
  Hessian of the dual potential evaluated on response velocities, so the response length of any
  data path is the `√(D²I)`-length of its image in mean coordinates.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The linear functional `⟨·, y⟩` on `ι → ℝ`. -/
noncomputable def dotCLM (y : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ := ∑ j, y j • ContinuousLinearMap.proj j

omit [MeasurableSpace X] in
theorem dotCLM_apply (y v : ι → ℝ) : dotCLM y v = dotJ v y := by
  simp [dotCLM, dotJ, mul_comm]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- **The Fréchet derivative of the free energy**: `DA(a₀) = −t ⟨·, m(a₀)⟩`. -/
theorem hasFDerivAt_affLogZ (a₀ : ι → ℝ) :
    HasFDerivAt (affLogZ μ π L₀ R t) ((-t) • dotCLM (meanMap μ π L₀ R t a₀)) a₀ := by
  obtain ⟨hZint, hZ'⟩ := hasFDerivAt_affNum hπm hπi hπ hL₀m hL₀ hR (φ := fun _ ↦ (1 : ℝ))
    measurable_const (Mφ := 1) (fun _ ↦ by simp) ht a₀
  have hT := (tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a₀ a₀ t).choose_spec
  have hZpos : 0 < priorZ μ π (affLoss L₀ R a₀) t := hT.ν_pos
  have hν : Integrable (baseWeight π (affLoss L₀ R a₀) t) μ := hT.ν_int
  have hZne : (∫ x, (fun _ ↦ (1 : ℝ)) x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x ∂μ) ≠ 0 := by
    simp only [one_mul]; exact hZpos.ne'
  have h := hZ'.log hZne
  have hfun : affLogZ μ π L₀ R t = fun a ↦
      Real.log (∫ x, (fun _ ↦ (1 : ℝ)) x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) := by
    funext a; simp [affLogZ, priorZ]
  rw [hfun]
  refine h.congr_fderiv ?_
  ext v
  rw [_root_.smul_apply, _root_.smul_apply, affNum_fderiv_apply hZint v,
    dotCLM_apply]
  simp only [one_mul, smul_eq_mul]
  have e : dotJ v (meanMap μ π L₀ R t a₀) =
      (∫ x, dirLoss R v x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x ∂μ) /
        priorZ μ π (affLoss L₀ R a₀) t := by
    change dotJ v (meanMap μ π L₀ R t a₀) = priorExp μ π (affLoss L₀ R a₀) (dirLoss R v) t
    rw [priorExp_dirLoss hν hR v]
    rfl
  rw [e]
  unfold priorZ
  field_simp

end

section Dual

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd

/-- **The dual potential** in mean coordinates, `I(y) = −t ⟨θ(y), y⟩ − A(θ(y))`. -/
noncomputable def dualPotential (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (y : ι → ℝ) : ℝ :=
  -t * dotJ (Function.invFun (meanMap μ π L₀ R t) y) y -
    affLogZ μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) y)

/-- At a realised response, `I(m(a)) = −t ⟨a, m(a)⟩ − A(a)`. -/
theorem dualPotential_meanMap (a : ι → ℝ) :
    dualPotential μ π L₀ R t (meanMap μ π L₀ R t a) =
      -t * dotJ a (meanMap μ π L₀ R t a) - affLogZ μ π L₀ R t a := by
  unfold dualPotential
  rw [invFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]

/-- **KL is the Bregman divergence of the dual potential in mean coordinates**:
`KL(P_b ‖ P_a) = I(m(b)) − I(m(a)) + t ⟨a, m(b) − m(a)⟩` (recall `∇I(m(a)) = −t a`). -/
theorem mixKL_eq_bregman_dual (a b : ι → ℝ) :
    mixKL μ π (affLoss L₀ R b) (dirLoss R (a - b)) t 0 1 =
      dualPotential μ π L₀ R t (meanMap μ π L₀ R t b) -
        dualPotential μ π L₀ R t (meanMap μ π L₀ R t a) +
        t * dotJ a (meanMap μ π L₀ R t b - meanMap μ π L₀ R t a) := by
  rw [dualPotential_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd,
    dualPotential_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd,
    mixKL_aff_eq hπm hπi hπ hπpos hL₀m hL₀ hR t b a]
  simp only [dotJ, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- The inverse Jacobian of the mean map at `a`, as a continuous linear map. -/
noncomputable def invJac (a : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ((meanMapDerivEquiv (meanMapDeriv_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a)).symm :
    (ι → ℝ) →L[ℝ] (ι → ℝ))

theorem invJac_meanMapDeriv (a v : ι → ℝ) :
    invJac hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a (meanMapDeriv μ π L₀ R t a v) = v := by
  have h := meanMapInverse_deriv_comp hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a
  have := congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) ↦ L v) h
  simpa [invJac] using this

/-- **The gradient of the dual potential is `−t` times the data coordinate**:
`DI(m(a)) = −t ⟨a, ·⟩`. -/
theorem hasFDerivAt_dualPotential (a : ι → ℝ) :
    HasFDerivAt (dualPotential μ π L₀ R t) ((-t) • dotCLM a) (meanMap μ π L₀ R t a) := by
  set θ := Function.invFun (meanMap μ π L₀ R t) with hθdef
  set E := invJac hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a with hEdef
  have hθ : HasFDerivAt θ E (meanMap μ π L₀ R t a) :=
    (hasStrictFDerivAt_invFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a).hasFDerivAt
  have hθa : θ (meanMap μ π L₀ R t a) = a := invFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a
  -- the free energy along the inverse chart
  have hA : HasFDerivAt (fun y ↦ affLogZ μ π L₀ R t (θ y))
      (((-t) • dotCLM (meanMap μ π L₀ R t a)).comp E) (meanMap μ π L₀ R t a) := by
    have h := (hasFDerivAt_affLogZ hπm hπi hπ hπpos hL₀m hL₀ hR ht (θ (meanMap μ π L₀ R t a))).comp
      (meanMap μ π L₀ R t a) hθ
    rw [hθa] at h
    exact h
  -- the bilinear term `⟨θ(y), y⟩`
  have hB : HasFDerivAt (fun y ↦ dotJ (θ y) y)
      (∑ j, (a j • ContinuousLinearMap.proj j +
        meanMap μ π L₀ R t a j • (ContinuousLinearMap.proj j).comp E)) (meanMap μ π L₀ R t a) := by
    have e : (fun y ↦ dotJ (θ y) y) = fun y ↦ ∑ j, θ y j * y j := by
      funext y; rfl
    rw [e]
    refine HasFDerivAt.fun_sum fun j _ ↦ ?_
    have h1 : HasFDerivAt (fun y ↦ θ y j) ((ContinuousLinearMap.proj j).comp E)
        (meanMap μ π L₀ R t a) :=
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι ↦ ℝ) j (θ (meanMap μ π L₀ R t a))).comp
        (meanMap μ π L₀ R t a) hθ
    have h2 : HasFDerivAt (fun y : ι → ℝ ↦ y j) (ContinuousLinearMap.proj j)
        (meanMap μ π L₀ R t a) := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι ↦ ℝ) j _
    have h := h1.mul h2
    rw [hθa] at h
    exact h
  have hI := (hB.const_mul (-t)).sub hA
  refine hI.congr_fderiv ?_
  ext v
  simp only [_root_.smul_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, _root_.sum_apply, _root_.add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, dotCLM_apply, dotJ, Finset.sum_add_distrib]
  simp only [Finset.mul_sum, mul_add]
  simp only [neg_mul, Finset.sum_neg_distrib]
  have e1 : ∑ x, t * (meanMap μ π L₀ R t a x * E v x) =
      ∑ x, t * (E v x * meanMap μ π L₀ R t a x) := Finset.sum_congr rfl fun x _ ↦ by ring
  have e2 : ∑ x, t * (a x * v x) = ∑ x, t * (v x * a x) := Finset.sum_congr rfl fun x _ ↦ by ring
  rw [e1, e2]
  ring

/-- The Hessian of the dual potential at `m(a)`: `D²I(m(a)) = −t (Dm(a))⁻¹`. -/
noncomputable def dualHessian (a : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (-t) • invJac hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a

/-- **The gradient map `y ↦ −t θ(y)` has derivative `D²I`.** -/
theorem hasFDerivAt_dualGradient (a : ι → ℝ) :
    HasFDerivAt (fun y ↦ (-t) • Function.invFun (meanMap μ π L₀ R t) y)
      (dualHessian hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a) (meanMap μ π L₀ R t a) :=
  (hasStrictFDerivAt_invFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a).hasFDerivAt.const_smul
    (-t)

/-- **`D²I` inverts the covariance**: `D²I(m(a)) (Cov_a(Rᵢ, R_v))ᵢ = v`. -/
theorem dualHessian_apply_cov (a v : ι → ℝ) :
    dualHessian hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a
      (fun i ↦ priorCov μ π (affLoss L₀ R a) (R i) (dirLoss R v) t) = v := by
  have hZ : priorZ μ π (affLoss L₀ R a) t ≠ 0 :=
    (tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a a t).choose_spec.ν_pos.ne'
  have e : (fun i ↦ priorCov μ π (affLoss L₀ R a) (R i) (dirLoss R v) t) =
      (-t)⁻¹ • meanMapDeriv μ π L₀ R t a v := by
    funext i
    rw [Pi.smul_apply, meanMapDeriv_apply hπm hπi hπ hL₀m hL₀ hR ht hZ v i, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ (by linarith : (-t) ≠ 0), one_mul]
  rw [e]
  unfold dualHessian
  rw [_root_.smul_apply, map_smul, invJac_meanMapDeriv, smul_smul,
    mul_inv_cancel₀ (by linarith : (-t) ≠ 0), one_smul]

/-- **The response form is the Hessian of the dual potential on response velocities**:
`⟨Dm(a) v, D²I(m(a)) (Dm(a) v)⟩ = G_a(v, v)`. -/
theorem dualHessian_quadratic_form (a v : ι → ℝ) :
    dotJ (meanMapDeriv μ π L₀ R t a v)
      (dualHessian hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a (meanMapDeriv μ π L₀ R t a v)) =
      responseForm μ π L₀ R a t v v := by
  have hZ : priorZ μ π (affLoss L₀ R a) t ≠ 0 :=
    (tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a a t).choose_spec.ν_pos.ne'
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  unfold dualHessian
  rw [_root_.smul_apply, invJac_meanMapDeriv]
  unfold dotJ responseForm
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [meanMapDeriv_apply hπm hπi hπ hL₀m hL₀ hR ht hZ v]
  rw [← sum_mul_priorCov_eq hν hR (bdd_dirLoss hR v) v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

end Dual

end Laplace.Multi
