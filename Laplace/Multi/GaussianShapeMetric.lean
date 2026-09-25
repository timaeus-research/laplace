/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.AnchoredVarianceGap
import Laplace.Multi.ThermoLength

/-!
# The response metric of a Gaussian family is Fisher–Rao on covariances, exactly

For Gaussian losses `L_a(w) = ½ wᵀ H_a w` with `H_a = H₀ + ∑ aᵢ Bᵢ` (a data family that moves the
posterior *shape* while keeping the minimiser at `0`), the response form is **independent of the
temperature** and equals half the trace of the square of `B_v H_a⁻¹`:

  `g_a(v, v) = t² Var_{t,a}(½ wᵀ B_v w) = ½ tr((B_v H_a⁻¹)²)`   (`responseForm_gaussian_self`),

for every `t > 0`. This is the Fisher–Rao metric on centred Gaussians in their covariance
`Σ = H⁻¹`, `½ tr(Σ⁻¹ dΣ Σ⁻¹ dΣ)`, read in the precision: the response map of a Gaussian family is
an isometry from the Hessian geometry of the data onto the Fisher–Rao geometry of the posterior
shapes, with no `t`-dependence at all. It is the exact form of Astra's "order-one shape metric"
`½ tr(H⁻¹ D_uH H⁻¹ D_vH)`, which for general regular families is only a limit; and it shows that the
`O(1)` scale of the thermodynamic distance (directions preserving the minimiser) is nontrivial.

The proof is the Wick variance of a quadratic form under a tilted Gaussian
(`Laplace.Sampler.tiltedVar_quadForm`) after identifying `e^{-t·½wᵀHw}` with the tilted weight of
precision `tH` and zero tilt (`priorExp_gaussLoss_eq_tilted`).
-/

open MeasureTheory Filter Topology Set Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- The Gaussian loss `½ wᵀ H w`. -/
noncomputable def gaussLoss (H : Matrix ι ι ℝ) : (ι → ℝ) → ℝ := fun w ↦ (1 / 2) * (w ⬝ᵥ H *ᵥ w)

/-- The posterior of a Gaussian loss at temperature `t` and flat prior is the tilted Gaussian of
precision `tH` and zero tilt. -/
theorem priorExp_gaussLoss_eq_tilted (H : Matrix ι ι ℝ) (φ : (ι → ℝ) → ℝ) (t : ℝ) :
    priorExp volume (fun _ ↦ (1 : ℝ)) (gaussLoss H) φ t = tiltedExpectation (t • H) 0 φ := by
  unfold priorExp priorZ tiltedExpectation tiltedZ
  have e : ∀ w, Real.exp (-(t * gaussLoss H w)) * 1 = tiltedWeight (t • H) 0 w := fun w ↦ by
    unfold gaussLoss tiltedWeight
    rw [mul_one, Matrix.smul_mulVec, dotProduct_smul, zero_dotProduct, smul_eq_mul]
    congr 1
    ring
  simp only [mul_assoc]
  simp_rw [e]

omit [Fintype ι] in
/-- A real linear combination of Hermitian matrices is Hermitian. -/
theorem isHermitian_sum_smul {κ : Type*} [Fintype κ] {B : κ → Matrix ι ι ℝ}
    (hB : ∀ i, (B i).IsHermitian) (v : κ → ℝ) : (∑ i, v i • B i).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Matrix.conjTranspose_smul, (hB i).eq, star_trivial]

/-- **The Gaussian shape metric**: `t² Var_t(½ wᵀBw) = ½ tr((B H⁻¹)²)` under `e^{-t·½wᵀHw}`, for
every `t > 0`. -/
theorem sq_mul_priorCov_gaussLoss [DecidableEq ι] {H B : Matrix ι ι ℝ} (hH : H.PosDef)
    (hB : B.IsHermitian) {t : ℝ} (ht : 0 < t) :
    t ^ 2 * priorCov volume (fun _ ↦ (1 : ℝ)) (gaussLoss H) (gaussLoss B) (gaussLoss B) t =
      (1 / 2) * Matrix.trace (B * H⁻¹ * (B * H⁻¹)) := by
  have hP : (t • H).PosDef := hH.smul ht
  unfold priorCov
  have e2 : (fun x ↦ gaussLoss B x * gaussLoss B x) = fun w ↦ (1 / 4) * (w ⬝ᵥ B *ᵥ w) ^ 2 := by
    funext w
    unfold gaussLoss
    ring
  rw [e2, priorExp_gaussLoss_eq_tilted, priorExp_gaussLoss_eq_tilted, tiltedExpectation_const_mul]
  unfold gaussLoss
  rw [tiltedExpectation_const_mul]
  have hvar := Laplace.Sampler.tiltedVar_quadForm hP 0 hB
  have hm : tiltMean (t • H) 0 = 0 := by
    unfold tiltMean
    exact Matrix.mulVec_zero _
  simp only [hm, Matrix.mulVec_zero, dotProduct_zero, mul_zero, add_zero] at hvar
  have hinv : (t • H)⁻¹ = t⁻¹ • H⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht.ne', one_smul,
      Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hH.det_pos.ne')]
  rw [hinv] at hvar
  simp only [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul] at hvar
  have htr : Matrix.trace (B * H⁻¹ * (B * H⁻¹)) = ∑ a, ∑ c, (B * H⁻¹) a c * (B * H⁻¹) c a := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact Finset.sum_congr rfl fun a _ ↦ Matrix.mul_apply
  have hS : ∑ a, ∑ c, t⁻¹ * (B * H⁻¹) a c * (t⁻¹ * (B * H⁻¹) c a) =
      t⁻¹ * t⁻¹ * ∑ a, ∑ c, (B * H⁻¹) a c * (B * H⁻¹) c a := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun c _ ↦ by ring
  rw [hS] at hvar
  rw [htr]
  set E2 := tiltedExpectation (t • H) 0 (fun u ↦ (u ⬝ᵥ B *ᵥ u) ^ 2) with hE2
  set E1 := tiltedExpectation (t • H) 0 (fun u ↦ u ⬝ᵥ B *ᵥ u) with hE1
  set S := ∑ a, ∑ c, (B * H⁻¹) a c * (B * H⁻¹) c a with hSdef
  clear_value E2 E1 S
  have h1 : t ^ 2 * (t⁻¹ * t⁻¹) = 1 := by
    rw [show t ^ 2 * (t⁻¹ * t⁻¹) = (t * t⁻¹) * (t * t⁻¹) by ring, mul_inv_cancel₀ ht.ne', one_mul]
  have hvar' : t ^ 2 * (E2 - E1 ^ 2) = 2 * S := by
    rw [hvar]
    linear_combination 2 * S * h1
  linear_combination (1 / 4) * hvar'

/-- The affine Gaussian family: `affLoss (½wᵀH₀w) (½wᵀBᵢw) a = ½ wᵀ(H₀ + ∑ aᵢBᵢ)w`. -/
theorem affLoss_gaussLoss (H₀ : Matrix ι ι ℝ) {κ : Type*} [Fintype κ] (B : κ → Matrix ι ι ℝ)
    (a : κ → ℝ) :
    affLoss (gaussLoss H₀) (fun i ↦ gaussLoss (B i)) a = gaussLoss (H₀ + ∑ i, a i • B i) := by
  funext w
  simp only [affLoss, gaussLoss, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The direction losses of the Gaussian family: `dirLoss (½wᵀBᵢw) v = ½ wᵀ(∑ vᵢBᵢ)w`. -/
theorem dirLoss_gaussLoss {κ : Type*} [Fintype κ] (B : κ → Matrix ι ι ℝ) (v : κ → ℝ) :
    dirLoss (fun i ↦ gaussLoss (B i)) v = gaussLoss (∑ i, v i • B i) := by
  funext w
  simp only [dirLoss, gaussLoss, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **The response form of a Gaussian family is Fisher–Rao on covariances, for every `t`**:
`g_a(v, v) = ½ tr((B_v H_a⁻¹)²)`. -/
theorem responseForm_gaussian_self [DecidableEq ι] (H₀ : Matrix ι ι ℝ) {κ : Type*} [Fintype κ]
    {B : κ → Matrix ι ι ℝ} (hB : ∀ i, (B i).IsHermitian) (a : κ → ℝ)
    (hH : (H₀ + ∑ i, a i • B i).PosDef) {t : ℝ} (ht : 0 < t) (v : κ → ℝ) :
    responseForm volume (fun _ ↦ (1 : ℝ)) (gaussLoss H₀) (fun i ↦ gaussLoss (B i)) a t v v =
      (1 / 2) * Matrix.trace ((∑ i, v i • B i) * (H₀ + ∑ i, a i • B i)⁻¹ *
        ((∑ i, v i • B i) * (H₀ + ∑ i, a i • B i)⁻¹)) := by
  unfold responseForm
  rw [affLoss_gaussLoss, dirLoss_gaussLoss]
  exact sq_mul_priorCov_gaussLoss hH (isHermitian_sum_smul hB v) ht

/-- **The Fisher speed of a Gaussian shape path is `½ tr((H_s⁻¹ Ḣ_s)²)`, for every `t`.** -/
theorem fisherSpeed_gaussian [DecidableEq ι] (H₀ B : Matrix ι ι ℝ) (hB : B.IsHermitian) {s : ℝ}
    (hH : (H₀ + s • B).PosDef) {t : ℝ} (ht : 0 < t) :
    fisherSpeed volume (fun _ ↦ (1 : ℝ)) (fun s ↦ gaussLoss (H₀ + s • B)) (fun _ ↦ gaussLoss B) t s
      = (1 / 2) * Matrix.trace (B * (H₀ + s • B)⁻¹ * (B * (H₀ + s • B)⁻¹)) :=
  sq_mul_priorCov_gaussLoss hH hB ht

end Laplace.Multi
