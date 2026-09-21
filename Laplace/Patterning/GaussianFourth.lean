/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Multi.MonomialVisibility

/-!
# Gaussian fourth moments by Stein's identity

The Gaussian moment identities behind Proposition 8.1 of the working note *Patterning flow*
(the isotropic perturbation estimator). For the kernel `e^{-⟪x, Hx⟫/2}` on `ℝᵈ` with `H`
positive definite and `Σ = H⁻¹`:

* `stein_invDir`: Stein's identity in the direction `Σ e_a`, `∫ x_a f k = ∫ ∂_{Σ e_a} f k`;
* `integral_coord_mul_coord_quadKernel`: `E[x_a x_b] = Σ_ab`;
* `integral_coord4_quadKernel` (**Isserlis/Wick for four coordinates**):
  `E[x_a x_b x_c x_e] = Σ_ab Σ_ce + Σ_ac Σ_be + Σ_ae Σ_bc`;
* `integral_coord4_stdKernel`: the standard Gaussian case with Kronecker deltas.

All statements are for the unnormalised integrals against `quadKernel H`, with the partition
function `∫ quadKernel H` factored out.
-/

namespace Laplace.Patterning

open MeasureTheory Laplace.Multi Matrix
open scoped ContDiff

variable {d : ℕ}

/-! ### Symmetry facts for a real positive-definite matrix -/

lemma posDef_transpose {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) : Hᵀ = H := by
  have h := hH.1.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

lemma posDef_inv_transpose {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) : (H⁻¹)ᵀ = H⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, posDef_transpose hH]

lemma posDef_inv_symm {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (a b : Fin d) :
    H⁻¹ a b = H⁻¹ b a := by
  have h := congrFun (congrFun (posDef_inv_transpose hH) a) b
  rw [Matrix.transpose_apply] at h
  exact h.symm

lemma posDef_det_isUnit {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) : IsUnit H.det :=
  isUnit_iff_ne_zero.mpr hH.det_pos.ne'

/-! ### The direction `Σ e_a` -/

/-- The direction `Σ e_a = H⁻¹ e_a`. -/
noncomputable def invDir (H : Matrix (Fin d) (Fin d) ℝ) (a : Fin d) : EuclidD d :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) H⁻¹ (EuclideanSpace.single a 1)

lemma invDir_apply (H : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d) : invDir H a b = H⁻¹ b a := by
  unfold invDir
  change (WithLp.ofLp (Matrix.toEuclideanCLM (𝕜 := ℝ) H⁻¹ (EuclideanSpace.single a 1))) b = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp

/-- `½ qderiv(H, x, Σ e_a) = x_a` for symmetric positive-definite `H`. -/
theorem qderiv_invDir {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (x : EuclidD d) (a : Fin d) :
    qderiv H x (invDir H a) / 2 = x a := by
  unfold qderiv invDir
  rw [Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  have hunit := posDef_det_isUnit hH
  simp only [Matrix.ofLp_toEuclideanCLM]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, posDef_transpose hH,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  simp

/-- **Stein's identity in the direction `Σ e_a`**: `∫ x_a f k = ∫ ∂_{Σ e_a} f k`. -/
theorem stein_invDir {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {f : EuclidD d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfg : HasPolynomialGrowth f) (a : Fin d)
    (hf'g : HasPolynomialGrowth fun x ↦ fderiv ℝ f x (invDir H a)) :
    ∫ x, x a * f x * quadKernel H x = ∫ x, fderiv ℝ f x (invDir H a) * quadKernel H x := by
  rw [stein_quadKernel hH hf hfg (invDir H a) hf'g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [qderiv_invDir hH]
  ring

lemma proj_invDir {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (a i : Fin d) :
    (EuclideanSpace.proj (𝕜 := ℝ) i) (invDir H a) = H⁻¹ a i := by
  change invDir H a i = _
  rw [invDir_apply, posDef_inv_symm hH]

lemma lowPoly_coord (b : Fin d) : LowPoly 1 (fun x : EuclidD d ↦ x b) := by
  have := LowPoly.coord_mul b (LowPoly.const 0 1)
  simpa using this

lemma lowPoly_coord3 (b c e : Fin d) : LowPoly 3 (fun x : EuclidD d ↦ x b * (x c * x e)) := by
  have := LowPoly.coord_mul b (LowPoly.coord_mul c (LowPoly.coord_mul e (LowPoly.const 0 1)))
  simpa using this

/-- Integrability of a coordinate monomial against the kernel. -/
lemma integrable_coord_mul_coord_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (b c : Fin d) : Integrable fun x : EuclidD d ↦ x b * x c * quadKernel H x :=
  integrable_mul_quadKernel_of_polynomialGrowth hH
    ((contDiff_coord b).continuous.mul (contDiff_coord c).continuous).aestronglyMeasurable
    ((hasPolynomialGrowth_coord b).mul (hasPolynomialGrowth_coord c))

/-- **Second moments.** `∫ x_a x_b k = Σ_ab ∫ k`. -/
theorem integral_coord_mul_coord_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (a b : Fin d) :
    ∫ x, x a * x b * quadKernel H x = H⁻¹ a b * ∫ x, quadKernel H x := by
  have hlow := lowPoly_coord (d := d) b
  rw [stein_invDir hH hlow.contDiff hlow.growth a (hlow.deriv_dir _).growth]
  have hder : ∀ x : EuclidD d, fderiv ℝ (fun x : EuclidD d ↦ x b) x (invDir H a) = H⁻¹ a b := by
    intro x
    have hd : HasFDerivAt (fun x : EuclidD d ↦ x b) (EuclideanSpace.proj (𝕜 := ℝ) b) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt
    rw [hd.fderiv, proj_invDir hH]
  simp_rw [hder]
  rw [integral_const_mul]

/-- **Fourth moments (Isserlis).** `∫ x_a x_b x_c x_e k = (Σ_ab Σ_ce + Σ_ac Σ_be + Σ_ae Σ_bc) ∫ k`. -/
theorem integral_coord4_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (a b c e : Fin d) :
    ∫ x, x a * (x b * (x c * x e)) * quadKernel H x
      = (H⁻¹ a b * H⁻¹ c e + H⁻¹ a c * H⁻¹ b e + H⁻¹ a e * H⁻¹ b c) * ∫ x, quadKernel H x := by
  have hlow := lowPoly_coord3 (d := d) b c e
  rw [stein_invDir hH hlow.contDiff hlow.growth a (hlow.deriv_dir _).growth]
  have hder : ∀ x : EuclidD d, fderiv ℝ (fun x : EuclidD d ↦ x b * (x c * x e)) x (invDir H a)
      = H⁻¹ a b * (x c * x e) + x b * (x c * H⁻¹ a e + x e * H⁻¹ a c) := by
    intro x
    have hd : HasFDerivAt (fun x : EuclidD d ↦ x b * (x c * x e))
        ((x b) • ((x c) • EuclideanSpace.proj (𝕜 := ℝ) e + (x e) • EuclideanSpace.proj (𝕜 := ℝ) c)
          + (x c * x e) • EuclideanSpace.proj (𝕜 := ℝ) b) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt.mul
        ((EuclideanSpace.proj (𝕜 := ℝ) c).hasFDerivAt.mul
          (EuclideanSpace.proj (𝕜 := ℝ) e).hasFDerivAt)
    rw [hd.fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, proj_invDir hH]
    ring
  simp_rw [hder]
  have e1 : ∀ x : EuclidD d,
      (H⁻¹ a b * (x c * x e) + x b * (x c * H⁻¹ a e + x e * H⁻¹ a c)) * quadKernel H x
        = H⁻¹ a b * (x c * x e * quadKernel H x)
          + (H⁻¹ a e * (x b * x c * quadKernel H x) + H⁻¹ a c * (x b * x e * quadKernel H x)) :=
    fun x ↦ by ring
  simp_rw [e1]
  have hA : Integrable fun x : EuclidD d ↦ H⁻¹ a b * (x c * x e * quadKernel H x) :=
    (integrable_coord_mul_coord_quadKernel hH c e).const_mul _
  have hB : Integrable fun x : EuclidD d ↦ H⁻¹ a e * (x b * x c * quadKernel H x) :=
    (integrable_coord_mul_coord_quadKernel hH b c).const_mul _
  have hC : Integrable fun x : EuclidD d ↦ H⁻¹ a c * (x b * x e * quadKernel H x) :=
    (integrable_coord_mul_coord_quadKernel hH b e).const_mul _
  have hBC : Integrable fun x : EuclidD d ↦
      H⁻¹ a e * (x b * x c * quadKernel H x) + H⁻¹ a c * (x b * x e * quadKernel H x) := hB.add hC
  rw [integral_add hA hBC, integral_add hB hC, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_coord_mul_coord_quadKernel hH,
    integral_coord_mul_coord_quadKernel hH, integral_coord_mul_coord_quadKernel hH]
  ring

/-! ### The standard Gaussian -/

lemma quadKernel_one_eq_stdKernel (x : EuclidD d) :
    quadKernel (1 : Matrix (Fin d) (Fin d) ℝ) x = stdKernel x := by
  unfold quadKernel qform stdKernel
  rw [map_one, ContinuousLinearMap.one_apply, real_inner_self_eq_norm_sq]

/-- **Standard Gaussian fourth moments.**
`∫ x_a x_b x_c x_e e^{-|x|²/2} = (δ_ab δ_ce + δ_ac δ_be + δ_ae δ_bc) (2π)^{d/2}`. -/
theorem integral_coord4_stdKernel (a b c e : Fin d) :
    ∫ x : EuclidD d, x a * (x b * (x c * x e)) * stdKernel x
      = ((if a = b then (1 : ℝ) else 0) * (if c = e then 1 else 0)
          + (if a = c then (1 : ℝ) else 0) * (if b = e then 1 else 0)
          + (if a = e then (1 : ℝ) else 0) * (if b = c then 1 else 0))
        * (2 * Real.pi) ^ ((d : ℝ) / 2) := by
  have h := integral_coord4_quadKernel (Matrix.PosDef.one (n := Fin d) (R := ℝ)) a b c e
  simp only [quadKernel_one_eq_stdKernel, inv_one, Matrix.one_apply, integral_stdKernel] at h
  exact h

/-! ### Quadratic forms: Isserlis for the covariance of two quadratic observables -/

/-- `⟪x, A x⟫ = ∑ i j, A_ij x_i x_j`. -/
lemma qform_eq_sum (A : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    qform A x = ∑ i, ∑ j, A i j * (x i * x j) := by
  rw [qform_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Integrability of a fourth-order coordinate monomial against the kernel. -/
lemma integrable_coord4_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (i j k l : Fin d) :
    Integrable fun x : EuclidD d ↦ x i * (x j * (x k * x l)) * quadKernel H x :=
  integrable_mul_quadKernel_of_polynomialGrowth hH
    ((contDiff_coord i).continuous.mul ((contDiff_coord j).continuous.mul
      ((contDiff_coord k).continuous.mul (contDiff_coord l).continuous))).aestronglyMeasurable
    ((hasPolynomialGrowth_coord i).mul ((hasPolynomialGrowth_coord j).mul
      ((hasPolynomialGrowth_coord k).mul (hasPolynomialGrowth_coord l))))

/-- The product of two quadratic forms times the kernel as a four-fold sum. -/
lemma qform_mul_qform_mul_quadKernel (A B H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    qform A x * qform B x * quadKernel H x
      = ∑ i, ∑ k, ∑ j, ∑ l, (A i j * B k l) * (x i * (x j * (x k * x l)) * quadKernel H x) := by
  rw [qform_eq_sum, qform_eq_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `∫ ∑∑∑∑ f = ∑∑∑∑ ∫ f` for integrable summands. -/
lemma integral_sum4 (f : Fin d → Fin d → Fin d → Fin d → EuclidD d → ℝ)
    (hf : ∀ i k j l, Integrable (f i k j l)) :
    ∫ x, ∑ i, ∑ k, ∑ j, ∑ l, f i k j l x = ∑ i, ∑ k, ∑ j, ∑ l, ∫ x, f i k j l x := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hf i k j l]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun l _ => hf i k j l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hf i k j l]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun l _ => hf i k j l]

/-- `∫ ∑∑ f = ∑∑ ∫ f` for integrable summands. -/
lemma integral_sum2 (f : Fin d → Fin d → EuclidD d → ℝ) (hf : ∀ i j, Integrable (f i j)) :
    ∫ x, ∑ i, ∑ j, f i j x = ∑ i, ∑ j, ∫ x, f i j x := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hf i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hf i j]

/-- `tr(A S) = ∑ i j, A_ij S_ji`. -/
lemma trace_mul_eq_sum2 (A S : Matrix (Fin d) (Fin d) ℝ) :
    (A * S).trace = ∑ i, ∑ j, A i j * S j i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-- `tr(A S B T) = ∑ i l k j, A_ij S_jk B_kl T_li` (in the order the products expand). -/
lemma trace_mul4_eq_sum (A S B T : Matrix (Fin d) (Fin d) ℝ) :
    (A * S * B * T).trace = ∑ i, ∑ l, ∑ k, ∑ j, A i j * S j k * B k l * T l i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]

/-- **Expectation of one quadratic form.** `∫ ⟪x, Ax⟫ k = tr(A Σ) ∫ k`. -/
theorem integral_qform_mul_quadKernel' {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (A : Matrix (Fin d) (Fin d) ℝ) :
    ∫ x, qform A x * quadKernel H x = (A * H⁻¹).trace * ∫ x, quadKernel H x := by
  have hq : ∀ x : EuclidD d, qform A x * quadKernel H x
      = ∑ i, ∑ j, A i j * (x i * x j * quadKernel H x) := by
    intro x
    rw [qform_eq_sum]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hq]
  rw [integral_sum2 (fun i j x => A i j * (x i * x j * quadKernel H x))
    (fun i j => (integrable_coord_mul_coord_quadKernel hH i j).const_mul _)]
  simp_rw [integral_const_mul, integral_coord_mul_coord_quadKernel hH, trace_mul_eq_sum2,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [posDef_inv_symm hH j i]
  ring

/-- **Isserlis for two quadratic forms** (unnormalised).
`∫ ⟪x,Ax⟫⟪x,Bx⟫ k = (tr(AΣ) tr(BΣ) + tr(AΣBΣ) + tr(AΣBᵀΣ)) ∫ k`. -/
theorem integral_qform_mul_qform_mul_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (A B : Matrix (Fin d) (Fin d) ℝ) :
    ∫ x, qform A x * qform B x * quadKernel H x
      = ((A * H⁻¹).trace * (B * H⁻¹).trace + (A * H⁻¹ * B * H⁻¹).trace
          + (A * H⁻¹ * Bᵀ * H⁻¹).trace) * ∫ x, quadKernel H x := by
  set S := H⁻¹ with hS
  have hsymm : ∀ p q, S p q = S q p := posDef_inv_symm hH
  simp_rw [qform_mul_qform_mul_quadKernel A B H]
  rw [integral_sum4 _ fun i k j l => (integrable_coord4_quadKernel hH i j k l).const_mul _]
  simp_rw [integral_const_mul, integral_coord4_quadKernel hH]
  -- reduce to the three finite-sum identities
  have L1 : ∑ i, ∑ k, ∑ j, ∑ l, A i j * B k l * (S i j * S k l) = (A * S).trace * (B * S).trace := by
    rw [trace_mul_eq_sum2, trace_mul_eq_sum2, Finset.sum_mul_sum]
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hsymm j i, hsymm l k]
    ring
  have L3 : ∑ i, ∑ k, ∑ j, ∑ l, A i j * B k l * (S i l * S j k) = (A * S * B * S).trace := by
    rw [trace_mul4_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hsymm l i]
    ring
  have L2 : ∑ i, ∑ k, ∑ j, ∑ l, A i j * B k l * (S i k * S j l) = (A * S * Bᵀ * S).trace := by
    rw [trace_mul4_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => arg 2; ext k; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.transpose_apply, hsymm k i]
    ring
  rw [← L1, ← L2, ← L3]
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Covariance of two quadratic forms** (Proposition 8.1, Isserlis):
`Cov(⟪x,Ax⟫, ⟪x,Bx⟫) = tr(AΣBΣ) + tr(AΣBᵀΣ)` under `N(0, Σ)`, `Σ = H⁻¹`. -/
theorem gaussianCovariance_qform_qform {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (A B : Matrix (Fin d) (Fin d) ℝ) :
    gaussianCovariance H (qform A) (qform B)
      = (A * H⁻¹ * B * H⁻¹).trace + (A * H⁻¹ * Bᵀ * H⁻¹).trace := by
  have hZ : (∫ x : EuclidD d, quadKernel H x) ≠ 0 := (integral_quadKernel_pos hH).ne'
  unfold gaussianCovariance gaussianExpectation
  have h2 : (∫ x : EuclidD d, qform A x * qform B x * quadKernel H x)
      = ∫ x : EuclidD d, (fun x ↦ qform A x * qform B x) x * quadKernel H x := rfl
  rw [← h2, integral_qform_mul_qform_mul_quadKernel hH, integral_qform_mul_quadKernel' hH,
    integral_qform_mul_quadKernel' hH]
  field_simp
  ring

/-- **The symmetric case.** For symmetric `B`, `Cov(½⟪x,Ax⟫, ½⟪x,Bx⟫) = ½ tr(AΣBΣ)`. -/
theorem gaussianCovariance_half_qform {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (A B : Matrix (Fin d) (Fin d) ℝ) (hB : Bᵀ = B) :
    gaussianCovariance H (fun x ↦ qform A x / 2) (fun x ↦ qform B x / 2)
      = (1 / 2) * (A * H⁻¹ * B * H⁻¹).trace := by
  have hZ : (∫ x : EuclidD d, quadKernel H x) ≠ 0 := (integral_quadKernel_pos hH).ne'
  have hcov := gaussianCovariance_qform_qform hH A B
  rw [hB] at hcov
  unfold gaussianCovariance gaussianExpectation at hcov ⊢
  have e1 : (fun x : EuclidD d ↦ qform A x / 2 * (qform B x / 2) * quadKernel H x)
      = fun x ↦ (1 / 4) * (qform A x * qform B x * quadKernel H x) := by
    funext x
    ring
  have e2 : (fun x : EuclidD d ↦ qform A x / 2 * quadKernel H x)
      = fun x ↦ (1 / 2) * (qform A x * quadKernel H x) := by
    funext x
    ring
  have e3 : (fun x : EuclidD d ↦ qform B x / 2 * quadKernel H x)
      = fun x ↦ (1 / 2) * (qform B x * quadKernel H x) := by
    funext x
    ring
  simp only [e1, e2, e3, integral_const_mul]
  rw [integral_qform_mul_qform_mul_quadKernel hH, integral_qform_mul_quadKernel' hH,
    integral_qform_mul_quadKernel' hH, hB]
  field_simp
  ring

/-! ### The cubic–linear term -/

/-- The linear observable `gᵀx = ∑ m, g_m x_m`. -/
def linForm (g : Fin d → ℝ) (x : EuclidD d) : ℝ := ∑ m, g m * x m

/-- The cubic form `T(x,x,x) = ∑ j k l, T_jkl x_j x_k x_l`. -/
def cubicForm (T : Fin d → Fin d → Fin d → ℝ) (x : EuclidD d) : ℝ :=
  ∑ j, ∑ k, ∑ l, T j k l * (x j * (x k * x l))

/-- The contraction `(T:S)_j = ∑ k l, T_jkl S_kl`. -/
def contract (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ :=
  ∑ k, ∑ l, T j k l * S k l

lemma linForm_mul_cubicForm_mul_quadKernel (g : Fin d → ℝ) (T : Fin d → Fin d → Fin d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    linForm g x * cubicForm T x * quadKernel H x
      = ∑ m, ∑ j, ∑ k, ∑ l, (g m * T j k l) * (x m * (x j * (x k * x l)) * quadKernel H x) := by
  unfold linForm cubicForm
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The cubic–linear Gaussian moment** (Proposition 8.1): for a fully symmetric 3-tensor `T`,
`∫ (gᵀx) T(x,x,x) k = 3 ∑ m j, g_m Σ_mj (T:Σ)_j ∫ k = 3 (Σg)ᵀ(T:Σ) ∫ k`. -/
theorem integral_linForm_mul_cubicForm_mul_quadKernel {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (g : Fin d → ℝ) (T : Fin d → Fin d → Fin d → ℝ)
    (hT : ∀ j k l, T j k l = T j l k ∧ T j k l = T k j l) :
    ∫ x, linForm g x * cubicForm T x * quadKernel H x
      = 3 * (∑ m, ∑ j, g m * H⁻¹ m j * contract T H⁻¹ j) * ∫ x, quadKernel H x := by
  simp_rw [linForm_mul_cubicForm_mul_quadKernel g T H]
  rw [integral_sum4 _ fun m j k l => (integrable_coord4_quadKernel hH m j k l).const_mul _]
  simp_rw [integral_const_mul, integral_coord4_quadKernel hH]
  have hsymm := posDef_inv_symm hH
  have P1 : ∑ m, ∑ j, ∑ k, ∑ l, g m * T j k l * (H⁻¹ m j * H⁻¹ k l)
      = ∑ m, ∑ j, g m * H⁻¹ m j * contract T H⁻¹ j := by
    unfold contract
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have P2 : ∑ m, ∑ j, ∑ k, ∑ l, g m * T j k l * (H⁻¹ m k * H⁻¹ j l)
      = ∑ m, ∑ j, g m * H⁻¹ m j * contract T H⁻¹ j := by
    unfold contract
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    rw [(hT j k l).2]
    ring
  have P3 : ∑ m, ∑ j, ∑ k, ∑ l, g m * T j k l * (H⁻¹ m l * H⁻¹ j k)
      = ∑ m, ∑ j, g m * H⁻¹ m j * contract T H⁻¹ j := by
    unfold contract
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [show T l j k = T j k l from by rw [(hT l j k).2, (hT j l k).1]]
    ring
  have hX : 3 * (∑ m, ∑ j, g m * H⁻¹ m j * contract T H⁻¹ j) * ∫ x, quadKernel H x
      = ((∑ m, ∑ j, ∑ k, ∑ l, g m * T j k l * (H⁻¹ m j * H⁻¹ k l))
          + (∑ m, ∑ j, ∑ k, ∑ l, g m * T j k l * (H⁻¹ m k * H⁻¹ j l))
          + (∑ m, ∑ j, ∑ k, ∑ l, g m * T j k l * (H⁻¹ m l * H⁻¹ j k))) * ∫ x, quadKernel H x := by
    rw [P1, P2, P3]
    ring
  rw [hX]
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The cubic–linear term of Proposition 8.1, normalised.**
`E[(gᵀδ) · ⅙ Q(δ,δ,δ)] = ½ (Σg)ᵀ (Q:Σ)` under `N(0, Σ)`, `Σ = H⁻¹`, for symmetric `Q`. -/
theorem gaussianExpectation_linForm_mul_cubicForm_div_six {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (g : Fin d → ℝ) (T : Fin d → Fin d → Fin d → ℝ)
    (hT : ∀ j k l, T j k l = T j l k ∧ T j k l = T k j l) :
    gaussianExpectation H (fun x ↦ linForm g x * (cubicForm T x / 6))
      = (1 / 2) * ∑ j, (∑ m, H⁻¹ j m * g m) * contract T H⁻¹ j := by
  have hZ : (∫ x : EuclidD d, quadKernel H x) ≠ 0 := (integral_quadKernel_pos hH).ne'
  unfold gaussianExpectation
  have e : (fun x : EuclidD d ↦ linForm g x * (cubicForm T x / 6) * quadKernel H x)
      = fun x ↦ (1 / 6) * (linForm g x * cubicForm T x * quadKernel H x) := by
    funext x
    ring
  simp only [e, integral_const_mul]
  rw [integral_linForm_mul_cubicForm_mul_quadKernel hH g T hT]
  field_simp
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [posDef_inv_symm hH j m]
  ring

/-! ### Odd moments and the linear observables of Proposition 8.1 -/

/-- **First moments vanish.** `∫ x_a k = 0`. -/
theorem integral_coord_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (a : Fin d) :
    ∫ x, x a * quadKernel H x = 0 := by
  have hlow : LowPoly 0 (fun _ : EuclidD d ↦ (1 : ℝ)) := LowPoly.const 0 1
  have h := stein_invDir hH hlow.contDiff hlow.growth a (hlow.deriv_dir _).growth
  have hder : ∀ x : EuclidD d, fderiv ℝ (fun _ : EuclidD d ↦ (1 : ℝ)) x (invDir H a) = 0 := by
    intro x
    simp
  simp only [mul_one] at h
  rw [h]
  simp_rw [hder, zero_mul, integral_zero]

/-- **Third moments vanish.** `∫ x_a x_b x_c k = 0`. -/
theorem integral_coord3_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (a b c : Fin d) :
    ∫ x, x a * (x b * x c) * quadKernel H x = 0 := by
  have hlow : LowPoly 2 (fun x : EuclidD d ↦ x b * x c) := by
    have := LowPoly.coord_mul b (LowPoly.coord_mul c (LowPoly.const 0 1))
    simpa using this
  rw [stein_invDir hH hlow.contDiff hlow.growth a (hlow.deriv_dir _).growth]
  have hder : ∀ x : EuclidD d, fderiv ℝ (fun x : EuclidD d ↦ x b * x c) x (invDir H a)
      = H⁻¹ a b * x c + x b * H⁻¹ a c := by
    intro x
    have hd : HasFDerivAt (fun x : EuclidD d ↦ x b * x c)
        ((x b) • EuclideanSpace.proj (𝕜 := ℝ) c + (x c) • EuclideanSpace.proj (𝕜 := ℝ) b) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt.mul
        (EuclideanSpace.proj (𝕜 := ℝ) c).hasFDerivAt
    rw [hd.fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, proj_invDir hH]
    ring
  simp_rw [hder]
  have e1 : ∀ x : EuclidD d, (H⁻¹ a b * x c + x b * H⁻¹ a c) * quadKernel H x
      = H⁻¹ a b * (x c * quadKernel H x) + H⁻¹ a c * (x b * quadKernel H x) := fun x ↦ by ring
  simp_rw [e1]
  have hI : ∀ i : Fin d, Integrable fun x : EuclidD d ↦ x i * quadKernel H x := fun i ↦
    integrable_mul_quadKernel_of_polynomialGrowth hH
      (contDiff_coord i).continuous.aestronglyMeasurable (hasPolynomialGrowth_coord i)
  rw [integral_add ((hI c).const_mul _) ((hI b).const_mul _), integral_const_mul, integral_const_mul,
    integral_coord_quadKernel hH, integral_coord_quadKernel hH]
  ring

/-- **The gradient–gradient term of Proposition 8.1**: `Cov(aᵀx, gᵀx) = aᵀ Σ g`. -/
theorem gaussianCovariance_linForm_linForm {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (a g : Fin d → ℝ) :
    gaussianCovariance H (linForm a) (linForm g) = ∑ m, ∑ n, a m * H⁻¹ m n * g n := by
  have hZ : (∫ x : EuclidD d, quadKernel H x) ≠ 0 := (integral_quadKernel_pos hH).ne'
  unfold gaussianCovariance gaussianExpectation
  have hlin : ∀ (c : Fin d → ℝ) (x : EuclidD d), linForm c x * quadKernel H x
      = ∑ m, c m * (x m * quadKernel H x) := by
    intro c x
    unfold linForm
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    ring
  have hI : ∀ i : Fin d, Integrable fun x : EuclidD d ↦ x i * quadKernel H x := fun i ↦
    integrable_mul_quadKernel_of_polynomialGrowth hH
      (contDiff_coord i).continuous.aestronglyMeasurable (hasPolynomialGrowth_coord i)
  have hE : ∀ c : Fin d → ℝ, ∫ x : EuclidD d, linForm c x * quadKernel H x = 0 := by
    intro c
    simp_rw [hlin]
    rw [integral_finsetSum _ fun m _ ↦ (hI m).const_mul _]
    simp_rw [integral_const_mul, integral_coord_quadKernel hH, mul_zero, Finset.sum_const_zero]
  have hprod : ∀ x : EuclidD d, linForm a x * linForm g x * quadKernel H x
      = ∑ m, ∑ n, (a m * g n) * (x m * x n * quadKernel H x) := by
    intro x
    unfold linForm
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun n _ ↦ ?_
    ring
  have h2 : (∫ x : EuclidD d, (fun x ↦ linForm a x * linForm g x) x * quadKernel H x)
      = ∫ x : EuclidD d, linForm a x * linForm g x * quadKernel H x := rfl
  rw [h2]
  simp_rw [hprod]
  rw [integral_sum2 (fun m n x ↦ (a m * g n) * (x m * x n * quadKernel H x))
    (fun m n ↦ (integrable_coord_mul_coord_quadKernel hH m n).const_mul _)]
  simp_rw [integral_const_mul, integral_coord_mul_coord_quadKernel hH]
  rw [hE, hE]
  simp only [zero_div, mul_zero, sub_zero]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  field_simp

/-- **The quadratic–linear term vanishes** (Proposition 8.1, "by symmetry"):
`∫ ⟪x,Ax⟫ (gᵀx) k = 0`. -/
theorem integral_qform_mul_linForm_mul_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (A : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    ∫ x, qform A x * linForm g x * quadKernel H x = 0 := by
  have hprod : ∀ x : EuclidD d, qform A x * linForm g x * quadKernel H x
      = ∑ i, ∑ m, ∑ j, (A i j * g m) * (x i * (x j * x m) * quadKernel H x) := by
    intro x
    rw [qform_eq_sum]
    unfold linForm
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun m _ ↦
      Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  simp_rw [hprod]
  have hI : ∀ i j m : Fin d, Integrable fun x : EuclidD d ↦ x i * (x j * x m) * quadKernel H x :=
    fun i j m ↦ integrable_mul_quadKernel_of_polynomialGrowth hH
      ((contDiff_coord i).continuous.mul ((contDiff_coord j).continuous.mul
        (contDiff_coord m).continuous)).aestronglyMeasurable
      ((hasPolynomialGrowth_coord i).mul ((hasPolynomialGrowth_coord j).mul
        (hasPolynomialGrowth_coord m)))
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun m _ ↦
    integrable_finsetSum _ fun j _ ↦ (hI i j m).const_mul _]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [integral_finsetSum _ fun m _ ↦ integrable_finsetSum _ fun j _ ↦ (hI i j m).const_mul _]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ (hI i j m).const_mul _]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [integral_const_mul, integral_coord3_quadKernel hH, mul_zero]

end Laplace.Patterning
