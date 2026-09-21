/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.CStarAlgebra.Matrix
import Laplace.Sampler.ULA

/-!
# Gaussian laws under the ULA step, and the invariance of `N(0, Σ_ULA)`

One step of the unadjusted Langevin algorithm on a Gaussian target is the affine map
`w ↦ A w + √(2h) ξ` with `A = I - hP` and `ξ ~ N(0, I)`. In Mathlib's language the law of the
output, when the input has law `μ`, is the convolution `(μ.map A) ∗ N(0, 2h I)`. This file proves

* `multivariateGaussian_map_euclid`: `N(m, S).map A = N(A m, A S Aᵀ)`;
* `multivariateGaussian_conv`: `N(m, S) ∗ N(b, R) = N(m + b, S + R)`;
* `multivariateGaussian_map_conv`: `(N(m, S).map A) ∗ N(b, R) = N(A m + b, A S Aᵀ + R)`;
* `invariant_of_covStep_fixed` and `ulaCov_invariant`: a centred Gaussian whose covariance is a
  fixed point of the covariance step is invariant; in particular `N(0, Σ_ULA)` is invariant under
  the ULA step, so the covariance recursion of `Laplace/Sampler/ULA.lean` really describes the
  stationary law of the chain;
* `gaussStep_iterate`: the finite-time marginal law `N(A^k m₀, Σ_k)` with `Σ_k` the iterate of the
  covariance step, and `gaussStep_iterate_zero`: from the mode, `Σ_k = S - A^k S (Aᵀ)^k`.

All statements carry explicit positive-semidefiniteness hypotheses: Mathlib's
`multivariateGaussian` degenerates to a Dirac mass off the positive semidefinite cone.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The continuous linear map of a real matrix on Euclidean space. -/
noncomputable abbrev euclid (A : Matrix ι ι ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  toEuclideanCLM (𝕜 := ℝ) A

/-- The adjoint of a real matrix acting on Euclidean space is its transpose. -/
theorem euclid_adjoint (A : Matrix ι ι ℝ) :
    ContinuousLinearMap.adjoint (euclid A) = euclid Aᵀ := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

theorem euclid_pow (A : Matrix ι ι ℝ) (k : ℕ) : euclid (A ^ k) = euclid A ^ k := map_pow _ _ _

theorem euclid_mul (A B : Matrix ι ι ℝ) : euclid (A * B) = euclid A * euclid B := map_mul _ _ _

omit [DecidableEq ι] in
/-- The quadratic form of `A S Aᵀ` is the quadratic form of `S` at the transported vectors. -/
lemma dotProduct_conj_mulVec (A S : Matrix ι ι ℝ) (x y : ι → ℝ) :
    (Aᵀ *ᵥ x) ⬝ᵥ S *ᵥ (Aᵀ *ᵥ y) = x ⬝ᵥ (A * S * Aᵀ) *ᵥ y := by
  rw [mulVec_transpose A x, dotProduct_mulVec, vecMul_vecMul, dotProduct_mulVec, vecMul_vecMul,
    dotProduct_mulVec]

omit [DecidableEq ι] in
/-- `A S Aᵀ` is positive semidefinite for `S ⪰ 0`. -/
theorem posSemidef_conj {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (A : Matrix ι ι ℝ) :
    (A * S * Aᵀ).PosSemidef := by
  have := hS.conjTranspose_mul_mul_same Aᵀ
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at this

omit [DecidableEq ι] in
/-- The covariance step preserves positive semidefiniteness. -/
theorem covStep_posSemidef {S R : Matrix ι ι ℝ} (hS : S.PosSemidef) (hR : R.PosSemidef)
    (A : Matrix ι ι ℝ) : (covStep A R S).PosSemidef :=
  (posSemidef_conj hS A).add hR

omit [DecidableEq ι] in
theorem covStep_iterate_posSemidef {S R : Matrix ι ι ℝ} (hS : S.PosSemidef) (hR : R.PosSemidef)
    (A : Matrix ι ι ℝ) (k : ℕ) : ((covStep A R)^[k] S).PosSemidef := by
  induction k with
  | zero => simpa using hS
  | succ k ih => rw [Function.iterate_succ_apply']; exact covStep_posSemidef ih hR A

/-! ### Push-forward and convolution of Gaussians -/

/-- **Push-forward of a Gaussian by a matrix**: `N(m, S).map A = N(A m, A S Aᵀ)`. -/
theorem multivariateGaussian_map_euclid {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (A : Matrix ι ι ℝ) (m : EuclideanSpace ℝ ι) :
    (multivariateGaussian m S).map (euclid A) = multivariateGaussian (euclid A m) (A * S * Aᵀ) := by
  have hS' := posSemidef_conj hS A
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_multivariateGaussian]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, euclid_adjoint,
      covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hS',
      ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, dotProduct_conj_mulVec]

/-- **Convolution of Gaussians**: `N(m, S) ∗ N(b, R) = N(m + b, S + R)`. -/
theorem multivariateGaussian_conv {S R : Matrix ι ι ℝ} (hS : S.PosSemidef) (hR : R.PosSemidef)
    (m b : EuclideanSpace ℝ ι) :
    multivariateGaussian m S ∗ multivariateGaussian b R = multivariateGaussian (m + b) (S + R) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv, charFun_multivariateGaussian hS, charFun_multivariateGaussian hR,
    charFun_multivariateGaussian (hS.add hR), ← Complex.exp_add, inner_add_right, add_mulVec,
    dotProduct_add]
  congr 1
  push_cast
  ring

/-- **Law of one affine Gaussian step**: `(N(m, S).map A) ∗ N(b, R) = N(A m + b, A S Aᵀ + R)`. -/
theorem multivariateGaussian_map_conv {S R : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hR : R.PosSemidef) (A : Matrix ι ι ℝ) (m b : EuclideanSpace ℝ ι) :
    ((multivariateGaussian m S).map (euclid A)) ∗ multivariateGaussian b R =
      multivariateGaussian (euclid A m + b) (A * S * Aᵀ + R) := by
  rw [multivariateGaussian_map_euclid hS A m, multivariateGaussian_conv (posSemidef_conj hS A) hR]

/-! ### Invariance -/

/-- A centred Gaussian whose covariance is a fixed point of the covariance step is invariant
under the affine Gaussian step. -/
theorem invariant_of_covStep_fixed {S R : Matrix ι ι ℝ} (hS : S.PosSemidef) (hR : R.PosSemidef)
    (A : Matrix ι ι ℝ) (hfix : covStep A R S = S) :
    ((multivariateGaussian 0 S).map (euclid A)) ∗ multivariateGaussian 0 R =
      multivariateGaussian 0 S := by
  rw [multivariateGaussian_map_conv hS hR A 0 0, map_zero, zero_add]
  exact congrArg _ hfix

/-- **Invariance of `N(0, Σ_ULA)` under the ULA step** `w ↦ (I - hP) w + √(2h) ξ`. -/
theorem ulaCov_invariant {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) :
    ((multivariateGaussian 0 (ulaCov P h)).map (euclid (ulaStep P h))) ∗
        multivariateGaussian (0 : EuclideanSpace ℝ ι) ((2 * h) • (1 : Matrix ι ι ℝ)) =
      multivariateGaussian 0 (ulaCov P h) := by
  have hPt : Pᵀ = P := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hev' : ∀ i, 0 < hP.1.eigenvalues i ∧ h * hP.1.eigenvalues i < 2 :=
    fun i => ⟨hP.eigenvalues_pos i, hev i⟩
  exact invariant_of_covStep_fixed (ulaCov_posDef hP h hh hev).posSemidef
    (Matrix.PosSemidef.one.smul (by positivity)) (ulaStep P h)
    (ulaCov_fixed P h hPt (isUnit_det_ulaDenom hP.1 h hev'))

/-! ### The finite-time marginal law -/

/-- One affine Gaussian step on laws: push forward by `A`, then add independent `N(0, R)` noise. -/
noncomputable def gaussStep (A R : Matrix ι ι ℝ) (μ : Measure (EuclideanSpace ℝ ι)) :
    Measure (EuclideanSpace ℝ ι) :=
  (μ.map (euclid A)) ∗ multivariateGaussian 0 R

/-- **Finite-time marginal law.** Starting from `N(m₀, S₀)`, after `k` steps the law is
`N(A^k m₀, Σ_k)` with `Σ_k` the `k`-th iterate of the covariance step. -/
theorem gaussStep_iterate {S₀ R : Matrix ι ι ℝ} (hS : S₀.PosSemidef) (hR : R.PosSemidef)
    (A : Matrix ι ι ℝ) (m₀ : EuclideanSpace ℝ ι) (k : ℕ) :
    (gaussStep A R)^[k] (multivariateGaussian m₀ S₀) =
      multivariateGaussian (euclid (A ^ k) m₀) ((covStep A R)^[k] S₀) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, gaussStep,
      multivariateGaussian_map_conv (covStep_iterate_posSemidef hS hR A k) hR, add_zero,
      Function.iterate_succ_apply', pow_succ', euclid_mul, mul_apply_eq_comp]
    rfl

/-- **From the mode.** If `S` is a fixed point of the covariance step, the law after `k` steps
from a point mass at the mode is `N(0, S - A^k S (Aᵀ)^k)`. -/
theorem gaussStep_iterate_zero {S R : Matrix ι ι ℝ} (hR : R.PosSemidef) (A : Matrix ι ι ℝ)
    (hS : covStep A R S = S) (k : ℕ) :
    (gaussStep A R)^[k] (multivariateGaussian 0 0) =
      multivariateGaussian 0 (S - A ^ k * S * (Aᵀ) ^ k) := by
  rw [gaussStep_iterate Matrix.PosSemidef.zero hR A 0 k, map_zero,
    covStep_iterate_zero A R S hS k]

end Laplace.Sampler
