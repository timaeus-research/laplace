/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.TwoD.ValleyQuadratic
import Laplace.Multi.OneLoop

/-!
# E5: where the Laplace error of the Rosenbrock valley hides

Exact corollaries of the closed-form covariance `rosenCov a t = (tH)⁻¹ + (2/t²) e_y e_yᵀ` of the
2D Rosenbrock valley `L = (a (y - x²)² + (1 - x)²)/2`:

* along the valley-normal direction `w = (2, -1)` (the stiff eigenvector of the Hessian up to an
  `O(1)` remainder, `rosenHess_mulVec_stiff`) the exact variance exceeds the Laplace one by the
  factor `1 + 2a/t` (`rosenCov_stiff`, `rosenCov_stiff_ratio`; `6/5` at `a = 100`, `t = 1000`,
  `rosenCov_stiff_ratio_100_1000`): the note's "wrong along the stiff direction by a factor
  `1 + 200/t`, 20% at `t = 1000`";
* along the flat direction `f = (1, 2)` the factor is `1 + 8/(t(25 + 4/a))` (`rosenCov_flat_ratio`);
* the squared Frobenius error is `4/t⁴` against `‖(tH)⁻¹‖_F² = (9 + (4 + 1/a)²)/t²`
  (`rosenCov_frobenius_sq`, `laplace_frobenius_sq`): "the whole-covariance Frobenius norm
  hides this because flat directions dominate it";
* the exact LLC is `1` at every `t` (`rosenbrock_llc`).
-/

open Matrix Laplace.Multi

namespace Laplace.TwoD

/-! ### The stiff and flat directions -/

/-- `(2, -1)` is the stiff eigenvector of the Rosenbrock Hessian up to `O(1)`:
`H w = 5a • w + (2, 0)`. -/
theorem rosenHess_mulVec_stiff (a : ℝ) :
    rosenHess a *ᵥ ![2, -1] = (5 * a) • ![2, -1] + ![2, 0] := by
  ext i
  fin_cases i <;> simp [rosenHess, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The Laplace variance along the stiff direction: `wᵀ (tH)⁻¹ w = 1/(a t)`. -/
theorem laplace_stiff {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ![2, -1] ⬝ᵥ (t • rosenHess a)⁻¹ *ᵥ ![2, -1] = 1 / (a * t) := by
  rw [rosenHess_smul_inv ha ht]
  simp [rosenSigma, mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

/-- **The exact variance along the stiff direction**: `wᵀ Cov w = 1/(a t) + 2/t²`. -/
theorem rosenCov_stiff {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ![2, -1] ⬝ᵥ rosenCov a t *ᵥ ![2, -1] = 1 / (a * t) + 2 / t ^ 2 := by
  rw [rosenCov_eq_laplace_add ha ht, rosenHess_smul_inv ha ht]
  simp [rosenSigma, mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

/-- **The stiff-direction factor `1 + 2a/t`**: the exact variance along `w = (2, -1)` is
`(1 + 2a/t)` times the Laplace variance; at `a = 100` this is the note's `1 + 200/t`. -/
theorem rosenCov_stiff_ratio {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ![2, -1] ⬝ᵥ rosenCov a t *ᵥ ![2, -1] =
      (1 + 2 * a / t) * (![2, -1] ⬝ᵥ (t • rosenHess a)⁻¹ *ᵥ ![2, -1]) := by
  rw [rosenCov_stiff ha ht, laplace_stiff ha ht]
  field_simp

/-- **At `a = 100`, `t = 1000` the stiff-direction variance is `6/5` of the Laplace value**
(20% high). -/
theorem rosenCov_stiff_ratio_100_1000 :
    ![2, -1] ⬝ᵥ rosenCov 100 1000 *ᵥ ![2, -1] =
      6 / 5 * (![2, -1] ⬝ᵥ ((1000 : ℝ) • rosenHess (100 : ℝ))⁻¹ *ᵥ ![2, -1]) := by
  rw [rosenCov_stiff (by norm_num) (by norm_num), laplace_stiff (by norm_num) (by norm_num)]
  norm_num

/-- At `a = 100`, `t = 10⁴` the factor is `51/50` (2% high). -/
theorem rosenCov_stiff_ratio_100_10000 :
    ![2, -1] ⬝ᵥ rosenCov 100 10000 *ᵥ ![2, -1] =
      51 / 50 * (![2, -1] ⬝ᵥ ((10000 : ℝ) • rosenHess (100 : ℝ))⁻¹ *ᵥ ![2, -1]) := by
  rw [rosenCov_stiff (by norm_num) (by norm_num), laplace_stiff (by norm_num) (by norm_num)]
  norm_num

/-- The Laplace variance along the flat direction `f = (1, 2)`: `fᵀ (tH)⁻¹ f = (25 + 4/a)/t`. -/
theorem laplace_flat {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ![1, 2] ⬝ᵥ (t • rosenHess a)⁻¹ *ᵥ ![1, 2] = (25 + 4 / a) / t := by
  rw [rosenHess_smul_inv ha ht]
  simp [rosenSigma, mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

/-- **The flat direction is barely affected**: the exact-to-Laplace factor along `f = (1, 2)` is
`1 + 8/(t(25 + 4/a))`. -/
theorem rosenCov_flat_ratio {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ![1, 2] ⬝ᵥ rosenCov a t *ᵥ ![1, 2] =
      (1 + 8 / (t * (25 + 4 / a))) * (![1, 2] ⬝ᵥ (t • rosenHess a)⁻¹ *ᵥ ![1, 2]) := by
  rw [laplace_flat ha ht, rosenCov_eq_laplace_add ha ht, rosenHess_smul_inv ha ht]
  simp [rosenSigma, mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

/-! ### The Frobenius norm hides the stiff-direction error -/

/-- The squared Frobenius error of the Laplace covariance: `∑ᵢⱼ (Cov - (tH)⁻¹)ᵢⱼ² = 4/t⁴`. -/
theorem rosenCov_frobenius_sq {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ∑ i, ∑ j, (rosenCov a t - (t • rosenHess a)⁻¹) i j ^ 2 = 4 / t ^ 4 := by
  rw [rosenCov_eq_laplace_add ha ht]
  simp [Fin.sum_univ_two]
  ring

/-- The squared Frobenius norm of the Laplace covariance:
`∑ᵢⱼ ((tH)⁻¹)ᵢⱼ² = (9 + (4 + 1/a)²)/t²`. -/
theorem laplace_frobenius_sq {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ∑ i, ∑ j, ((t • rosenHess a)⁻¹) i j ^ 2 = (9 + (4 + 1 / a) ^ 2) / t ^ 2 := by
  rw [rosenHess_smul_inv ha ht]
  simp [rosenSigma, Fin.sum_univ_two]
  field_simp
  ring

/-- **The relative squared Frobenius error** of the Laplace covariance is `4/(t² (9 + (4 + 1/a)²))`,
about `(0.4/t)²` at `a = 100`, against the factor `1 + 200/t` along the stiff direction. -/
theorem rosenCov_frobenius_rel {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (∑ i, ∑ j, (rosenCov a t - (t • rosenHess a)⁻¹) i j ^ 2) /
      ∑ i, ∑ j, ((t • rosenHess a)⁻¹) i j ^ 2 = 4 / (t ^ 2 * (9 + (4 + 1 / a) ^ 2)) := by
  rw [rosenCov_frobenius_sq ha ht, laplace_frobenius_sq ha ht]
  have h9 : (0 : ℝ) < 9 + (4 + 1 / a) ^ 2 := by positivity
  field_simp

/-! ### The exact LLC -/

/-- **The exact LLC of the Rosenbrock valley is `1 = d/2`** at every temperature, although the
Laplace covariance is off by `1 + 2a/t` along the stiff direction: Morse but not
Laplace-accurate. -/
theorem rosenbrock_llc {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t * gibbsExpectation (rosenbrock a) t (rosenbrock a) = 1 := by
  rw [rosenbrock_eq_quadValley, gibbsExpectation_quadValley_self ha ht]
  field_simp

end Laplace.TwoD
