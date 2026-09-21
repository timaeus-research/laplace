/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Sampler.GaussianInvariance

/-!
# SGD fluctuations measure sharpness

The algebra of Proposition 12.2 of the working note *Patterning flow*. For the
Ornstein–Uhlenbeck model of SGD near a minimiser, the stationary covariance `Σ` solves the
continuous Lyapunov equation `H Σ + Σ H = (η/B) C`; taking the trace gives the stationary
excess loss `E[K] = ½ tr(H Σ) = (η/4B) tr C`. When `C = c H` the isotropic matrix
`(ηc/2B) I` solves the equation. The discrete recursion `Σ = (1 - ηH) Σ (1 - ηH) + (η²/B) C`
in an eigenbasis of `H` has the unique stable fixed point with diagonal entries
`ηc/(B(2 - ηλ_i))`.

These are identities for the covariance equations; that an SDE or the SGD chain has this
stationary covariance is not part of the statements.
-/

namespace Laplace.Patterning

open Matrix Laplace.Sampler MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-- The stationary excess loss `E[K] = ½ tr(H Σ)` of a quadratic loss under covariance `Σ`. -/
def excessLoss (H S : Matrix ι ι ℝ) : ℝ := (1 / 2) * (H * S).trace

/-- **Trace of the Lyapunov equation.** `H Σ + Σ H = (η/B) C` implies
`tr(H Σ) = (η/2B) tr C`; no symmetry or invertibility is needed. -/
theorem trace_mul_of_lyapunov (H S C : Matrix ι ι ℝ) (η B : ℝ)
    (h : H * S + S * H = (η / B) • C) :
    (H * S).trace = (η / (2 * B)) * C.trace := by
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_mul_comm S H, smul_eq_mul] at ht
  rw [show η / (2 * B) = (η / B) / 2 by ring]
  linarith

/-- `E[K] = (η/4B) tr C` under the Lyapunov equation. -/
theorem excessLoss_of_lyapunov (H S C : Matrix ι ι ℝ) (η B : ℝ)
    (h : H * S + S * H = (η / B) • C) :
    excessLoss H S = (η / (4 * B)) * C.trace := by
  unfold excessLoss
  rw [trace_mul_of_lyapunov H S C η B h]
  ring

/-- **The isotropic solution.** When `C = c H`, `Σ = (ηc/2B) I` solves the Lyapunov equation. -/
theorem lyapunov_isotropic (H : Matrix ι ι ℝ) (η B c : ℝ) :
    H * ((η * c / (2 * B)) • (1 : Matrix ι ι ℝ)) + ((η * c / (2 * B)) • (1 : Matrix ι ι ℝ)) * H
      = (η / B) • (c • H) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul]
  rw [← add_smul]
  congr 1
  ring

/-- With `C = c H` the excess loss is the sharpness `(ηc/4B) tr H`. -/
theorem excessLoss_isotropic (H : Matrix ι ι ℝ) (η B c : ℝ) :
    excessLoss H ((η * c / (2 * B)) • (1 : Matrix ι ι ℝ)) = (η * c / (4 * B)) * H.trace := by
  unfold excessLoss
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  ring

/-! ### The discrete recursion in an eigenbasis -/

/-- The SGD step matrix `1 - η diag(λ)` as a diagonal matrix. -/
lemma one_sub_smul_diagonal (η : ℝ) (lam : ι → ℝ) :
    (1 : Matrix ι ι ℝ) - η • diagonal lam = diagonal (fun i => 1 - η * lam i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]

/-- **Discrete SGD law.** With `C = c diag(λ)` and `|1 - ηλ_i| < 1`, the fixed point of
`Σ ↦ (1 - ηH) Σ (1 - ηH) + (η²/B) C` is `diagLyapunov`, whose diagonal entries are
`ηc/(B(2 - ηλ_i))`. -/
theorem sgd_discrete_fixed_iff (lam : ι → ℝ) (η B c : ℝ)
    (hstab : ∀ i, |1 - η * lam i| < 1) (X : Matrix ι ι ℝ) :
    covStep (1 - η • diagonal lam) ((η ^ 2 / B) • (c • diagonal lam)) X = X ↔
      X = diagLyapunov (fun i => 1 - η * lam i) ((η ^ 2 / B) • (c • diagonal lam)) := by
  rw [one_sub_smul_diagonal]
  exact covStep_diagonal_fixed_iff _ hstab _ X

theorem sgd_discrete_diag (lam : ι → ℝ) (η B c : ℝ) (hB : 0 < B)
    (hstab : ∀ i, |1 - η * lam i| < 1) (i : ι) :
    diagLyapunov (fun i => 1 - η * lam i) ((η ^ 2 / B) • (c • diagonal lam)) i i
      = η * c / (B * (2 - η * lam i)) := by
  simp only [diagLyapunov, Matrix.of_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
    smul_eq_mul]
  have h := abs_lt.mp (hstab i)
  have h0 : 0 < η * lam i := by linarith
  have h2 : η * lam i < 2 := by linarith
  have hden : 1 - (1 - η * lam i) * (1 - η * lam i) ≠ 0 := by nlinarith
  have hden' : B * (2 - η * lam i) ≠ 0 := mul_ne_zero hB.ne' (by linarith)
  rw [div_eq_div_iff hden hden']
  field_simp
  ring

/-- The discrete stationary excess loss: `E[K] = ½ ∑ λ_i · ηc/(B(2 - ηλ_i))`. -/
theorem sgd_discrete_excessLoss (lam : ι → ℝ) (η B c : ℝ) (hB : 0 < B)
    (hstab : ∀ i, |1 - η * lam i| < 1) :
    excessLoss (diagonal lam)
        (diagLyapunov (fun i => 1 - η * lam i) ((η ^ 2 / B) • (c • diagonal lam)))
      = (1 / 2) * ∑ i, lam i * (η * c / (B * (2 - η * lam i))) := by
  unfold excessLoss
  congr 1
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul, sgd_discrete_diag lam η B c hB hstab i]

/-- The exact remainder behind `E[K] = (ηc/4B) tr H + (η²c/8B) tr H² + O(η³)`: per mode,
`ηcλ/(B(2 - ηλ)) = ηcλ/(2B) + η²cλ²/(4B) + η³cλ³/(4B(2 - ηλ))`. -/
theorem sgd_discrete_mode_expansion (lam η B c : ℝ) (hB : B ≠ 0) (h2 : η * lam ≠ 2) :
    lam * (η * c / (B * (2 - η * lam)))
      = η * c * lam / (2 * B) + η ^ 2 * c * lam ^ 2 / (4 * B)
        + η ^ 3 * c * lam ^ 3 / (4 * B * (2 - η * lam)) := by
  have h2' : 2 - η * lam ≠ 0 := sub_ne_zero.mpr (Ne.symm h2)
  have h2'' : 2 - lam * η ≠ 0 := by rwa [mul_comm]
  field_simp
  ring


/-! ### The stationary law of the linearised SGD chain with Gaussian noise -/

/-- The discrete SGD fixed point is the diagonal matrix with entries `ηc/(B(2 - ηλ_i))`. -/
theorem sgd_discrete_diagLyapunov_eq_diagonal (lam : ι → ℝ) (η B c : ℝ) (hB : 0 < B)
    (hstab : ∀ i, |1 - η * lam i| < 1) :
    diagLyapunov (fun i => 1 - η * lam i) ((η ^ 2 / B) • (c • diagonal lam))
      = diagonal (fun i => η * c / (B * (2 - η * lam i))) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [sgd_discrete_diag lam η B c hB hstab i, Matrix.diagonal_apply_eq]
  · simp [diagLyapunov, Matrix.diagonal_apply_ne _ hij]

/-- **The stationary Gaussian law of linearised SGD** (Proposition 12.2, discrete form): with
Gaussian minibatch noise `ξ ~ N(0, (η²c/B) diag λ)`, the centred Gaussian with covariance
`diag(ηc/(B(2 - ηλ_i)))` is invariant under the step `w ↦ (1 - η diag λ) w + ξ`. -/
theorem sgd_gaussian_invariant (lam : ι → ℝ) (η B c : ℝ) (hη : 0 < η) (hB : 0 < B) (hc : 0 ≤ c)
    (hstab : ∀ i, |1 - η * lam i| < 1) :
    ((multivariateGaussian 0 (diagonal (fun i => η * c / (B * (2 - η * lam i))))).map
        (euclid (1 - η • diagonal lam))) ∗
      multivariateGaussian (0 : EuclideanSpace ℝ ι) ((η ^ 2 / B) • (c • diagonal lam))
      = multivariateGaussian 0 (diagonal (fun i => η * c / (B * (2 - η * lam i)))) := by
  have hlam : ∀ i, 0 < lam i := by
    intro i
    have h := abs_lt.mp (hstab i)
    have : 0 < η * lam i := by linarith
    exact (pos_iff_pos_of_mul_pos this).mp hη
  have hS : (diagonal (fun i => η * c / (B * (2 - η * lam i)))).PosSemidef := by
    refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
    have h := abs_lt.mp (hstab i)
    exact div_nonneg (mul_nonneg hη.le hc) (mul_nonneg hB.le (by linarith))
  have hR : ((η ^ 2 / B) • (c • diagonal lam)).PosSemidef := by
    rw [← Matrix.diagonal_smul, ← Matrix.diagonal_smul]
    refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (mul_nonneg hc (hlam i).le)
  refine invariant_of_covStep_fixed hS hR _ ?_
  rw [← sgd_discrete_diagLyapunov_eq_diagonal lam η B c hB hstab]
  exact (sgd_discrete_fixed_iff lam η B c hstab _).mpr rfl

end

end Laplace.Patterning
