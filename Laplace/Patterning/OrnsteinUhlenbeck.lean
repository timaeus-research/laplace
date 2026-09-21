/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.SGDLyapunov

/-!
# The Ornstein–Uhlenbeck model of SGD as a Gaussian semigroup

Proposition 12.2 of the working note *Patterning flow* models SGD near a minimiser by the
Ornstein–Uhlenbeck diffusion `dw = -Hw ds + √(η/B) C^{1/2} dW_s` and reads off its stationary
covariance from the Lyapunov equation `HΣ + ΣH = (η/B) C`. Mathlib has no stochastic
integration, so the diffusion is represented here by what defines it as a Gaussian Markov
process: its transition semigroup. Writing `E_s = e^{-sH}` and `D = (η/B) C`, the law at time `s`
started from `w` is `N(E_s w, Σ_s)` with `Σ_s = Σ - E_s Σ E_s`, where `Σ` solves the Lyapunov
equation. We prove, for symmetric `H` and positive semidefinite `D`:

* `hasDerivAt_ouCov`, `hasDerivAt_ouCov'`: `Σ_s` solves the Lyapunov ODE
  `Σ_s' = E_s D E_s = D - HΣ_s - Σ_s H` with `Σ_0 = 0` (the covariance equation of the OU process);
* `ouCov_semigroup`, `ouStep_semigroup`: the kernels `N(E_s w, Σ_s)` form a semigroup,
  `Σ_{s+t} = E_s Σ_t E_s + Σ_s`;
* `ouCov_posSemidef`: `Σ_s ⪰ 0` for `s ≥ 0` (the quadratic form is nondecreasing in `s`);
* `ouStep_invariant`: **the centred Gaussian with covariance `Σ` is invariant** under every
  `ouStep s`: the stationary law of the OU semigroup has the Lyapunov covariance;
* `ouStep_from_mode`: started at the minimiser the law at time `s` is `N(0, Σ_s)`;
* `ouFlow_tendsto_zero`, `ouCov_tendsto`, `lyapunov_posSemidef`: for positive definite `H`,
  `E_s → 0`, `Σ_s → Σ`, and `Σ ⪰ 0`.

The identification of this semigroup with the Itô SDE is the textbook definition of the OU
process and is not formalised. The matrix exponential is Mathlib's `NormedSpace.exp` with the
`L∞`-operator norm enabled locally, as in `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`.
-/

namespace Laplace.Patterning

open Matrix NormedSpace MeasureTheory ProbabilityTheory Laplace.Sampler Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-! ### The flow `e^{-sH}` -/

/-- The deterministic flow `E_s = e^{-sH}`. -/
def ouFlow (H : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ := exp (s • (-H))

theorem ouFlow_zero (H : Matrix ι ι ℝ) : ouFlow H 0 = 1 := by
  simp [ouFlow]

theorem ouFlow_add (H : Matrix ι ι ℝ) (s t : ℝ) :
    ouFlow H (s + t) = ouFlow H s * ouFlow H t := by
  unfold ouFlow
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (-H)).smul_left s).smul_right t)

theorem ouFlow_mul_comm (H : Matrix ι ι ℝ) (s t : ℝ) :
    ouFlow H s * ouFlow H t = ouFlow H t * ouFlow H s := by
  rw [← ouFlow_add, add_comm, ouFlow_add]

theorem ouFlow_transpose (H : Matrix ι ι ℝ) (hH : Hᵀ = H) (s : ℝ) :
    (ouFlow H s)ᵀ = ouFlow H s := by
  unfold ouFlow
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, Matrix.transpose_neg, hH]

theorem ouFlow_comm (H : Matrix ι ι ℝ) (s : ℝ) : H * ouFlow H s = ouFlow H s * H := by
  unfold ouFlow
  exact (((Commute.refl H).neg_right).smul_right s).exp_right

/-! ### The covariance path `Σ_s = Σ - E_s Σ E_s` -/

/-- The covariance at time `s` of the OU process started at the minimiser, `Σ_s = Σ - E_s Σ E_s`,
for `Σ` the Lyapunov solution. -/
def ouCov (H S : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ := S - ouFlow H s * S * ouFlow H s

theorem ouCov_zero (H S : Matrix ι ι ℝ) : ouCov H S 0 = 0 := by
  simp [ouCov, ouFlow_zero]

/-- `Σ_{s+t} = E_s Σ_t E_s + Σ_s`: the semigroup identity of the covariances. -/
theorem ouCov_semigroup (H S : Matrix ι ι ℝ) (s t : ℝ) :
    ouCov H S (s + t) = ouFlow H s * ouCov H S t * ouFlow H s + ouCov H S s := by
  unfold ouCov
  rw [ouFlow_add]
  have h : ouFlow H s * ouFlow H t * S * (ouFlow H s * ouFlow H t)
      = ouFlow H s * ouFlow H t * S * (ouFlow H t * ouFlow H s) := by
    rw [ouFlow_mul_comm H s t]
  rw [h]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-! ### Relaxation of the flow for positive definite `H` (spectral form) -/

/-- `E_s = U diag(e^{-sλ_i}) Uᵀ` in an orthonormal eigenbasis of the symmetric matrix `H`. -/
theorem ouFlow_eq_spectral {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (s : ℝ) :
    ouFlow H s = orthoOf hH * diagonal (fun i => Real.exp (-(s * hH.eigenvalues i))) *
      (orthoOf hH)ᵀ := by
  have hU := orthoOf_transpose_mul hH
  have hU' := orthoOf_mul_transpose hH
  have hUinv : (orthoOf hH)⁻¹ = (orthoOf hH)ᵀ := Matrix.inv_eq_left_inv hU
  have hunit : IsUnit (orthoOf hH) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_det_of_right_inverse hU'
  have hconj : s • -H = orthoOf hH * diagonal (fun i => s * -hH.eigenvalues i) * (orthoOf hH)⁻¹ := by
    conv_lhs => rw [spectral_real hH]
    rw [hUinv]
    have hd : diagonal (fun i => s * -hH.eigenvalues i) = s • -(diagonal hH.eigenvalues) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hd]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg,
      Matrix.mul_assoc]
  unfold ouFlow
  rw [hconj, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, hUinv]
  congr 3
  funext i
  rw [Pi.exp_def, ← Real.exp_eq_exp_ℝ]
  simp only [mul_neg]

/-- **The flow relaxes**: `E_s → 0` as `s → ∞` for positive definite `H`. -/
theorem ouFlow_tendsto_zero {H : Matrix ι ι ℝ} (hH : H.PosDef) :
    Tendsto (ouFlow H) atTop (𝓝 0) := by
  have hfun : ouFlow H = fun s => orthoOf hH.1 * diagonal (fun i => Real.exp (-(s * hH.1.eigenvalues i)))
      * (orthoOf hH.1)ᵀ := funext fun s => ouFlow_eq_spectral hH.1 s
  rw [hfun]
  have hdiag : Tendsto (fun s : ℝ => (fun i => Real.exp (-(s * hH.1.eigenvalues i)) : ι → ℝ)) atTop
      (𝓝 0) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    have hpos := hH.eigenvalues_pos i
    have h1 : Tendsto (fun s : ℝ => s * hH.1.eigenvalues i) atTop atTop :=
      Tendsto.atTop_mul_const hpos tendsto_id
    simpa using h1
  have hcont : Continuous fun v : ι → ℝ => orthoOf hH.1 * diagonal v * (orthoOf hH.1)ᵀ :=
    (continuous_const.matrix_mul continuous_id.matrix_diagonal).matrix_mul continuous_const
  have h3 := (hcont.tendsto 0).comp hdiag
  have h0 : diagonal (0 : ι → ℝ) = (0 : Matrix ι ι ℝ) := Matrix.diagonal_zero
  simp only [Function.comp_def, h0, Matrix.mul_zero, Matrix.zero_mul] at h3
  exact h3

/-- **Relaxation of the covariance**: `Σ_s → Σ` as `s → ∞` for positive definite `H`. -/
theorem ouCov_tendsto {H : Matrix ι ι ℝ} (hH : H.PosDef) (S : Matrix ι ι ℝ) :
    Tendsto (ouCov H S) atTop (𝓝 S) := by
  unfold ouCov
  have h := ouFlow_tendsto_zero hH
  have h2 : Tendsto (fun s => ouFlow H s * S * ouFlow H s) atTop (𝓝 (0 * S * 0)) :=
    (h.mul (tendsto_const_nhds (x := S))).mul h
  have := (tendsto_const_nhds (x := S)).sub h2
  simpa using this

/-- The quadratic form along the covariance path converges to that of `Σ`. -/
theorem quadForm_ouCov_tendsto {H : Matrix ι ι ℝ} (hH : H.PosDef) (S : Matrix ι ι ℝ)
    (x : ι → ℝ) :
    Tendsto (fun s => x ⬝ᵥ (ouCov H S s *ᵥ x)) atTop (𝓝 (x ⬝ᵥ (S *ᵥ x))) := by
  have hcont : Continuous fun M : Matrix ι ι ℝ => x ⬝ᵥ (M *ᵥ x) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact (hcont.tendsto S).comp (ouCov_tendsto hH S)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_ouFlow (H : Matrix ι ι ℝ) (s : ℝ) :
    HasDerivAt (ouFlow H) (-H * ouFlow H s) s := by
  unfold ouFlow
  exact hasDerivAt_exp_smul_const' (-H) s

/-- **The Lyapunov ODE, flow form.** If `HΣ + ΣH = D` then `Σ_s' = E_s D E_s`. -/
theorem hasDerivAt_ouCov (H S D : Matrix ι ι ℝ) (hLyap : H * S + S * H = D) (s : ℝ) :
    HasDerivAt (ouCov H S) (ouFlow H s * D * ouFlow H s) s := by
  unfold ouCov
  have h := ((hasDerivAt_ouFlow H s).mul (hasDerivAt_const s S)).mul (hasDerivAt_ouFlow H s)
  refine ((hasDerivAt_const s S).sub h).congr_deriv ?_
  change (0 : Matrix ι ι ℝ) - ((-H * ouFlow H s * S + ouFlow H s * 0) * ouFlow H s
      + ouFlow H s * S * (-H * ouFlow H s)) = ouFlow H s * D * ouFlow H s
  have e1 : (0 : Matrix ι ι ℝ) - ((-H * ouFlow H s * S + ouFlow H s * 0) * ouFlow H s
      + ouFlow H s * S * (-H * ouFlow H s))
      = H * ouFlow H s * S * ouFlow H s + ouFlow H s * S * H * ouFlow H s := by
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_zero, add_zero, Matrix.mul_assoc]
    abel
  rw [e1, ouFlow_comm, ← hLyap]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- **The Lyapunov ODE.** `Σ_s' = D - HΣ_s - Σ_s H`. -/
theorem hasDerivAt_ouCov' (H S D : Matrix ι ι ℝ) (hLyap : H * S + S * H = D) (s : ℝ) :
    HasDerivAt (ouCov H S) (D - H * ouCov H S s - ouCov H S s * H) s := by
  refine (hasDerivAt_ouCov H S D hLyap s).congr_deriv ?_
  unfold ouCov
  rw [← hLyap]
  have h1 : H * ouFlow H s * S * ouFlow H s = ouFlow H s * H * S * ouFlow H s := by
    rw [ouFlow_comm]
  have h2 : ouFlow H s * S * ouFlow H s * H = ouFlow H s * S * H * ouFlow H s := by
    rw [Matrix.mul_assoc, ← ouFlow_comm, ← Matrix.mul_assoc]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc] at h1 h2 ⊢
  rw [← h1, ← h2]
  abel

/-! ### Positivity of the covariance path -/

/-- The quadratic form of a differentiable matrix path is differentiable. -/
theorem hasDerivAt_quadForm_path {M : ℝ → Matrix ι ι ℝ} {M' : Matrix ι ι ℝ} {s : ℝ}
    (h : HasDerivAt M M' s) (x : ι → ℝ) :
    HasDerivAt (fun s => x ⬝ᵥ (M s *ᵥ x)) (x ⬝ᵥ (M' *ᵥ x)) s := by
  let L : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => x ⬝ᵥ (A *ᵥ x)
      map_add' := fun A B => by simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := fun c A => by simp [Matrix.smul_mulVec, dotProduct_smul] }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt s h

/-- `x ⬝ᵥ (E D E x) = (E x) ⬝ᵥ (D (E x)) ≥ 0` for symmetric `E` and `D ⪰ 0`. -/
theorem quadForm_conj_nonneg {D E : Matrix ι ι ℝ} (hD : D.PosSemidef) (hE : Eᵀ = E)
    (x : ι → ℝ) : 0 ≤ x ⬝ᵥ ((E * D * E) *ᵥ x) := by
  have h := hD.dotProduct_mulVec_nonneg (E *ᵥ x)
  rw [star_trivial] at h
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hE]
  exact h

/-- **`Σ_s ⪰ 0` for `s ≥ 0`.** -/
theorem ouCov_posSemidef (H S D : Matrix ι ι ℝ) (hH : Hᵀ = H) (hS : Sᵀ = S)
    (hLyap : H * S + S * H = D) (hD : D.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    (ouCov H S s).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · change (ouCov H S s)ᴴ = ouCov H S s
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    unfold ouCov
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, ouFlow_transpose H hH,
      hS, Matrix.mul_assoc]
  · rw [star_trivial]
    have hf : ∀ u, HasDerivAt (fun u => x ⬝ᵥ (ouCov H S u *ᵥ x))
        (x ⬝ᵥ ((ouFlow H u * D * ouFlow H u) *ᵥ x)) u :=
      fun u => hasDerivAt_quadForm_path (hasDerivAt_ouCov H S D hLyap u) x
    have hmono : Monotone fun u => x ⬝ᵥ (ouCov H S u *ᵥ x) := by
      refine monotone_of_deriv_nonneg (fun u => (hf u).differentiableAt) fun u => ?_
      rw [(hf u).deriv]
      exact quadForm_conj_nonneg hD (ouFlow_transpose H hH u) x
    have h0 : x ⬝ᵥ (ouCov H S 0 *ᵥ x) = 0 := by simp [ouCov_zero]
    have := hmono hs
    simp only [h0] at this
    exact this

/-! ### The Gaussian transition semigroup -/

/-- One OU transition on laws: push forward by `E_s`, then add independent `N(0, Σ_s)` noise. -/
def ouStep (H S : Matrix ι ι ℝ) (s : ℝ) (μ : Measure (EuclideanSpace ℝ ι)) :
    Measure (EuclideanSpace ℝ ι) :=
  (μ.map (euclid (ouFlow H s))) ∗ multivariateGaussian 0 (ouCov H S s)

/-- **Gaussian in, Gaussian out.** `ouStep s (N(m, R)) = N(E_s m, E_s R E_s + Σ_s)`. -/
theorem ouStep_gaussian (H S : Matrix ι ι ℝ) (hH : Hᵀ = H) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) {s : ℝ} (hcov : (ouCov H S s).PosSemidef) (m : EuclideanSpace ℝ ι) :
    ouStep H S s (multivariateGaussian m R)
      = multivariateGaussian (euclid (ouFlow H s) m)
          (ouFlow H s * R * ouFlow H s + ouCov H S s) := by
  unfold ouStep
  rw [multivariateGaussian_map_conv hR hcov, add_zero, ouFlow_transpose H hH]

/-- **Invariance of `N(0, Σ)`**: the Gaussian with the Lyapunov covariance is stationary for
the OU semigroup. -/
theorem ouStep_invariant (H S : Matrix ι ι ℝ) (hH : Hᵀ = H) (hS : S.PosSemidef) {s : ℝ}
    (hcov : (ouCov H S s).PosSemidef) :
    ouStep H S s (multivariateGaussian 0 S) = multivariateGaussian 0 S := by
  rw [ouStep_gaussian H S hH hS hcov, map_zero]
  congr 1
  unfold ouCov
  abel

/-- **From the minimiser.** Started at the point mass at `0`, the law at time `s` is `N(0, Σ_s)`. -/
theorem ouStep_from_mode (H S : Matrix ι ι ℝ) (hH : Hᵀ = H) {s : ℝ}
    (hcov : (ouCov H S s).PosSemidef) :
    ouStep H S s (multivariateGaussian 0 0) = multivariateGaussian 0 (ouCov H S s) := by
  rw [ouStep_gaussian H S hH Matrix.PosSemidef.zero hcov, map_zero]
  simp

/-- **The semigroup property** on Gaussian laws: `ouStep s ∘ ouStep t = ouStep (s + t)`. -/
theorem ouStep_semigroup (H S : Matrix ι ι ℝ) (hH : Hᵀ = H) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) {s t : ℝ} (hcs : (ouCov H S s).PosSemidef)
    (hct : (ouCov H S t).PosSemidef) (hcst : (ouCov H S (s + t)).PosSemidef)
    (m : EuclideanSpace ℝ ι) :
    ouStep H S s (ouStep H S t (multivariateGaussian m R))
      = ouStep H S (s + t) (multivariateGaussian m R) := by
  have hRt : (ouFlow H t * R * ouFlow H t).PosSemidef := by
    have := posSemidef_conj hR (ouFlow H t)
    rwa [ouFlow_transpose H hH] at this
  rw [ouStep_gaussian H S hH hR hct, ouStep_gaussian H S hH hR hcst,
    ouStep_gaussian H S hH (hRt.add hct) hcs]
  congr 1
  · rw [ouFlow_add, euclid_mul]
    rfl
  · rw [ouCov_semigroup, ouFlow_add]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [ouFlow_mul_comm H t s]
    abel

/-- **Proposition 12.2 in the note's parameters.** With `D = (η/B) C` and `HΣ + ΣH = (η/B) C`,
the Gaussian `N(0, Σ)` is invariant under the OU semigroup, and the stationary excess loss is
`½ tr(HΣ) = (η/4B) tr C`. -/
theorem ou_sgd_stationary (H S C : Matrix ι ι ℝ) (η B : ℝ) (hH : Hᵀ = H) (hSt : Sᵀ = S)
    (hS : S.PosSemidef) (hC : ((η / B) • C).PosSemidef) (hLyap : H * S + S * H = (η / B) • C)
    {s : ℝ} (hs : 0 ≤ s) :
    ouStep H S s (multivariateGaussian 0 S) = multivariateGaussian 0 S ∧
      excessLoss H S = (η / (4 * B)) * C.trace :=
  ⟨ouStep_invariant H S hH hS (ouCov_posSemidef H S _ hH hSt hLyap hC hs),
    excessLoss_of_lyapunov H S C η B hLyap⟩

/-- **The Lyapunov solution is positive semidefinite** for positive definite `H` and `D ⪰ 0`:
`xᵀΣx = lim xᵀΣ_s x ≥ 0`. -/
theorem lyapunov_posSemidef {H S D : Matrix ι ι ℝ} (hH : H.PosDef) (hS : Sᵀ = S)
    (hLyap : H * S + S * H = D) (hD : D.PosSemidef) : S.PosSemidef := by
  have hHt : Hᵀ = H := by
    have h := hH.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · change Sᴴ = S
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial]
  · rw [star_trivial]
    refine ge_of_tendsto (quadForm_ouCov_tendsto hH S x) ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with s hs
    have h := (ouCov_posSemidef H S D hHt hS hLyap hD hs).dotProduct_mulVec_nonneg x
    rwa [star_trivial] at h


end

end Laplace.Patterning
