/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMetric
import Laplace.Multi.CovarianceExplicit

/-!
# The shape metric at a fixed minimiser, for general regular families

When a data direction leaves the minimiser fixed (`∇R_v(m) = 0`) the leading response metric
`t ⟨∇R_v, H⁻¹ ∇R_u⟩` vanishes, and the response form has a finite limit given by the second-order
Laplace coefficient of the covariance (`gibbsCov_first_order_rate_explicit`,
`cov2Coefficient`). With both gradients zero the three cubic terms of that coefficient drop out
(`cov2Coefficient_grad_zero`) and what remains is

  `g_a(v, u) → ½ tr(A_v Σ A_u Σ)`,   `Σ = H⁻¹`, `A_v = ∇²R_v(m)`
  (`responseForm_shape_asymptotic`),

the **shape metric** on the fibre of the minimiser map: the Fisher–Rao metric of the limiting
centred Gaussian in its precision, exactly the `t`-independent value found for Gaussian families
(`GaussianShapeMetric`). Two data distributions with the same learned minimiser are therefore at
a finite response distance as `t → ∞`, measured by how their loss Hessians differ.
-/

open MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- With both gradients zero the second-order covariance coefficient is the pure shape term
`½ tr(A_φ Σ A_ψ Σ)`. -/
theorem cov2Coefficient_grad_zero (V φ ψ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H) (hφ : ObservableTensorApprox φ 0)
    (hψ : ObservableTensorApprox ψ 0) :
    cov2Coefficient V φ ψ H Hinv 0 0 hV hφ hψ =
      (1 / 2 : ℝ) * trASig (hφ.A.comp (Hinv.comp (hψ.A.comp Hinv))) 1 := by
  simp [cov2Coefficient, dot]

/-- **The shape metric at a fixed minimiser**: if the direction losses `R_v`, `R_u` have zero
gradient at the minimiser (quintic/tensor jets with `a = b = 0`), then
`g_a(v, u) → ½ tr(A_v Σ A_u Σ)` at rate `O(1/t)`. -/
theorem responseForm_shape_asymptotic [Nonempty ι] (L₀ : (ι → ℝ) → ℝ) {κ : Type*} [Fintype κ]
    (R : κ → (ι → ℝ) → ℝ) (a : κ → ℝ) (v u : κ → ℝ) {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hV : PotentialQuinticApprox (affLoss L₀ R a) H)
    (hv : ObservableQuinticApprox (dirLoss R v) 0) (hu : ObservableTensorApprox (dirLoss R u) 0)
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |responseForm volume (fun _ ↦ (1 : ℝ)) L₀ R a t v u -
        (1 / 2 : ℝ) * trASig (hv.A.comp (Hinv.comp (hu.A.comp Hinv))) 1| ≤ K / t := by
  obtain ⟨K, T₀, hT₀, hK⟩ := gibbsCov_first_order_rate_explicit (affLoss L₀ R a) (dirLoss R v)
    (dirLoss R u) H Hinv 0 0 hV hv hu rfl hGauss
  refine ⟨K, T₀, hT₀, fun t ht ↦ ?_⟩
  rw [responseForm_volume_one, ← cov2Coefficient_grad_zero (affLoss L₀ R a) (dirLoss R v)
    (dirLoss R u) H Hinv hV.toPotentialTensorApprox hv.toObservableTensorApprox hu]
  exact hK t ht

/-- The trace form of the shape metric: `trASig (A Σ B Σ) 1 = tr(A Σ B Σ)` for matrix data. -/
theorem trASig_matCLM_eq_trace (A S B : Matrix ι ι ℝ) :
    trASig ((matCLM A).comp ((matCLM S).comp ((matCLM B).comp (matCLM S)))) 1 =
      Matrix.trace (A * S * B * S) := by
  simp only [trASig, ContinuousLinearMap.comp_apply, one_apply_eq_self, matCLM_apply,
    Matrix.mulVec_mulVec, Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.mulVec_single_one]
  simp [Matrix.mul_assoc]

end Laplace.Multi
