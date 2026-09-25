/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMap
import Laplace.Multi.HessianRoute

/-!
# The asymptotic response metric at a regular minimum

The response form `g_a(v, u) = t² Cov_a(R_v, R_u)` of `ResponseMap` is the Fisher information of
the posterior family in the data directions `v, u`. At a nondegenerate minimiser of the loss the
first-order Laplace expansion of the covariance (`eq:cov` of the primer,
`gibbsCov_first_order_rate_sharp_posDef`) gives

  `g_a(v, u) = t ⟨∇R_v, H⁻¹ ∇R_u⟩ + O(1)`   (`responseForm_asymptotic`),

with `H` the Hessian of the loss at the minimiser and `∇R_v` the gradient of the direction loss
there: the response metric grows linearly in the inverse temperature, and its limiting shape is
the pull-back of the inverse Hessian under the Jacobian of the loss map `q ↦ L_q` at the
minimiser. This is the asymptotic layer of the response map at a regular point of the data
manifold; the singular layer is where the scaling in `t` becomes anisotropic and part of the phase
diagram. Here the prior is Lebesgue measure on `ι → ℝ` (`priorExp_volume_one`).
-/

open MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- With prior density `1` on `ι → ℝ` the posterior expectation is the seabed's Gibbs
expectation. -/
theorem priorExp_volume_one (L φ : (ι → ℝ) → ℝ) (t : ℝ) :
    priorExp volume (fun _ ↦ (1 : ℝ)) L φ t = gibbsExpectation L t φ := by
  simp only [priorExp, priorZ, gibbsExpectation, partitionFunction, mul_one]

theorem priorCov_volume_one (L φ ψ : (ι → ℝ) → ℝ) (t : ℝ) :
    priorCov volume (fun _ ↦ (1 : ℝ)) L φ ψ t = gibbsCov L t φ ψ := by
  simp only [priorCov, gibbsCov, priorExp_volume_one]

theorem responseForm_volume_one (L₀ : (ι → ℝ) → ℝ) {κ : Type*} [Fintype κ]
    (R : κ → (ι → ℝ) → ℝ) (a : κ → ℝ) (t : ℝ) (v u : κ → ℝ) :
    responseForm volume (fun _ ↦ (1 : ℝ)) L₀ R a t v u =
      t ^ 2 * gibbsCov (affLoss L₀ R a) t (dirLoss R v) (dirLoss R u) := by
  simp only [responseForm, priorCov_volume_one]

/-- **The response metric at a regular minimum**: `g_a(v, u) / t → ⟨∇R_v, H⁻¹ ∇R_u⟩` at rate
`O(1/t)`, i.e. `g_a(v, u) = t ⟨∇R_v, H⁻¹ ∇R_u⟩ + O(1)`. -/
theorem responseForm_asymptotic [DecidableEq ι] [Nonempty ι] (L₀ : (ι → ℝ) → ℝ) {κ : Type*}
    [Fintype κ] (R : κ → (ι → ℝ) → ℝ) (a : κ → ℝ) (v u : κ → ℝ) {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {gv gu : ι → ℝ} (hV : PotentialJetApprox (affLoss L₀ R a) (matCLM P))
    (hv : ObservableJetApprox (dirLoss R v) gv) (hu : ObservableJetApprox (dirLoss R u) gu) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |responseForm volume (fun _ ↦ (1 : ℝ)) L₀ R a t v u / t - dot gv (matCLM P⁻¹ gu)| ≤
        K / t := by
  obtain ⟨K, T₀, hT₀, hK⟩ := gibbsCov_first_order_rate_sharp_posDef (affLoss L₀ R a) (dirLoss R v)
    (dirLoss R u) hP gv gu hV hv hu
  refine ⟨K, T₀, hT₀, fun t ht ↦ ?_⟩
  have ht0 : t ≠ 0 := by linarith
  rw [responseForm_volume_one, show t ^ 2 * gibbsCov (affLoss L₀ R a) t (dirLoss R v)
    (dirLoss R u) / t = t * gibbsCov (affLoss L₀ R a) t (dirLoss R v) (dirLoss R u) by
      field_simp]
  exact hK t ht

end Laplace.Multi
