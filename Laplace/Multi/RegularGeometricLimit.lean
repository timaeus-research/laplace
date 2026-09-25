/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMetric
import Laplace.Patterning.MovingMinimizer

/-!
# The regular geometric limit: the response metric measures minimiser motion

At a regular point of the data manifold the response form grows linearly in the inverse
temperature with limiting shape `⟨∇R_v, H⁻¹ ∇R_u⟩` (`responseForm_asymptotic`), where `H` is the
Hessian of the loss at its minimiser and `∇R_v` the gradient of the direction loss there. The
stationarity equation `H Dm[v] + ∇R_v = 0` (`movingMinimizer_deriv`) identifies this limit with
the Hessian evaluated on the **velocities of the learned minimiser**:

  `g_a(v, u)/t → H(Dm[v], Dm[u])`   (`responseForm_asymptotic_minimizer`),

Astra's *regular geometric limit*: the leading response metric on the data manifold is the loss
Hessian pulled back along the minimiser section `q ↦ m(q)`. It is not literally a pull-back of a
fixed metric on parameter space (the Hessian itself moves with `q`), but a Hessian field along the
section; for well-specified negative log-likelihood losses it is the model Fisher information
pulled back by `m`. The identification is pure algebra once the minimiser velocity is known:
`⟨g, H⁻¹ g'⟩ = ⟨−H⁻¹g, H(−H⁻¹g')⟩` (`dot_inv_eq_hessian_form`).
-/

open MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `⟨g, H⁻¹ g'⟩ = ⟨−H⁻¹ g, H (−H⁻¹ g')⟩` for positive definite `H`: the inverse-Hessian pairing
of two gradients is the Hessian pairing of the corresponding minimiser velocities. -/
theorem dot_inv_eq_hessian_form {P : Matrix ι ι ℝ} (hP : P.PosDef) (gv gu : ι → ℝ) :
    dot gv (matCLM P⁻¹ gu) = (-(P⁻¹ *ᵥ gv)) ⬝ᵥ P *ᵥ (-(P⁻¹ *ᵥ gu)) := by
  have hunit : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv P hunit, Matrix.one_mulVec, matCLM_apply]
  have hPt : Pᵀ = P := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hP.1.eq
  have hsym : (P⁻¹ *ᵥ gv) ⬝ᵥ gu = gv ⬝ᵥ P⁻¹ *ᵥ gu := by
    rw [dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.transpose_nonsing_inv, hPt]
    exact dotProduct_comm _ _
  rw [hsym]
  rfl

/-- **The regular geometric limit**: if the minimiser velocities in the data directions `v, u`
are `mv = −H⁻¹ ∇R_v`, `mu = −H⁻¹ ∇R_u`, then `g_a(v, u)/t → H(mv, mu)` at rate `O(1/t)`. -/
theorem responseForm_asymptotic_minimizer [Nonempty ι] (L₀ : (ι → ℝ) → ℝ) {κ : Type*}
    [Fintype κ] (R : κ → (ι → ℝ) → ℝ) (a : κ → ℝ) (v u : κ → ℝ) {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {gv gu : ι → ℝ} (hV : PotentialJetApprox (affLoss L₀ R a) (matCLM P))
    (hv : ObservableJetApprox (dirLoss R v) gv) (hu : ObservableJetApprox (dirLoss R u) gu)
    {mv mu : ι → ℝ} (hmv : mv = -(P⁻¹ *ᵥ gv)) (hmu : mu = -(P⁻¹ *ᵥ gu)) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |responseForm volume (fun _ ↦ (1 : ℝ)) L₀ R a t v u / t - mv ⬝ᵥ P *ᵥ mu| ≤ K / t := by
  obtain ⟨K, T₀, hT₀, hK⟩ := responseForm_asymptotic L₀ R a v u hP hV hv hu
  refine ⟨K, T₀, hT₀, fun t ht ↦ ?_⟩
  rw [hmv, hmu, ← dot_inv_eq_hessian_form hP]
  exact hK t ht

/-- **The regular geometric limit with the minimiser velocities supplied by the stationarity
equation** (`movingMinimizer_deriv`): a differentiable curve `w` of critical points of the
gradient field `G` of the family in direction `v` (`∂_s G = ∇R_v`, `∂_w G = P` at `(0, m)`) has
velocity `−P⁻¹ ∇R_v`, so `g_a(v, v)/t → P(w'(0), w'(0))`. -/
theorem responseForm_asymptotic_movingMinimizer [Nonempty ι] (L₀ : (ι → ℝ) → ℝ) {κ : Type*}
    [Fintype κ] (R : κ → (ι → ℝ) → ℝ) (a : κ → ℝ) (v : κ → ℝ) {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {gv : ι → ℝ} (hV : PotentialJetApprox (affLoss L₀ R a) (matCLM P))
    (hv : ObservableJetApprox (dirLoss R v) gv)
    (G : ℝ → (ι → ℝ) → (ι → ℝ)) (w : ℝ → ι → ℝ) (w' w₀ : ι → ℝ)
    (G' : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)) (hw0 : w 0 = w₀) (hw : HasDerivAt w w' 0)
    (hG : HasFDerivAt (fun p : ℝ × (ι → ℝ) => G p.1 p.2) G' (0, w₀))
    (hG' : ∀ σ y, G' (σ, y) = σ • gv + P *ᵥ y) (hzero : ∀ s, G s (w s) = 0) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |responseForm volume (fun _ ↦ (1 : ℝ)) L₀ R a t v v / t - w' ⬝ᵥ P *ᵥ w'| ≤ K / t := by
  have hw' : w' = -(P⁻¹ *ᵥ gv) :=
    Laplace.Patterning.movingMinimizer_deriv G w w' w₀ gv P G' hw0 hw hG hG' hzero
      (isUnit_iff_ne_zero.mpr hP.det_pos.ne')
  exact responseForm_asymptotic_minimizer L₀ R a v v hP hV hv hv hw' hw'

end Laplace.Multi
