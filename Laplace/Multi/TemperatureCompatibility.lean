/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LossHessianBlocks
import Laplace.Multi.SchurComplement

/-!
# Temperature compatibility: the slices form one thermodynamic object

At a fixed response `M` the temperature-`t` slice dual potential `I_t(M)` (the Legendre transform
of the free energy at the response `M`, `DualPotential`) depends on the temperature through the
temperature path `θ(t) = (t, t a_t(M))` of natural coordinates. The first law
`∂_t I_t(M) = u_t(M) = ⟨L₀⟩_{t,M}` — the expected base loss at fixed response is the temperature
derivative of the slice dual potential — is `hasDerivAt_dualPotential_temp` (`ReducedPotential`);
here `u_t(M)` is identified with the loss chart (`lossChart_eq_obsMean`) and differentiated once
more:

* `∂_t² I_t(M) = ∂_t u_t(M) = −Var_{t,M}(H) = −δ_t(M)` — the second derivative is minus the
  residual variance (`hasDerivAt_lossChart_temp`, `hasDerivAt_obsMean_base_temp`), so `t ↦ I_t(M)`
is
  strictly concave under joint nondegeneracy (`lossChart_temp_deriv_neg`, from `natVarH_pos`).

Together with `∂_t 𝒮|_M = −t δ` (`hasDerivAt_relEntropy_temp`) and the block-diagonal mixed
metric `δ dt² + dMᵀC⁻¹dM` (`natForm_sliceInv_deriv`), the same residual fluctuation `δ` controls the
temperature response of the dual potential, its concavity, the entropy production and the Fisher
energy of the fixed-response temperature path.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty ι] [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π)
  (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀)
  {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR hnd

/-- The loss chart is the expected base loss at fixed response: `h(t, M) = u_t(M)`. -/
theorem lossChart_eq_obsMean {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    lossChart μ π L₀ R (jointPoint t M) = obsMean μ π L₀ L₀ R t M :=
  (obsMean_eq_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM L₀).symm

/-- **`∂_t² I_t(M) = −Var_{t,M}(H)`**: the expected base loss at fixed response decreases with the
temperature at the rate of the residual variance. -/
theorem hasDerivAt_lossChart_temp [DecidableEq ι] {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ lossChart μ π L₀ R (jointPoint t M))
      (-priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t₀))
        (natH μ π L₀ R (tempPath μ π L₀ R M t₀))
        (natH μ π L₀ R (tempPath μ π L₀ R M t₀)) 1) t₀ := by
  have h := hasDerivAt_lossChart_line hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM 1 0
  -- reparametrise `s ↦ t₀ + s`
  have hline : (fun t ↦ lossChart μ π L₀ R (jointPoint t M)) =
      (fun s : ℝ ↦ lossChart μ π L₀ R (jointPoint t₀ M + s • jointPoint 1 0)) ∘ fun t ↦ t - t₀ := by
    funext t
    simp only [Function.comp]
    congr 1
    funext j
    cases j <;> simp [jointPoint]
  rw [hline]
  have h0 : HasDerivAt (fun s : ℝ ↦ lossChart μ π L₀ R (jointPoint t₀ M + s • jointPoint 1 0))
      (lossGrad μ π L₀ R (tempPath μ π L₀ R M t₀) 1 0) ((fun t : ℝ ↦ t - t₀) t₀) := by
    simp only [sub_self]
    exact h
  have h2 := HasDerivAt.comp (h := fun t : ℝ ↦ t - t₀) t₀ h0
    ((hasDerivAt_id' (x := t₀)).sub_const t₀)
  refine h2.congr_deriv ?_
  simp only [lossGrad, zero_dotProduct, add_zero, neg_one_mul, mul_one]

/-- **`∂_t u_t(M) = −Var_{t,M}(H)`** for the expected base loss at fixed response. -/
theorem hasDerivAt_obsMean_base_temp [DecidableEq ι] {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ obsMean μ π L₀ L₀ R t M)
      (-priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t₀))
        (natH μ π L₀ R (tempPath μ π L₀ R M t₀))
        (natH μ π L₀ R (tempPath μ π L₀ R M t₀)) 1) t₀ := by
  refine (hasDerivAt_lossChart_temp hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM).congr_of_eventuallyEq
    ?_
  filter_upwards [lt_mem_nhds ht₀] with t ht
  exact (lossChart_eq_obsMean hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM).symm

/-- The slice dual potential is strictly concave in the temperature: its second derivative is
minus the residual variance, which is positive under joint nondegeneracy. -/
theorem lossChart_temp_deriv_neg
    (hjnd : ∀ v : Option ι → ℝ, v ≠ 0 →
      ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss (jointStat L₀ R) v x = c)
    {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ} (hM : M ∈ interior (momentBody μ π R)) :
    deriv (fun t ↦ lossChart μ π L₀ R (jointPoint t M)) t₀ < 0 := by
  classical
  rw [(hasDerivAt_lossChart_temp hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM).deriv, neg_lt_zero]
  exact natVarH_pos hπm hπi hπ hπpos hL₀m hL₀ hR hjnd

end

end Laplace.Multi
