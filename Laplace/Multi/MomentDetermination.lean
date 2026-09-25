/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MixtureSeries

/-!
# The moments of the loss contrast determine the mixture line

The partition function along a mixture line is the exponential generating function of the moments
of the loss contrast under the base posterior (`TiltData.hasSum_priorZ_pathLoss`), and the
numerator of an observable `φ` is that of the mixed moments `∫ φ Δⁿ e^{-tL₀} π`
(`TiltData.hasSum_mixNum`). Hence two contrasts with the same base moments have the same partition
function along their whole lines (`priorZ_pathLoss_eq_of_moments_eq`), and two contrasts with the
same mixed moments with `φ` have the same response `s ↦ ⟨φ⟩_{t,s}` (`mixExp_eq_of_moments_eq`).
As Astra notes, the scalar moments determine the scalar tilt family (the law of `Δ` under the base
posterior), while the response of a general observable requires the joint information carried by
the mixed moments.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [Nonempty X]

/-- Two contrasts with the same base-posterior moments have the same partition function along
their mixture lines. -/
theorem priorZ_pathLoss_eq_of_moments_eq {π L₀ Δ Δ' : X → ℝ} {t M M' : ℝ}
    (h : TiltData μ (baseWeight π L₀ t) Δ M) (h' : TiltData μ (baseWeight π L₀ t) Δ' M')
    (hmom : ∀ n : ℕ, ∫ x, Δ x ^ n * Real.exp (-(t * L₀ x)) * π x ∂μ =
      ∫ x, Δ' x ^ n * Real.exp (-(t * L₀ x)) * π x ∂μ) (s : ℝ) :
    priorZ μ π (pathLoss L₀ Δ s) t = priorZ μ π (pathLoss L₀ Δ' s) t := by
  have h1 := h.hasSum_priorZ_pathLoss s
  have h2 := h'.hasSum_priorZ_pathLoss s
  simp_rw [hmom] at h1
  exact h1.tsum_eq.symm.trans h2.tsum_eq

/-- Two contrasts with the same mixed moments with `φ` (and the same base moments) have the same
response `s ↦ ⟨φ⟩_{t,s}` along their mixture lines. -/
theorem mixExp_eq_of_moments_eq {π L₀ Δ Δ' : X → ℝ} {t M M' : ℝ}
    (h : TiltData μ (baseWeight π L₀ t) Δ M) (h' : TiltData μ (baseWeight π L₀ t) Δ' M')
    {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
    (hmom : ∀ n : ℕ, ∫ x, Δ x ^ n * Real.exp (-(t * L₀ x)) * π x ∂μ =
      ∫ x, Δ' x ^ n * Real.exp (-(t * L₀ x)) * π x ∂μ)
    (hmix : ∀ n : ℕ, ∫ x, φ x * Δ x ^ n * Real.exp (-(t * L₀ x)) * π x ∂μ =
      ∫ x, φ x * Δ' x ^ n * Real.exp (-(t * L₀ x)) * π x ∂μ) (s : ℝ) :
    mixExp μ π L₀ Δ φ t s = mixExp μ π L₀ Δ' φ t s := by
  have h1 := h.hasSum_mixNum hφm hφ s
  have h2 := h'.hasSum_mixNum hφm hφ s
  simp_rw [hmix] at h1
  unfold mixExp priorExp
  rw [h1.tsum_eq.symm.trans h2.tsum_eq, priorZ_pathLoss_eq_of_moments_eq h h' hmom s]

end Laplace.Multi
