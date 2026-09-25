/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.IntegratedSusceptibility

/-!
# The bounded scale of the response geometry

If the Fisher speed of a data path stays below `C` on `[0, 1]` then its thermodynamic length is at
most `√C` (`thermoLength_le_sqrt_of_fisherSpeed_le`). On a mixture line this is the case whenever
`t² Var_{t,s}(Δ) ≤ C` uniformly in `s` (`TiltData.thermoLength_le_sqrt_of_var_le`): the `O(1)`
scale of the response geometry, occupied by data variations whose loss contrast has posterior
variance of order `t⁻²` — those that leave the learned minimiser fixed, where the limiting value
is the shape metric (`ShapeMetricLimit`, `GaussianShapeMetric`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A path of Fisher speed at most `C` on `[0,1]` has thermodynamic length at most `√C`. -/
theorem thermoLength_le_sqrt_of_fisherSpeed_le {π : X → ℝ} {L L' : ℝ → X → ℝ} {t C : ℝ}
    (hint : IntervalIntegrable (fun s ↦ Real.sqrt (fisherSpeed μ π L L' t s)) volume 0 1)
    (h : ∀ s ∈ Icc (0 : ℝ) 1, fisherSpeed μ π L L' t s ≤ C) :
    thermoLength μ π L L' t ≤ Real.sqrt C := by
  unfold thermoLength
  calc ∫ s in (0 : ℝ)..1, Real.sqrt (fisherSpeed μ π L L' t s)
      ≤ ∫ _ in (0 : ℝ)..1, Real.sqrt C :=
        intervalIntegral.integral_mono_on zero_le_one hint intervalIntegrable_const
          fun s hs ↦ Real.sqrt_le_sqrt (h s hs)
    _ = Real.sqrt C := by simp

variable [Nonempty X]

/-- **The bounded scale on a mixture line**: `t² Var_{t,s}(Δ) ≤ C` on `[0,1]` ⇒ `ℓ(t) ≤ √C`. -/
theorem TiltData.thermoLength_le_sqrt_of_var_le {π L₀ Δ : X → ℝ} {t M C : ℝ}
    (h : TiltData μ (baseWeight π L₀ t) Δ M) (ht : t ≠ 0)
    (hC : ∀ s ∈ Icc (0 : ℝ) 1, t ^ 2 * mixCov μ π L₀ Δ Δ Δ t s ≤ C) :
    thermoLength μ π (pathLoss L₀ Δ) (fun _ ↦ Δ) t ≤ Real.sqrt C := by
  have hΔ : Bdd Δ := ⟨h.R_meas, M, h.R_bound⟩
  refine thermoLength_le_sqrt_of_fisherSpeed_le ?_ fun s hs ↦ ?_
  · exact (Real.continuous_sqrt.comp
      (continuous_const.mul (h.continuous_mixCov ht hΔ))).intervalIntegrable 0 1
  · exact hC s hs

end Laplace.Multi
