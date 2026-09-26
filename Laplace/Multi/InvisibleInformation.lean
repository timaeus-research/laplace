/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CubicResponse

/-!
# The invisible information along the data path

The information decomposition splits the information of a data law into the part visible through
the responses, `𝓘_ν(E_D S)`, and the invisible remainder `KL(D ‖ Π_ν(E_D S))`. Along the data path
`D_s = ν.tilted (s h)` both parts are differentiable, and

* `hasDerivAt_invisible_dataPath`:
  `d/ds KL(D_s ‖ Π(M(s))) = s Var_{D_s} h + ⟨θ(M(s)), Cov_{D_s}(S, h)⟩`;
* `hasDerivAt_invisible_dataPath_zero`: the invisible information starts with zero velocity;
* **`hasDerivAt_deriv_invisible_dataPath_zero`**: its curvature at the featureless law is the
  residual variance `Var_ν(h − regressor)`, the part of the data direction unexplained by the
  visible statistics.

So at second order the information entering the data, `Var_ν h`, is exactly the sum of the visible
curvature `Var_ν(regressor)` and the invisible curvature `Var_ν(h − regressor)`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The invisible information along the data path is the total information minus the visible one. -/
theorem invisible_dataPath_eq (s : ℝ) :
    (klDiv (ν.tilted (fun x ↦ s * h x))
        (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x)))).toReal =
      (klDiv (ν.tilted (fun x ↦ s * h x)) ν).toReal -
        (genRate ν S (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x))).toReal := by
  have h1 := information_decomposition_path hS ν hh s
  have h2 := klDiv_tilted_eq_integral ν hh s
  linarith

/-- **The invisible information moves by the residual forcing**:
`d/ds KL(D_s ‖ Π(M(s))) = s Var_{D_s} h + ⟨θ(M(s)), Cov_{D_s}(S, h)⟩`. -/
theorem hasDerivAt_invisible_dataPath (s₀ : ℝ) :
    HasDerivAt (fun s ↦ (klDiv (ν.tilted (fun x ↦ s * h x))
        (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x)))).toReal)
      (s₀ * lawCov (ν.tilted (fun x ↦ s₀ * h x)) h h +
        dotJ (dataTheta hS ν hh s₀ : J → ℝ) (dataCov S ν h s₀)) s₀ := by
  have h := (hasDerivAt_klDiv_tilted_toReal ν hh s₀).sub (hasDerivAt_genRate_dataPath hS ν hh s₀)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)).congr_deriv ?_
  · exact invisible_dataPath_eq hS ν hh s
  · unfold lawCov
    ring

/-- The invisible information starts with zero velocity at the featureless law. -/
theorem hasDerivAt_invisible_dataPath_zero :
    HasDerivAt (fun s ↦ (klDiv (ν.tilted (fun x ↦ s * h x))
        (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x)))).toReal)
      0 0 := by
  have := hasDerivAt_invisible_dataPath hS ν hh 0
  rwa [dataTheta_zero, Submodule.coe_zero, dotJ_zero_left, zero_mul, add_zero] at this

/-- **The curvature of the invisible information at the featureless law is the residual variance**
`Var_ν(h − regressor)`. -/
theorem hasDerivAt_deriv_invisible_dataPath_zero :
    HasDerivAt (deriv fun s ↦ (klDiv (ν.tilted (fun x ↦ s * h x))
        (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x)))).toReal)
      (lawCov ν (fun x ↦ h x - regressor hS ν hh x) (fun x ↦ h x - regressor hS ν hh x)) 0 := by
  have e : (deriv fun s ↦ (klDiv (ν.tilted (fun x ↦ s * h x))
      (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ s * h x)))).toReal) =
      fun s ↦ s * lawCov (ν.tilted (fun x ↦ s * h x)) h h +
        dotJ (dataTheta hS ν hh s : J → ℝ) (dataCov S ν h s) :=
    funext fun s ↦ (hasDerivAt_invisible_dataPath hS ν hh s).deriv
  rw [e]
  have h1 : HasDerivAt (fun s ↦ s * lawCov (ν.tilted (fun x ↦ s * h x)) h h)
      (1 * lawCov (ν.tilted (fun x ↦ (0 : ℝ) * h x)) h h +
        0 * ∫ x, (h x - ∫ y, h y ∂ν.tilted (fun x ↦ (0 : ℝ) * h x)) ^ 3
          ∂ν.tilted (fun x ↦ (0 : ℝ) * h x)) 0 :=
    (hasDerivAt_id 0).mul (hasDerivAt_var_tilted ν hh 0)
  have h2 : HasDerivAt (fun s ↦ dotJ (dataTheta hS ν hh s : J → ℝ) (dataCov S ν h s))
      (-lawCov ν (regressor hS ν hh) (regressor hS ν hh)) 0 := by
    exact (hasDerivAt_rateVel_zero hS ν hh).neg.congr_of_eventuallyEq
      (Eventually.of_forall fun s ↦ by simp)
  refine (h1.add h2).congr_deriv ?_
  rw [tilted_zero_mul, ← residual_variance hS ν hh]
  ring

end Laplace.Multi
