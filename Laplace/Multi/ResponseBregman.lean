/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FixedNormalLimit
import Laplace.Multi.ProjectionPythagoras
import Laplace.Multi.ResponsePathDifferential
import Laplace.Multi.EmpiricalProjection
import Laplace.Multi.StraightPathAtlas

/-!
# The response potential and its Bregman identity

The rate `I(M) = D(q_M ‖ ν)` of an interior response is, in natural coordinates,
`I(M) = −⟨θ(M), M⟩ − log Z(θ(M))` (`genRate_toReal_eq_neg_dotJ_sub_log`), and the information
between two response projections is the Bregman divergence of the response potential in mean
coordinates:

  `D(q_M ‖ q_N) = I(M) − I(N) + ⟨θ(N), M − N⟩`   (`toReal_klDiv_responseProjection_eq`).

Since `DI(N)[u] = −⟨θ(N), u⟩` (the rate's derivative along the straight path is `−⟨θ_s, Δ⟩`,
`hasDerivAt_atlasRate`), this is `D(q_M‖q_N) = I(M) − I(N) − DI(N)[M − N]`: the response potential
is a convex function of the mean whose Bregman divergence is the relative entropy of the
projections, and the supporting-hyperplane inequality `I(N) − ⟨θ(N), M − N⟩ ≤ I(M)`
(`genRate_toReal_ge_tangent`)
is its convexity.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Bregman

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The response chart `θ(M)`. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The response projection of an interior response is the Mathlib tilt by `−⟨θ(M), S⟩`. -/
theorem responseProjection_eq_tilted_responseTheta {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    responseProjection hS ν M = ν.tilted fun x ↦ -1 * dirLoss S (θr M : J → ℝ) x := by
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hM,
    familyMeasure_one_zero_eq_tilted hS ν]

/-- The pairing of a natural parameter with the mean of a response projection. -/
theorem integral_neg_dirLoss_responseProjection {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (θ : J → ℝ) :
    ∫ x, -1 * dirLoss S θ x ∂responseProjection hS ν M = -dotJ θ M := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hM
  have hspec := responseProjection_spec hS ν hfin
  have := hspec.1
  rw [integral_const_mul, ← dotJ_integral_eq _ hS, hspec.2.1]
  ring

/-- **The rate in natural coordinates**: `I(M) = −⟨θ(M), M⟩ − log Z(θ(M))`. -/
theorem genRate_toReal_eq_neg_dotJ_sub_log {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (genRate ν S M).toReal =
      -dotJ (θr M : J → ℝ) M -
        Real.log (∫ x, Real.exp (-1 * dirLoss S (θr M : J → ℝ) x) ∂ν) := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hM
  have hspec := responseProjection_spec hS ν hfin
  have hf : Bdd fun x ↦ -1 * dirLoss S (θr M : J → ℝ) x :=
    Bdd.const_mul (-1) (bdd_dirLoss hS _)
  have hmean := integral_neg_dirLoss_responseProjection hS ν hM (θr M : J → ℝ)
  rw [← hspec.2.2.1, responseProjection_eq_tilted_responseTheta hS ν hM, klDiv_tilted_eq ν hf,
    ENNReal.toReal_ofReal (integral_sub_log_nonneg ν hf),
    ← responseProjection_eq_tilted_responseTheta hS ν hM, hmean]

/-- **The Bregman identity in mean coordinates**:
`D(q_M ‖ q_N) = I(M) − I(N) + ⟨θ(N), M − N⟩`. -/
theorem toReal_klDiv_responseProjection_eq {M N : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hN : N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (klDiv (responseProjection hS ν M) (responseProjection hS ν N)).toReal =
      (genRate ν S M).toReal - (genRate ν S N).toReal + dotJ (θr N : J → ℝ) (M - N) := by
  have hfinM := genRate_ne_top_of_mem_intrinsicInterior hS ν hM
  have hspecM := responseProjection_spec hS ν hfinM
  have := hspecM.1
  have hac : responseProjection hS ν M ≪ ν := responseProjection_absolutelyContinuous hS ν hfinM
  have hkl : klDiv (responseProjection hS ν M) ν ≠ ⊤ := by
    rw [hspecM.2.2.1]
    exact hfinM
  have hf : Bdd fun x ↦ -1 * dirLoss S (θr N : J → ℝ) x :=
    Bdd.const_mul (-1) (bdd_dirLoss hS _)
  rw [responseProjection_eq_tilted_responseTheta hS ν hN, toReal_klDiv_tilted_right ν _ hac hkl hf,
    integral_neg_dirLoss_responseProjection hS ν hM, hspecM.2.2.1,
    genRate_toReal_eq_neg_dotJ_sub_log hS ν hN, (isLinearMap_dotJ _).map_sub]
  ring

/-- **Convexity of the response potential**: the tangent at `N` lies below the rate at `M`,
`I(N) − ⟨θ(N), M − N⟩ ≤ I(M)`. -/
theorem genRate_toReal_ge_tangent {M N : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hN : N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (genRate ν S N).toReal - dotJ (θr N : J → ℝ) (M - N) ≤ (genRate ν S M).toReal := by
  have h := toReal_klDiv_responseProjection_eq hS ν hM hN
  have h0 : 0 ≤ (klDiv (responseProjection hS ν M) (responseProjection hS ν N)).toReal :=
    ENNReal.toReal_nonneg
  linarith

/-- The Bregman divergence of the response potential is symmetric in sum with the pairing of the
parameter difference and the mean difference: `D(q_M‖q_N) + D(q_N‖q_M) = ⟨θ(N) − θ(M), M − N⟩`. -/
theorem toReal_klDiv_responseProjection_add_symm {M N : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hN : N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (klDiv (responseProjection hS ν M) (responseProjection hS ν N)).toReal +
        (klDiv (responseProjection hS ν N) (responseProjection hS ν M)).toReal =
      dotJ ((θr N : J → ℝ) - (θr M : J → ℝ)) (M - N) := by
  have e : dotJ ((θr N : J → ℝ) - (θr M : J → ℝ)) (M - N) =
      dotJ (θr N : J → ℝ) (M - N) - dotJ (θr M : J → ℝ) (M - N) := by
    simp only [dotJ, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [toReal_klDiv_responseProjection_eq hS ν hM hN, toReal_klDiv_responseProjection_eq hS ν hN hM,
    e]
  simp only [(isLinearMap_dotJ (θr M : J → ℝ)).map_sub, (isLinearMap_dotJ (θr N : J → ℝ)).map_sub]
  ring

end Bregman

end Laplace.Multi
