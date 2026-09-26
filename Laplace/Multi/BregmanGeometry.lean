/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AtlasEnergy

/-!
# The Bregman geometry of the atlas: three points and two orientations

* **Three-point identity** (`toReal_klDiv_responseProjection_three_point`): for a finite-rate `A`
  and interior `B, C`,
  `KL(Π(A)‖Π(C)) = KL(Π(A)‖Π(B)) + KL(Π(B)‖Π(C)) + ⟨θ(C) − θ(B), A − B⟩`.
  The generalised Pythagorean theorem holds exactly when the mixed pairing vanishes
  (`klDiv_responseProjection_three_point_eq_iff`): the arrival direction `A − B` of the straight
  response path into `B` is Fisher-orthogonal at `B` to the departure direction of the natural
  path from `B` to `C` (whose mean-coordinate tangent is `Σ_B(θ_C − θ_B)`, so that the Fisher
  pairing
  is exactly `⟨θ_C − θ_B, A − B⟩`).
* **Asymmetry as weighted curvature** (`toReal_klDiv_responseProjection_sub_symm`): for
  interior `M`,
  `KL(Π(M)‖ν) − KL(ν‖Π(M)) = ∫₀¹ (1 − 2s) κ(s) ds`, the companion of the sum `∫₀¹ κ`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The three-point identity** between atlas points. -/
theorem toReal_klDiv_responseProjection_three_point {A B C : J → ℝ} (hA : genRate ν S A ≠ ⊤)
    (hB : B ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hC : C ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (klDiv (responseProjection hS ν A) (responseProjection hS ν C)).toReal =
      (klDiv (responseProjection hS ν A) (responseProjection hS ν B)).toReal +
        (klDiv (responseProjection hS ν B) (responseProjection hS ν C)).toReal +
        dotJ ((responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos ν) hS C : J → ℝ) -
          (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos ν) hS B : J → ℝ)) (A - B) := by
  have hBfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hB
  rw [toReal_klDiv_responseProjection_interior hS ν hA hC,
    toReal_klDiv_responseProjection_interior hS ν hA hB,
    toReal_klDiv_responseProjection_interior hS ν hBfin hC, (isLinearMap_dotJ _).map_sub A B,
    (isLinearMap_dotJ _).map_sub A C, (isLinearMap_dotJ _).map_sub A B,
    (isLinearMap_dotJ _).map_sub B C]
  have e1 := (isLinearMap_dotJ A).map_sub
  simp only [dotJ] at *
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- **Generalised Pythagoras iff Fisher orthogonality**: the three-point identity reduces to
`KL(Π(A)‖Π(C)) = KL(Π(A)‖Π(B)) + KL(Π(B)‖Π(C))` exactly when `⟨θ(C) − θ(B), A − B⟩ = 0`. -/
theorem klDiv_responseProjection_three_point_eq_iff {A B C : J → ℝ} (hA : genRate ν S A ≠ ⊤)
    (hB : B ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hC : C ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (klDiv (responseProjection hS ν A) (responseProjection hS ν C)).toReal =
        (klDiv (responseProjection hS ν A) (responseProjection hS ν B)).toReal +
          (klDiv (responseProjection hS ν B) (responseProjection hS ν C)).toReal ↔
      dotJ ((responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos ν) hS C : J → ℝ) -
          (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos ν) hS B : J → ℝ)) (A - B) = 0 := by
  rw [toReal_klDiv_responseProjection_three_point hS ν hA hB hC]
  constructor
  · intro h
    linarith
  · intro h
    rw [h, add_zero]

/-- **Divergence asymmetry as weighted curvature**: `KL(Π(M)‖ν) − KL(ν‖Π(M)) = ∫₀¹ (1 − 2s) κ`. -/
theorem toReal_klDiv_responseProjection_sub_symm {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (klDiv (responseProjection hS ν M) ν).toReal - (klDiv ν (responseProjection hS ν M)).toReal =
      ∫ s in Ioo (0 : ℝ) 1, (1 - 2 * s) * atlasCurv hS ν hfin s := by
  obtain ⟨-, -, hQkl, -⟩ := responseProjection_spec hS ν hfin
  rw [hQkl, genRate_toReal_eq_integral_atlasCurv hS ν hfin,
    toReal_klDiv_featureless_responseProjection_eq_integral hS ν hfin hrel]
  have h1 := integrableOn_atlasCurv_weighted hS ν hfin
  have h2 : IntegrableOn (fun s ↦ s * atlasCurv hS ν hfin s) (Ioo (0 : ℝ) 1) := by
    have := (integrableOn_atlasCurv hS ν hfin hrel).sub h1
    refine this.congr_fun (fun s _ ↦ ?_) measurableSet_Ioo
    simp only [Pi.sub_apply]
    ring
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
  ring

end Laplace.Multi
