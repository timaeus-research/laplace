/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.GeneralResidualSplit
import Laplace.Multi.EmpiricalProjection

/-!
# Pythagoras against an arbitrary interior target

For a data law `D ≪ ν` of finite information and any interior response `N`,

  `KL(D ‖ Π(N)) = KL(D ‖ D↑) + KL(S_*D ‖ S_*Π(M_D)) + KL(Π(M_D) ‖ Π(N))`
                                                (`klDiv_responseProjection_target_eq`)

the fibre information, the marginal-invisible information, and the divergence between the two atlas
points. The proof: the log-density of `Π(N)` relative to `ν` is affine in `S`, so its expectation
under `D` equals its expectation under `Π(M_D)` (the means agree); combining the two tilted-target
identities with the general residual split gives the statement. Along the bridge `D_s = (1−s)ν + sD`
the response is `M_s = (1−s)m₀ + sM_D`, and the identity reads

  `KL(D_s ‖ Π(N)) = L_s + R_s + KL(Π(M_s) ‖ Π(N))`   (`klDiv_bridge_responseProjection_target_eq`).

With `N = M_D` this is the projection defect `KL(D ‖ Π(M_D)) = L + R` of the residual split; with
`N` arbitrary it is the commuting projection diagram in one theorem.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **Pythagoras against an arbitrary interior target**:
`KL(D ‖ Π(N)) = KL(D ‖ D↑) + KL(S_*D ‖ S_*Π(M_D)) + KL(Π(M_D) ‖ Π(N))`. -/
theorem klDiv_responseProjection_target_eq (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) {N : J → ℝ}
    (hrelN : N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv D (responseProjection hS ν N) =
      klDiv D (statisticLift ν D (statPoint S)) +
        klDiv (D.map (statPoint S))
          ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)).map (statPoint S)) +
        klDiv (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)) (responseProjection hS ν N) := by
  have hDν : D ≪ ν := (klDiv_ne_top_iff.1 hDkl).1
  have hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤ := fun h ↦
    hDkl (klDiv_eq_top_of_genRate_eq_top hS ν D h)
  obtain ⟨hQP, hQM, hQkl, hpyth⟩ := responseProjection_spec hS ν hfin
  have hsplit := klDiv_responseProjection_eq_statisticLift_add_map' hS ν D hDkl
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D) := ⟨_, rfl⟩
  rw [← hQ] at hQM hQkl hpyth hsplit ⊢
  have hQP' : IsProbabilityMeasure Q := by
    rw [hQ]
    exact hQP
  have hDQ := hpyth D inferInstance rfl
  have hQkl' : klDiv Q ν ≠ ⊤ := by
    rw [hQkl]
    exact hfin
  have hQν : Q ≪ ν := (klDiv_ne_top_iff.1 hQkl').1
  have hDQne : klDiv D Q ≠ ⊤ := by
    intro h
    rw [h, top_add] at hDQ
    exact hDkl hDQ
  obtain ⟨θ, hθ⟩ : ∃ θ : J → ℝ, θ = (responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS N : J → ℝ) := ⟨_, rfl⟩
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hrelN, ← hθ,
    familyMeasure_one_zero_eq_tilted hS ν]
  have hbdd : Bdd (fun x ↦ -1 * dirLoss S θ x) := Bdd.const_mul (-1) (bdd_dirLoss hS _)
  rw [klDiv_tilted_right_eq ν D hDν hDkl hbdd, klDiv_tilted_right_eq ν Q hQν hQkl' hbdd, hQkl]
  have hmeanD : ∫ x, -1 * dirLoss S θ x ∂D = -dotJ θ (fun i ↦ ∫ x, S i x ∂D) := by
    rw [MeasureTheory.integral_const_mul, ← dotJ_integral_eq D hS _]
    ring
  have hmeanQ : ∫ x, -1 * dirLoss S θ x ∂Q = -dotJ θ (fun i ↦ ∫ x, S i x ∂D) := by
    rw [MeasureTheory.integral_const_mul, ← dotJ_integral_eq Q hS _, hQM]
    ring
  have hlog : Real.log (∫ x, Real.exp (-1 * dirLoss S θ x) ∂ν) = featCgf ν S (-θ) := by
    unfold featCgf
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [dirLoss_neg (S := S)]
    ring_nf
  have hnn : 0 ≤ (genRate ν S (fun i ↦ ∫ x, S i x ∂D)).toReal -
      -dotJ θ (fun i ↦ ∫ x, S i x ∂D) + featCgf ν S (-θ) := by
    have hF := dotJ_sub_genRate_le_featCgf ν hfin (-θ)
    rw [dotJ_neg_left] at hF
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (klDiv D Q).toReal := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ ENNReal.toReal_nonneg
  have hDQ' : klDiv D Q = ENNReal.ofReal c := by
    rw [hc, ENNReal.ofReal_toReal hDQne]
  have hsum : (klDiv D ν).toReal = c + (genRate ν S (fun i ↦ ∫ x, S i x ∂D)).toReal := by
    rw [hDQ, ENNReal.toReal_add hDQne hfin, hc]
  rw [hmeanD, hmeanQ, hlog, hsum, ← hsplit, hDQ', ← ENNReal.ofReal_add hc0 hnn]
  congr 1
  ring

/-- **The pathwise Pythagorean identity** along the bridge `D_s = aν + bD`:
`KL(D_s ‖ Π(N)) = L_s + R_s + KL(Π(M_s) ‖ Π(N))`, with `M_s = a m₀ + b M_D`. -/
theorem klDiv_bridge_responseProjection_target_eq (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) {a b : ℝ≥0} (hab : a + b = 1) {N : J → ℝ}
    (hrelN : N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv (a • ν + b • D) (responseProjection hS ν N) =
      klDiv (a • ν + b • D) (statisticLift ν (a • ν + b • D) (statPoint S)) +
        klDiv ((a • ν + b • D).map (statPoint S))
          ((responseProjection hS ν
            ((a : ℝ) • (fun i ↦ ∫ x, S i x ∂ν) + (b : ℝ) • fun i ↦ ∫ x, S i x ∂D)).map
              (statPoint S)) +
        klDiv (responseProjection hS ν
            ((a : ℝ) • (fun i ↦ ∫ x, S i x ∂ν) + (b : ℝ) • fun i ↦ ∫ x, S i x ∂D))
          (responseProjection hS ν N) := by
  have hDν : D ≪ ν := (klDiv_ne_top_iff.1 hDkl).1
  have := isProbabilityMeasure_mixture ν D hab
  have hkl : klDiv (a • ν + b • D) ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (klDiv_mixture_le ν ν D Measure.AbsolutelyContinuous.rfl hDν hab)
    rw [klDiv_self, mul_zero, zero_add]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hDkl
  have h := klDiv_responseProjection_target_eq hS ν (a • ν + b • D) hkl hrelN
  rwa [mean_mixture hS ν D a b] at h

end Laplace.Multi
