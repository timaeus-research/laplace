/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseRefinementBudget
import Laplace.Multi.CompletionLawEqProjection
import Laplace.Multi.FiniteResponse
import Laplace.Multi.PathEnergy

/-!
# The trivial family and the featureless start of the budget

For the trivial feature family `S₀ = 0` every data law has mean `0`, and the entropy response of
that mean is the featureless law itself, `R^{S₀}_0 = ν` (`responseProjection_zero_family`): the
featureless law is the response of the coarsest possible family, the one that sees nothing. When
the coarsest level of a chain of refinements is trivial, the global refinement budget of
`ResponseRefinementBudget` therefore starts at the reference law:
`KL(D ‖ ν) = KL(D ‖ R_K) + Σ_{k<K} KL(R_{k+1} ‖ R_k)` (`klDiv_levelResponse_telescope_of_zero`),
the total information of the data relative to the featureless reference — maximal entropy
relative to `ν`, Shannon entropy only for a uniform reference — is spent in exact nonnegative
increments along the chain.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Trivial

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  (ν : Measure X) [IsProbabilityMeasure ν]

/-- **The featureless law is the response of the trivial family**: `R^{S₀}_0 = ν`. -/
theorem responseProjection_zero_family :
    responseProjection (S := fun _ : J ↦ fun _ : X ↦ (0 : ℝ)) (fun _ ↦ Bdd.const 0) ν 0 = ν := by
  have h := familyMeasure_eq_responseProjection_meanMap (S := fun _ : J ↦ fun _ : X ↦ (0 : ℝ))
    (fun _ ↦ Bdd.const 0) ν 0
  rw [familyMeasure_zero_eq (S := fun _ : J ↦ fun _ : X ↦ (0 : ℝ)) (fun _ ↦ Bdd.const 0) ν] at h
  have hm := mean_familyMeasure_one_zero (S := fun _ : J ↦ fun _ : X ↦ (0 : ℝ))
    (fun _ ↦ Bdd.const 0) ν 0
  have hm0 : (fun i : J ↦ ∫ x, (fun _ : J ↦ fun _ : X ↦ (0 : ℝ)) i x ∂familyMeasure ν
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) (fun _ : J ↦ fun _ : X ↦ (0 : ℝ)) 1 0) = 0 := by
    funext i
    simp
  rw [hm0] at hm
  rw [← hm] at h
  exact h.symm

end Trivial

section Chain

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : ℕ → Type*} [∀ k, Fintype (J k)]
  [∀ k, Nonempty (J k)] {S : (k : ℕ) → J k → X → ℝ} (hS : ∀ k j, Bdd (S k j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (D : Measure X) [IsProbabilityMeasure D]
  (hchain : ∀ k, Refines (S k) (S (k + 1)) ν) (hDν : D ≪ ν)
include hS hchain hDν

omit [IsProbabilityMeasure D] hchain hDν in
/-- With a trivial coarsest family the level-`0` response is the featureless law. -/
theorem levelResponse_zero_of_zero (h0 : S 0 = fun _ _ ↦ 0) : levelResponse hS ν D 0 = ν := by
  unfold levelResponse
  have e : (fun j ↦ ∫ x, S 0 j x ∂D) = (0 : J 0 → ℝ) := by
    funext j
    rw [h0]
    simp
  rw [e]
  have hgen : ∀ (T : J 0 → X → ℝ) (hT : ∀ j, Bdd (T j)), T = (fun _ _ ↦ 0) →
      responseProjection hT ν 0 = ν := by
    intro T hT hT0
    subst hT0
    exact responseProjection_zero_family ν
  exact hgen (S 0) (hS 0) h0

/-- **THE BUDGET FROM THE FEATURELESS LAW**: with a trivial coarsest family,
`KL(D ‖ ν) = KL(D ‖ R_K) + Σ_{k<K} KL(R_{k+1} ‖ R_k)`. -/
theorem klDiv_levelResponse_telescope_of_zero (h0 : S 0 = fun _ _ ↦ 0) {K : ℕ}
    (hK : genRate ν (S K) (fun j ↦ ∫ x, S K j x ∂D) ≠ ⊤) :
    klDiv D ν = klDiv D (levelResponse hS ν D K) +
      ∑ k ∈ Finset.range K, klDiv (levelResponse hS ν D (k + 1)) (levelResponse hS ν D k) := by
  rw [← klDiv_levelResponse_telescope hS ν D hchain hDν hK,
    levelResponse_zero_of_zero hS ν D h0]

end Chain

end Laplace.Multi
