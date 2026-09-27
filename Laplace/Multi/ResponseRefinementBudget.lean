/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseRefinementCompanions
import Laplace.Multi.PinskerObservable

/-!
# The global refinement information budget

Let `S_0, S_1, …` be a chain of feature families on the same space, each refining the previous
one (`hchain : ∀ k, Refines (S k) (S (k + 1)) ν`), and let `R_k = R^{S_k}_{m_k(D)}` be the level-`k`
entropy response of a data law `D` (`levelResponse`). The refinement ladder of
`ResponseFeatureRefinement` telescopes along the chain:

`KL(D ‖ R_0) = KL(D ‖ R_K) + Σ_{k<K} KL(R_{k+1} ‖ R_k)`   (`klDiv_levelResponse_telescope`),

the information carried by the data beyond the coarsest response is the sum of the informations
resolved by the successive refinements plus the information still invisible at level `K`. When
the finest family is saturated the last term vanishes
(`klDiv_levelResponse_telescope_of_spansAffine`), `KL(D ‖ R_0) = Σ_{k<K} KL(R_{k+1} ‖ R_k)`,
and the total information of the data is exactly the sum
of the refinement innovations. The remaining information is an observable certificate
(`sq_integral_sub_levelResponse_le`, `pinsker_budget`): for every bounded observable
`|E_D F − E_{R_K} F|² / (2 L²) ≤ KL(D ‖ R_K) = KL(D ‖ R_0) − Σ_{k<K} KL(R_{k+1} ‖ R_k)`, so the
unresolved information bounds the remaining observable error — a stopping criterion for refinement.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Chain

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : ℕ → Type*} [∀ k, Fintype (J k)]
  [∀ k, Nonempty (J k)] {S : (k : ℕ) → J k → X → ℝ} (hS : ∀ k j, Bdd (S k j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (D : Measure X) [IsProbabilityMeasure D]
include hS

/-- **The level-`k` response** of the data law: the entropy response of its `S_k`-mean. -/
noncomputable def levelResponse (k : ℕ) : Measure X :=
  responseProjection (hS k) ν (fun j ↦ ∫ x, S k j x ∂D)

variable (hchain : ∀ k, Refines (S k) (S (k + 1)) ν) (hDν : D ≪ ν)
include hchain hDν

/-- Finite rate propagates down the chain. -/
theorem genRate_level_ne_top_of_le {K : ℕ}
    (hK : genRate ν (S K) (fun j ↦ ∫ x, S K j x ∂D) ≠ ⊤) :
    ∀ k ≤ K, genRate ν (S k) (fun j ↦ ∫ x, S k j x ∂D) ≠ ⊤ := by
  induction K with
  | zero =>
    intro k hk
    rw [Nat.le_zero.1 hk]
    exact hK
  | succ K ih =>
    intro k hk
    have hK' := genRate_ne_top_of_refines (hS K) (hS (K + 1)) ν D hDν hK (hchain K)
    rcases Nat.le_succ_iff.1 hk with h | h
    · exact ih hK' k h
    · rw [h]
      exact hK

/-- **THE GLOBAL REFINEMENT BUDGET**: along a chain of refinements,
`KL(D ‖ R_0) = KL(D ‖ R_K) + Σ_{k<K} KL(R_{k+1} ‖ R_k)`. -/
theorem klDiv_levelResponse_telescope {K : ℕ}
    (hK : genRate ν (S K) (fun j ↦ ∫ x, S K j x ∂D) ≠ ⊤) :
    klDiv D (levelResponse hS ν D 0) =
      klDiv D (levelResponse hS ν D K) +
        ∑ k ∈ Finset.range K, klDiv (levelResponse hS ν D (k + 1)) (levelResponse hS ν D k) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hK' := genRate_ne_top_of_refines (hS K) (hS (K + 1)) ν D hDν hK (hchain K)
    rw [ih hK', Finset.sum_range_succ]
    have hlad := klDiv_data_responseProjection_refine (hS K) (hS (K + 1)) ν D hDν hK (hchain K)
    unfold levelResponse
    rw [hlad]
    ring

/-- **Saturation closes the budget**: when the finest family spans the bounded functions affinely,
`KL(D ‖ R_0) = Σ_{k<K} KL(R_{k+1} ‖ R_k)`. -/
theorem klDiv_levelResponse_telescope_of_spansAffine {K : ℕ} (hspan : SpansAffine (S K) ν)
    (hK : genRate ν (S K) (fun j ↦ ∫ x, S K j x ∂D) ≠ ⊤) :
    klDiv D (levelResponse hS ν D 0) =
      ∑ k ∈ Finset.range K, klDiv (levelResponse hS ν D (k + 1)) (levelResponse hS ν D k) := by
  rw [klDiv_levelResponse_telescope hS ν D hchain hDν hK]
  unfold levelResponse
  rw [responseProjection_eq_self_of_spansAffine (hS K) ν hspan D hDν hK, klDiv_self, zero_add]

omit [IsProbabilityMeasure D] hchain hDν in
/-- The level-`K` response is a probability law. -/
theorem isProbabilityMeasure_levelResponse {K : ℕ}
    (hK : genRate ν (S K) (fun j ↦ ∫ x, S K j x ∂D) ≠ ⊤) :
    IsProbabilityMeasure (levelResponse hS ν D K) :=
  (responseProjection_spec (hS K) ν hK).1

omit hchain hDν in
/-- **The observable certificate of the remaining information**: for `|F − c| ≤ L`,
`(E_D F − E_{R_K} F)² / (2 L²) ≤ KL(D ‖ R_K)`. -/
theorem sq_integral_sub_levelResponse_le {K : ℕ}
    (hK : genRate ν (S K) (fun j ↦ ∫ x, S K j x ∂D) ≠ ⊤) {F : X → ℝ} (hF : Bdd F) {c L : ℝ}
    (hL : 0 < L) (hFc : ∀ x, |F x - c| ≤ L) :
    ENNReal.ofReal (((∫ x, F x ∂D) - ∫ x, F x ∂levelResponse hS ν D K) ^ 2 / (2 * L ^ 2)) ≤
      klDiv D (levelResponse hS ν D K) := by
  have := isProbabilityMeasure_levelResponse hS ν D hK
  exact pinsker_observable D _ hF hL hFc

/-- **THE BUDGET AS A STOPPING CRITERION**: the observable error of the level-`K` response plus the
information already resolved by the refinements is at most the total information beyond the
coarsest level, `(E_D F − E_{R_K} F)²/(2L²) + Σ_{k<K} KL(R_{k+1} ‖ R_k) ≤ KL(D ‖ R_0)`. -/
theorem pinsker_budget {K : ℕ} (hK : genRate ν (S K) (fun j ↦ ∫ x, S K j x ∂D) ≠ ⊤)
    {F : X → ℝ} (hF : Bdd F) {c L : ℝ} (hL : 0 < L) (hFc : ∀ x, |F x - c| ≤ L) :
    ENNReal.ofReal (((∫ x, F x ∂D) - ∫ x, F x ∂levelResponse hS ν D K) ^ 2 / (2 * L ^ 2)) +
        ∑ k ∈ Finset.range K, klDiv (levelResponse hS ν D (k + 1)) (levelResponse hS ν D k) ≤
      klDiv D (levelResponse hS ν D 0) := by
  rw [klDiv_levelResponse_telescope hS ν D hchain hDν hK]
  exact add_le_add (sq_integral_sub_levelResponse_le hS ν D hK hF hL hFc) le_rfl

end Chain

end Laplace.Multi
