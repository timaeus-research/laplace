/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.HalfspaceChernoff

/-!
# The compact-cover Cramér upper bound

The halfspace Chernoff bound extends to finite unions of halfspaces with the union-bound prefactor
(`finite_union_chernoff`), and by compactness to any compact set `F` of responses every point of
which has a **dual witness** `θ` with `θ·x − Λ_ν(θ) > α` (that is, `I(x) > α` for the Cramér rate
`I = Λ_ν^*`): there is `N` with

`P(R̄_n ∈ F) ≤ N e^{−nα}` for every `n ≥ 1`   (`compact_cover_chernoff`).

This is the finite-`n` form of Cramér's upper bound: the exponential decay rate of the probability
that the empirical feature mean lands in `F` is at least `α` whenever `α < inf_F I`, with the
number of halfspaces in the cover as the only prefactor. The closed-set version without the
prefactor is false at finite `n`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]

section

variable (ν : Measure X) [IsProbabilityMeasure ν] {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hR

/-- The halfspace Chernoff bound with unit multiplier: `P(θ·R̄_n ≥ c) ≤ exp(−n(c − Λ_ν(θ)))`. -/
theorem halfspace_chernoff_one (θ : ι → ℝ) (c : ℝ) {n : ℕ} (hn : 0 < n) :
    (Measure.pi fun _ : Fin n ↦ ν).real {x | c ≤ ∑ i, θ i * empMean R n x i} ≤
      Real.exp (-(n * (c - featCgf ν R θ))) := by
  have := halfspace_chernoff ν hR θ c hn (lam := 1) zero_le_one
  simpa using this

/-- **Finite-union Chernoff**: `P(R̄_n ∈ ⋃ₖ {θₖ·x ≥ cₖ}) ≤ ∑ₖ e^{−n(cₖ − Λ_ν(θₖ))}`. -/
theorem finite_union_chernoff {κ : Type*} (s : Finset κ) (θ : κ → ι → ℝ) (c : κ → ℝ) {n : ℕ}
    (hn : 0 < n) :
    (Measure.pi fun _ : Fin n ↦ ν).real
        {x | empMean R n x ∈ ⋃ k ∈ s, {y : ι → ℝ | c k ≤ ∑ i, θ k i * y i}} ≤
      ∑ k ∈ s, Real.exp (-(n * (c k - featCgf ν R (θ k)))) := by
  have hset : {x : Fin n → X | empMean R n x ∈ ⋃ k ∈ s, {y : ι → ℝ | c k ≤ ∑ i, θ k i * y i}} =
      ⋃ k ∈ s, {x | c k ≤ ∑ i, θ k i * empMean R n x i} := by
    ext x
    simp
  rw [hset]
  exact (measureReal_biUnion_finset_le s _).trans
    (Finset.sum_le_sum fun k _ ↦ halfspace_chernoff_one ν hR (θ k) (c k) hn)

/-- **The compact-cover Cramér upper bound**: if every point of the compact set `F` has a dual
witness `θ` with `θ·x − Λ_ν(θ) > α`, then `P(R̄_n ∈ F) ≤ N e^{−nα}` for all `n ≥ 1`, with `N` the
number of halfspaces in a finite cover of `F`. -/
theorem compact_cover_chernoff {F : Set (ι → ℝ)} (hF : IsCompact F) {α : ℝ}
    (hwit : ∀ x ∈ F, ∃ θ : ι → ℝ, α < ∑ i, θ i * x i - featCgf ν R θ) :
    ∃ N : ℕ, ∀ n : ℕ, 0 < n →
      (Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F} ≤ N * Real.exp (-(n * α)) := by
  classical
  have hwit' : ∀ x : ι → ℝ, ∃ θ : ι → ℝ, x ∈ F → α < ∑ i, θ i * x i - featCgf ν R θ := by
    intro x
    by_cases hx : x ∈ F
    · obtain ⟨θ, h⟩ := hwit x hx
      exact ⟨θ, fun _ ↦ h⟩
    · exact ⟨0, fun h ↦ absurd h hx⟩
  choose θ hθ using hwit'
  -- the open cover by strict halfspaces
  set U : (ι → ℝ) → Set (ι → ℝ) := fun x ↦
    {y | α + featCgf ν R (θ x) < ∑ i, θ x i * y i} with hU
  have hUo : ∀ x, IsOpen (U x) := fun x ↦
    isOpen_lt continuous_const (continuous_finsetSum _ fun i _ ↦ continuous_const.mul
      (continuous_apply i))
  have hcov : F ⊆ ⋃ x, U x := fun x hx ↦ Set.mem_iUnion.2 ⟨x, by
    simp only [hU, Set.mem_ofPred_eq]
    linarith [hθ x hx]⟩
  obtain ⟨t, ht⟩ := hF.elim_finite_subcover U hUo hcov
  refine ⟨t.card, fun n hn ↦ ?_⟩
  have hsub : {x : Fin n → X | empMean R n x ∈ F} ⊆
      {x | empMean R n x ∈ ⋃ k ∈ t, {y : ι → ℝ | α + featCgf ν R (θ k) ≤ ∑ i, θ k i * y i}} := by
    intro x hx
    have hmem := ht hx
    simp only [hU, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hmem ⊢
    obtain ⟨k, hk, hlt⟩ := hmem
    exact ⟨k, hk, hlt.le⟩
  calc (Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F}
      ≤ (Measure.pi fun _ : Fin n ↦ ν).real
          {x | empMean R n x ∈ ⋃ k ∈ t, {y : ι → ℝ | α + featCgf ν R (θ k) ≤ ∑ i, θ k i * y i}} :=
        measureReal_mono hsub
    _ ≤ ∑ k ∈ t, Real.exp (-(n * ((α + featCgf ν R (θ k)) - featCgf ν R (θ k)))) :=
        finite_union_chernoff ν hR t θ (fun k ↦ α + featCgf ν R (θ k)) hn
    _ = t.card * Real.exp (-(n * α)) := by
        simp only [add_sub_cancel_right, Finset.sum_const, nsmul_eq_mul]

end

end Laplace.Multi
