/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ProductChartLP

/-!
# The dual certificate of an active-truth face

The LP `min c·α` over `α ≥ 0`, `Q·α ≤ γ`, `κ·α ≥ δ` with both constraints active. A dual
certificate `(β, η)` with `β, η > 0` and nonnegative reduced costs `d_i = c_i − βκ_i + ηQ_i ≥ 0`
gives the identity `c·α − (βδ − ηγ) = β(κ·α − δ) + η(γ − Q·α) + ∑ d_i α_i` (`dual_identity`), every
term of which is nonnegative on the feasible set; hence, when the face
`{α ≥ 0 | κ·α = δ, Q·α = γ, α_i = 0 for d_i > 0}` is nonempty, it is exactly the optimal set and
the optimal value is `βδ − ηγ` (`lpOptimal_activeTruth_iff`). The LP of the degenerate-face
example (`DegenerateFace.lean`) is the instance `c = (1,1,3)`, `κ = (1,1,2)`, `Q = (1,1,1)`,
`γ = 2`, `δ = 3`, `β = 2`, `η = 1`: the optimal set is the segment `α₂ = 1, α₀ + α₁ = 1`
(`lpOptimal_deg_iff`). This is the LP half of the transverse active-truth face theorem (Astra,
round 7): the logarithmic exponent is the dimension of this face.
-/

open Finset

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- The dual identity of an active-truth certificate. -/
theorem dual_identity (Q κ c : ι → ℝ) (γ δ β η : ℝ) (α : ι → ℝ) :
    ∑ i, c i * α i - (β * δ - η * γ) =
      β * (∑ i, κ i * α i - δ) + η * (γ - ∑ i, Q i * α i) +
        ∑ i, (c i - β * κ i + η * Q i) * α i := by
  have e : ∑ i, (c i - β * κ i + η * Q i) * α i =
      ∑ i, c i * α i - β * ∑ i, κ i * α i + η * ∑ i, Q i * α i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e]
  ring

variable {Q κ c α : ι → ℝ} {γ δ β η : ℝ}

/-- **The optimal set of an active-truth face.** With a dual certificate `(β, η)`, `β, η > 0`,
nonnegative reduced costs and a nonempty face, the optimal points are exactly the nonnegative `α`
with both constraints active and vanishing on the coordinates of positive reduced cost. -/
theorem lpOptimal_activeTruth_iff (hβ : 0 < β) (hη : 0 < η)
    (hd : ∀ i, 0 ≤ c i - β * κ i + η * Q i)
    (hne : ∃ α₀ : ι → ℝ, (∀ i, 0 ≤ α₀ i) ∧ ∑ i, κ i * α₀ i = δ ∧ ∑ i, Q i * α₀ i = γ ∧
      ∀ i, 0 < c i - β * κ i + η * Q i → α₀ i = 0) :
    LPOptimal Q κ γ δ c α ↔ (∀ i, 0 ≤ α i) ∧ ∑ i, κ i * α i = δ ∧ ∑ i, Q i * α i = γ ∧
      ∀ i, 0 < c i - β * κ i + η * Q i → α i = 0 := by
  -- the value on the face
  have hface : ∀ α' : ι → ℝ, (∀ i, 0 ≤ α' i) → ∑ i, κ i * α' i = δ → ∑ i, Q i * α' i = γ →
      (∀ i, 0 < c i - β * κ i + η * Q i → α' i = 0) → ∑ i, c i * α' i = β * δ - η * γ := by
    intro α' _ hκ hQ h0
    have := dual_identity Q κ c γ δ β η α'
    rw [hκ, hQ, sub_self, sub_self, mul_zero, mul_zero, zero_add, zero_add] at this
    have hs : ∑ i, (c i - β * κ i + η * Q i) * α' i = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rcases (hd i).lt_or_eq with h | h
      · rw [h0 i h, mul_zero]
      · rw [← h, zero_mul]
    rw [hs] at this
    linarith
  -- the three nonnegative terms on the feasible set
  have hterms : ∀ α' : ι → ℝ, ConstrainedFeasible Q κ γ δ α' →
      0 ≤ β * (∑ i, κ i * α' i - δ) ∧ 0 ≤ η * (γ - ∑ i, Q i * α' i) ∧
        0 ≤ ∑ i, (c i - β * κ i + η * Q i) * α' i := fun α' ⟨h0, hQ, hκ⟩ ↦
    ⟨mul_nonneg hβ.le (sub_nonneg.mpr hκ), mul_nonneg hη.le (sub_nonneg.mpr hQ),
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (hd i) (h0 i)⟩
  obtain ⟨α₀, h₀0, h₀κ, h₀Q, h₀d⟩ := hne
  have hfeas₀ : ConstrainedFeasible Q κ γ δ α₀ := ⟨h₀0, h₀Q.le, h₀κ.ge⟩
  have hval₀ := hface α₀ h₀0 h₀κ h₀Q h₀d
  constructor
  · rintro ⟨hfeas, hopt⟩
    obtain ⟨h1, h2, h3⟩ := hterms α hfeas
    have hle : ∑ i, c i * α i ≤ β * δ - η * γ := hval₀ ▸ hopt α₀ hfeas₀
    have hid := dual_identity Q κ c γ δ β η α
    have hκα : ∑ i, κ i * α i = δ := by
      have : β * (∑ i, κ i * α i - δ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hβ.ne'
      · linarith
    have hQα : ∑ i, Q i * α i = γ := by
      have : η * (γ - ∑ i, Q i * α i) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hη.ne'
      · linarith
    have hsum : ∑ i, (c i - β * κ i + η * Q i) * α i = 0 := by linarith
    refine ⟨hfeas.1, hκα, hQα, fun i hi ↦ ?_⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_nonneg (hd i) (hfeas.1 i)).mp hsum i
      (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hi.ne'
    · exact h
  · rintro ⟨h0, hκα, hQα, hd0⟩
    refine ⟨⟨h0, hQα.le, hκα.ge⟩, fun α' hα' ↦ ?_⟩
    obtain ⟨h1, h2, h3⟩ := hterms α' hα'
    have hid := dual_identity Q κ c γ δ β η α'
    rw [hface α h0 hκα hQα hd0]
    linarith

/-- **The LP of the degenerate-face example**: the optimal set is the segment
`α₂ = 1, α₀ + α₁ = 1`. -/
theorem lpOptimal_deg_iff (α : Fin 3 → ℝ) :
    LPOptimal ![1, 1, 1] ![1, 1, 2] 2 3 ![1, 1, 3] α ↔
      (∀ i, 0 ≤ α i) ∧ α 2 = 1 ∧ α 0 + α 1 = 1 := by
  rw [lpOptimal_activeTruth_iff (β := 2) (η := 1) two_pos one_pos
    (by intro i; fin_cases i <;> norm_num)
    ⟨![1, 0, 1], by intro i; fin_cases i <;> norm_num,
      by simp [Fin.sum_univ_three]; norm_num, by simp [Fin.sum_univ_three]; norm_num,
      by intro i; fin_cases i <;> norm_num⟩]
  simp only [Fin.sum_univ_three, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    Matrix.cons_val_zero, one_mul, Matrix.cons_val_one, Matrix.cons_val, and_congr_right_iff]
  intro _
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith, fun i hi ↦ by fin_cases i <;> norm_num at hi⟩

end Laplace.Multi
