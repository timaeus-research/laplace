/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib

/-!
# Bounded positive reweighting: the sublevel-set core

The sublevel-set core of Proposition 6.1 of the working note *Patterning flow*: for
nonnegative per-sample excess losses `K_i` and weights `w_i ∈ [c₁, c₂]` with `c₁ > 0`, the
reweighted mean `K_w = (1/n) ∑ w_i K_i` is sandwiched, `c₁ K ≤ K_w ≤ c₂ K`, its zero set
equals that of `K`, and its sublevel sets (hence their volumes) are sandwiched between
sublevel sets of `K` at rescaled levels. The learning-coefficient conclusion of the note
(the volume asymptotics of real analytic functions) is not formalised here.
-/

namespace Laplace.Patterning

open Finset MeasureTheory Set

variable {W ν : Type*} [Fintype ν]

noncomputable section

/-- The mean loss `K = (1/n) ∑ K_i`. -/
def meanLoss (K : ν → W → ℝ) (x : W) : ℝ := (1 / (Fintype.card ν : ℝ)) * ∑ i, K i x

/-- The reweighted loss `K_w = (1/n) ∑ w_i K_i`. -/
def reweighted (K : ν → W → ℝ) (w : ν → ℝ) (x : W) : ℝ :=
  (1 / (Fintype.card ν : ℝ)) * ∑ i, w i * K i x

lemma meanLoss_nonneg (K : ν → W → ℝ) (hK : ∀ i x, 0 ≤ K i x) (x : W) : 0 ≤ meanLoss K x := by
  unfold meanLoss
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hK i x)

/-- **Pointwise sandwich.** `c₁ K ≤ K_w ≤ c₂ K` for nonnegative `K_i` and `w_i ∈ [c₁, c₂]`. -/
theorem reweighted_sandwich (K : ν → W → ℝ) (w : ν → ℝ) (c₁ c₂ : ℝ)
    (hK : ∀ i x, 0 ≤ K i x) (hw : ∀ i, c₁ ≤ w i ∧ w i ≤ c₂) (x : W) :
    c₁ * meanLoss K x ≤ reweighted K w x ∧ reweighted K w x ≤ c₂ * meanLoss K x := by
  unfold reweighted meanLoss
  have hn : (0 : ℝ) ≤ 1 / (Fintype.card ν : ℝ) := by positivity
  constructor
  · rw [mul_left_comm, Finset.mul_sum (f := fun i => K i x)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i).1 (hK i x)) hn
  · rw [mul_left_comm, Finset.mul_sum (f := fun i => K i x)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i).2 (hK i x)) hn

/-- The zero set of `K` is the common zero set of the `K_i` (samplewise interpolation). -/
theorem meanLoss_eq_zero_iff [Nonempty ν] (K : ν → W → ℝ) (hK : ∀ i x, 0 ≤ K i x) (x : W) :
    meanLoss K x = 0 ↔ ∀ i, K i x = 0 := by
  unfold meanLoss
  have hn : (1 / (Fintype.card ν : ℝ)) ≠ 0 := by positivity
  rw [mul_eq_zero, or_iff_right hn, Finset.sum_eq_zero_iff_of_nonneg fun i _ => hK i x]
  simp

/-- **Zero sets agree.** With `c₁ > 0`, `K_w(x) = 0 ↔ K(x) = 0`. -/
theorem reweighted_eq_zero_iff (K : ν → W → ℝ) (w : ν → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hK : ∀ i x, 0 ≤ K i x) (hw : ∀ i, c₁ ≤ w i ∧ w i ≤ c₂) (x : W) :
    reweighted K w x = 0 ↔ meanLoss K x = 0 := by
  obtain ⟨h₁, h₂⟩ := reweighted_sandwich K w c₁ c₂ hK hw x
  have h0 := meanLoss_nonneg K hK x
  constructor
  · intro h
    rw [h] at h₁
    nlinarith
  · intro h
    rw [h, mul_zero] at h₁ h₂
    linarith

/-- **Sublevel sandwich.** `{K < ε/c₂} ⊆ {K_w < ε} ⊆ {K < ε/c₁}`. -/
theorem reweighted_sublevel_sandwich (K : ν → W → ℝ) (w : ν → ℝ) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hK : ∀ i x, 0 ≤ K i x) (hw : ∀ i, c₁ ≤ w i ∧ w i ≤ c₂) (ε : ℝ) :
    {x | meanLoss K x < ε / c₂} ⊆ {x | reweighted K w x < ε} ∧
      {x | reweighted K w x < ε} ⊆ {x | meanLoss K x < ε / c₁} := by
  constructor
  · intro x hx
    have h := (reweighted_sandwich K w c₁ c₂ hK hw x).2
    have hx' : c₂ * meanLoss K x < ε := by
      rw [Set.mem_ofPred_eq, lt_div_iff₀ hc₂] at hx
      linarith
    exact lt_of_le_of_lt h hx'
  · intro x hx
    have h := (reweighted_sandwich K w c₁ c₂ hK hw x).1
    rw [Set.mem_ofPred_eq, lt_div_iff₀ hc₁]
    rw [Set.mem_ofPred_eq] at hx
    linarith

/-- **Volume sandwich.** For any measure, `μ{K < ε/c₂} ≤ μ{K_w < ε} ≤ μ{K < ε/c₁}`. -/
theorem reweighted_volume_sandwich {m : MeasurableSpace W} (μ : Measure W)
    (K : ν → W → ℝ) (w : ν → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hK : ∀ i x, 0 ≤ K i x) (hw : ∀ i, c₁ ≤ w i ∧ w i ≤ c₂) (ε : ℝ) :
    μ {x | meanLoss K x < ε / c₂} ≤ μ {x | reweighted K w x < ε} ∧
      μ {x | reweighted K w x < ε} ≤ μ {x | meanLoss K x < ε / c₁} :=
  ⟨measure_mono (reweighted_sublevel_sandwich K w c₁ c₂ hc₁ hc₂ hK hw ε).1,
    measure_mono (reweighted_sublevel_sandwich K w c₁ c₂ hc₁ hc₂ hK hw ε).2⟩

end

end Laplace.Patterning
