/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.E2Matrix
import Laplace.Multi.OneLoopRotated

/-!
# The rotated oscillator is exactly its Taylor polynomial in the rotated tensors

The E2/E7 matrix-form theorems (`oneLoopCov_rot`, `covKFormula_rot`, `meanShift_rot`, …) take
`H = Q diag(λ) Qᵀ`, `rotT` and `rotQ` as the derivative tensors of E2's rotated oscillator at its
minimum `c`. This file certifies that reading in the seabed's Rosenbrock sense
(`rosenbrock_taylor_full`): the potential *is* the polynomial with these coefficient tensors,

`(L∘A)(c + v) = ½ vᵀHv + (1/6) ∑ᵢⱼₖ Tᵢⱼₖ vᵢvⱼvₖ + (1/24) ∑ᵢⱼₖₘ Q4ᵢⱼₖₘ vᵢvⱼvₖvₘ`
(`rotatedAnharmonic_taylor`), with `(L∘A)(c) = 0` (`rotatedAnharmonic_center`), and the tensors are
symmetric (`rotT_swap₁₂`, `rotT_swap₂₃`, `rotQ_swap₁₂`, `rotQ_swap₂₃`, `rotQ_swap₃₄`). So `H, T, Q4`
are the second, third and fourth derivatives of `L∘A` at `w* = c` in the note's eq:oneloop, eq:mean
and eq:covK.
-/

open Matrix

namespace Laplace.Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ}

/-! ### Symmetry of the rotated tensors -/

theorem rotT_swap₁₂ (Q : Matrix (Fin d) (Fin d) ℝ) (alpha : Fin d → ℝ) (i j k : Fin d) :
    rotT Q alpha i j k = rotT Q alpha j i k := by
  unfold rotT
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem rotT_swap₂₃ (Q : Matrix (Fin d) (Fin d) ℝ) (alpha : Fin d → ℝ) (i j k : Fin d) :
    rotT Q alpha i j k = rotT Q alpha i k j := by
  unfold rotT
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem rotQ_swap₁₂ (Q : Matrix (Fin d) (Fin d) ℝ) (gamma : Fin d → ℝ) (i j k m : Fin d) :
    rotQ Q gamma i j k m = rotQ Q gamma j i k m := by
  unfold rotQ
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem rotQ_swap₂₃ (Q : Matrix (Fin d) (Fin d) ℝ) (gamma : Fin d → ℝ) (i j k m : Fin d) :
    rotQ Q gamma i j k m = rotQ Q gamma i k j m := by
  unfold rotQ
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem rotQ_swap₃₄ (Q : Matrix (Fin d) (Fin d) ℝ) (gamma : Fin d → ℝ) (i j k m : Fin d) :
    rotQ Q gamma i j k m = rotQ Q gamma i j m k := by
  unfold rotQ
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ### The three forms in the eigen-coordinates `u = Qᵀv` -/

/-- `(Qᵀ v)ₗ = ∑ᵢ Qᵢₗ vᵢ`. -/
theorem transpose_mulVec_apply (Q : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (l : Fin d) :
    (Qᵀ *ᵥ v) l = ∑ i, Q i l * v i := by
  simp only [Matrix.mulVec, dotProduct, transpose_apply]

/-- `vᵀ (Q diag λ Qᵀ) v = ∑ₗ λₗ (Qᵀv)ₗ²`. -/
theorem quadratic_form_conj (hQ : Qᵀ * Q = 1) (lam v : Fin d → ℝ) :
    v ⬝ᵥ ((Q * diagonal lam * Qᵀ) *ᵥ v) = ∑ l, lam l * (∑ i, Q i l * v i) ^ 2 := by
  rw [conj_mulVec hQ, dotProduct_mulVec_eq]
  simp only [dotProduct, transpose_mulVec_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `∑ᵢⱼₖ Tᵢⱼₖ vᵢvⱼvₖ = ∑ₗ αₗ (Qᵀv)ₗ³`. -/
theorem rotT_cubic_form (Q : Matrix (Fin d) (Fin d) ℝ) (alpha v : Fin d → ℝ) :
    ∑ i, ∑ j, ∑ k, rotT Q alpha i j k * (v i * v j * v k) =
      ∑ p, alpha p * (∑ i, Q i p * v i) ^ 3 := by
  set u : Fin d → ℝ := fun p => ∑ i, Q i p * v i with hu
  clear_value u
  have hup : ∀ p, ∑ i, Q i p * v i = u p := fun p => by rw [hu]
  have hin : ∀ p, ∑ j, ∑ k, Q j p * (v j * v k) * Q k p = u p * u p := by
    intro p
    rw [← hup p, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have h1 : ∀ i, ∑ j, ∑ k, rotT Q alpha i j k * (v i * v j * v k) =
      ∑ p, alpha p * (u p * u p) * (Q i p * v i) := by
    intro i
    have e : ∑ j, ∑ k, rotT Q alpha i j k * (v i * v j * v k) =
        v i * ∑ j, ∑ k, rotT Q alpha i j k * (v j * v k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e, rotT_contract, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hin p]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, hup p]
  ring

/-- `∑ᵢⱼₖₘ Q4ᵢⱼₖₘ vᵢvⱼvₖvₘ = ∑ₗ γₗ (Qᵀv)ₗ⁴`. -/
theorem rotQ_quartic_form (Q : Matrix (Fin d) (Fin d) ℝ) (gamma v : Fin d → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ m, rotQ Q gamma i j k m * (v i * v j * v k * v m) =
      ∑ p, gamma p * (∑ i, Q i p * v i) ^ 4 := by
  set u : Fin d → ℝ := fun p => ∑ i, Q i p * v i with hu
  clear_value u
  have hup : ∀ p, ∑ i, Q i p * v i = u p := fun p => by rw [hu]
  have hin : ∀ p, ∑ k, ∑ m, Q k p * (v k * v m) * Q m p = u p * u p := by
    intro p
    rw [← hup p, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have h1 : ∀ i j, ∑ k, ∑ m, rotQ Q gamma i j k m * (v i * v j * v k * v m) =
      ∑ p, gamma p * (u p * u p) * (Q i p * v i) * (Q j p * v j) := by
    intro i j
    have e : ∑ k, ∑ m, rotQ Q gamma i j k m * (v i * v j * v k * v m) =
        v i * v j * ∑ k, ∑ m, rotQ Q gamma i j k m * (v k * v m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [e, rotQ_contract, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hin p]
    ring
  simp_rw [h1]
  rw [sum_comm3]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e3 : ∑ i, ∑ j, gamma p * (u p * u p) * (Q i p * v i) * (Q j p * v j) =
      gamma p * (u p * u p) * ((∑ i, Q i p * v i) * (∑ j, Q j p * v j)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun (i : Fin d) _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun (j : Fin d) _ => ?_
    ring
  rw [e3, hup p]
  ring

/-! ### The Taylor identity -/

theorem affineFrame_add (Q : Matrix (Fin d) (Fin d) ℝ) (c v : Fin d → ℝ) :
    affineFrame Q c (c + v) = Qᵀ *ᵥ v := by
  unfold affineFrame
  rw [add_sub_cancel_left]

/-- **The rotated oscillator is its Taylor polynomial in the rotated tensors**:
`(L∘A)(c + v) = ½ vᵀHv + (1/6)∑ Tᵢⱼₖ vᵢvⱼvₖ + (1/24)∑ Q4ᵢⱼₖₘ vᵢvⱼvₖvₘ`. -/
theorem rotatedAnharmonic_taylor (hQ : Qᵀ * Q = 1) (c lam alpha gamma v : Fin d → ℝ) :
    rotatedAnharmonic Q c lam alpha gamma (c + v) =
      1 / 2 * (v ⬝ᵥ ((Q * diagonal lam * Qᵀ) *ᵥ v)) +
        1 / 6 * ∑ i, ∑ j, ∑ k, rotT Q alpha i j k * (v i * v j * v k) +
        1 / 24 * ∑ i, ∑ j, ∑ k, ∑ m, rotQ Q gamma i j k m * (v i * v j * v k * v m) := by
  rw [quadratic_form_conj hQ, rotT_cubic_form, rotQ_quartic_form]
  simp only [rotatedAnharmonic, rotated, affineFrame_add, separableAnharmonic, separablePotential,
    OneD.anharmonicPotential, transpose_mulVec_apply]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- `(L∘A)(c) = 0`: the minimum value. -/
theorem rotatedAnharmonic_center (Q : Matrix (Fin d) (Fin d) ℝ) (c lam alpha gamma : Fin d → ℝ) :
    rotatedAnharmonic Q c lam alpha gamma c = 0 := by
  simp [rotatedAnharmonic, rotated, affineFrame, separableAnharmonic, separablePotential,
    OneD.anharmonicPotential]

end Laplace.Multi
