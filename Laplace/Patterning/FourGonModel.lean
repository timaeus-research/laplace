/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.FourGon

/-!
# The per-feature loss is the population reconstruction error

Equation *(featureloss)* of the working note *Patterning flow* defines the per-feature loss
`ℓ_i(W) = ⅓[(1 - |W_i|²)² + ∑_{j≠i} [W_j·W_i]_+²]`. Here we derive it from the model: for the
input `x e_i` with `x ~ U[0,1]`, the network `f(x) = ReLU(WᵀW x)` (no bias) has squared
reconstruction error `∑_a (x δ_{ai} - [x W_a·W_i]_+)² = x² · 3 ℓ_i(W)`, and integrating over
`x ∈ [0, 1]` gives `ℓ_i(W)`. This is the bias-free, single-feature-input case of the closed-form
TMS potential formalised in `timaeus-research/tms-lean` (`integral_tmsMeasure_sqLoss`).
-/

namespace Laplace.Patterning

open Finset

/-- The squared reconstruction error of `ReLU(WᵀW x e_i)` against the target `x e_i`. -/
noncomputable def reconError (W : Fin 5 → Fin 2 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  ∑ a, ((if a = i then x else 0) - relu (x * dot2 (W a) (W i))) ^ 2

lemma dot2_self (v : Fin 2 → ℝ) : dot2 v v = sqNorm v := by
  simp [dot2, sqNorm]
  ring

lemma sqNorm_nonneg (v : Fin 2 → ℝ) : 0 ≤ sqNorm v := by
  unfold sqNorm
  positivity

/-- For `x ≥ 0` the reconstruction error is `x²` times `3 ℓ_i(W)`. -/
theorem reconError_eq (W : Fin 5 → Fin 2 → ℝ) (i : Fin 5) {x : ℝ} (hx : 0 ≤ x) :
    reconError W i x = x ^ 2 * (3 * featureLoss W i) := by
  unfold reconError featureLoss
  have hterm : ∀ a, ((if a = i then x else 0) - relu (x * dot2 (W a) (W i))) ^ 2
      = (if a = i then x ^ 2 * (1 - sqNorm (W i)) ^ 2 else 0)
        + x ^ 2 * (if a = i then 0 else relu (dot2 (W a) (W i)) ^ 2) := by
    intro a
    by_cases hai : a = i
    · subst hai
      simp only [if_true, add_zero, mul_zero]
      rw [dot2_self, relu_of_nonneg (mul_nonneg hx (sqNorm_nonneg _))]
      ring
    · simp only [hai, if_false, zero_add, zero_sub, neg_sq]
      rw [relu_mul_of_nonneg hx]
      ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i),
    ← Finset.mul_sum]
  ring

/-- **Equation (featureloss) from the model.** `ℓ_i(W) = ∫₀¹ ‖x e_i - ReLU(WᵀW x e_i)‖² dx`. -/
theorem featureLoss_eq_integral (W : Fin 5 → Fin 2 → ℝ) (i : Fin 5) :
    featureLoss W i = ∫ x in (0 : ℝ)..1, reconError W i x := by
  have h : ∫ x in (0 : ℝ)..1, reconError W i x
      = ∫ x in (0 : ℝ)..1, x ^ 2 * (3 * featureLoss W i) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact reconError_eq W i hx.1
  rw [h, intervalIntegral.integral_mul_const, integral_pow]
  norm_num
  ring

end Laplace.Patterning
