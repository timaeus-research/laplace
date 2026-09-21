/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.FourGon

/-!
# The 4-gon is a degenerate saddle of the full loss

Proposition 11.1 (v) of the working note *Patterning flow*: relaxing the alive features along
`W₀ = (1 - r²/4, -3r²/4)`, `W₁ = (-3r²/4, 1 - r²/4)`, `W₂ = (-1, -r²/4)`, `W₃ = (-r²/4, -1)`,
`W₄ = (r/√2)(1, 1)` gives, at uniform `h`,

  `L_h(W(r)) - L_h(4-gon) = -r⁴/15 + r⁶/15 + 103 r⁸/1920`   for `0 < r < 1`,

an exact polynomial (the note states `-r⁴/15 + O(r⁶)` and checked it numerically). For
`0 < r < 1/2` the right-hand side is negative, so the 4-gon is not a local minimum of the full
loss. On `0 < r < 1` the sign pattern of the twenty pairwise interferences is fixed, so every
ReLU is either the identity or zero and the loss is a polynomial in `r` and `√2`.
-/

namespace Laplace.Patterning

open Finset

/-- The descending path of Proposition 11.1 (v); `W₄ = (√2 r/2)(1, 1) = (r/√2)(1, 1)`. -/
noncomputable def saddlePath (r : ℝ) : Fin 5 → Fin 2 → ℝ :=
  ![![1 - r ^ 2 / 4, -(3 * r ^ 2 / 4)], ![-(3 * r ^ 2 / 4), 1 - r ^ 2 / 4],
    ![-1, -(r ^ 2 / 4)], ![-(r ^ 2 / 4), -1],
    ![Real.sqrt 2 * r / 2, Real.sqrt 2 * r / 2]]

lemma sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma saddle_r2_lt {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : r ^ 2 < 1 := by nlinarith

lemma saddle_r4_lt {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : r ^ 4 < 1 := by
  nlinarith [saddle_r2_lt hr0 hr1]

lemma sqNorm_saddlePath_0 (r : ℝ) : sqNorm (saddlePath r 0) = 1 - r ^ 2 / 2 + 5 * r ^ 4 / 8 := by
  simp [saddlePath, sqNorm]
  ring

lemma sqNorm_saddlePath_1 (r : ℝ) : sqNorm (saddlePath r 1) = 1 - r ^ 2 / 2 + 5 * r ^ 4 / 8 := by
  simp [saddlePath, sqNorm]
  ring

lemma sqNorm_saddlePath_2 (r : ℝ) : sqNorm (saddlePath r 2) = 1 + r ^ 4 / 16 := by
  simp [saddlePath, sqNorm]
  ring

lemma sqNorm_saddlePath_3 (r : ℝ) : sqNorm (saddlePath r 3) = 1 + r ^ 4 / 16 := by
  simp [saddlePath, sqNorm]
  ring

lemma sqNorm_saddlePath_4 (r : ℝ) : sqNorm (saddlePath r 4) = r ^ 2 := by
  simp [saddlePath, sqNorm]
  linear_combination (r ^ 2 / 2) * sqrt_two_sq

lemma dot2_saddlePath_1_0 (r : ℝ) : dot2 (saddlePath r 1) (saddlePath r 0) = -(3 * r ^ 2 * (4 - r ^ 2) / 8) := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_0_1 (r : ℝ) : dot2 (saddlePath r 0) (saddlePath r 1) = -(3 * r ^ 2 * (4 - r ^ 2) / 8) := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_2_0 (r : ℝ) : dot2 (saddlePath r 2) (saddlePath r 0) = (3 * r ^ 4 + 4 * r ^ 2 - 16) / 16 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_0_2 (r : ℝ) : dot2 (saddlePath r 0) (saddlePath r 2) = (3 * r ^ 4 + 4 * r ^ 2 - 16) / 16 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_3_1 (r : ℝ) : dot2 (saddlePath r 3) (saddlePath r 1) = (3 * r ^ 4 + 4 * r ^ 2 - 16) / 16 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_1_3 (r : ℝ) : dot2 (saddlePath r 1) (saddlePath r 3) = (3 * r ^ 4 + 4 * r ^ 2 - 16) / 16 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_3_0 (r : ℝ) : dot2 (saddlePath r 3) (saddlePath r 0) = r ^ 2 * (r ^ 2 + 8) / 16 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_0_3 (r : ℝ) : dot2 (saddlePath r 0) (saddlePath r 3) = r ^ 2 * (r ^ 2 + 8) / 16 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_2_1 (r : ℝ) : dot2 (saddlePath r 2) (saddlePath r 1) = r ^ 2 * (r ^ 2 + 8) / 16 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_1_2 (r : ℝ) : dot2 (saddlePath r 1) (saddlePath r 2) = r ^ 2 * (r ^ 2 + 8) / 16 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_3_2 (r : ℝ) : dot2 (saddlePath r 3) (saddlePath r 2) = r ^ 2 / 2 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_2_3 (r : ℝ) : dot2 (saddlePath r 2) (saddlePath r 3) = r ^ 2 / 2 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_4_0 (r : ℝ) : dot2 (saddlePath r 4) (saddlePath r 0) = Real.sqrt 2 * r * (1 - r ^ 2) / 2 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_0_4 (r : ℝ) : dot2 (saddlePath r 0) (saddlePath r 4) = Real.sqrt 2 * r * (1 - r ^ 2) / 2 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_4_1 (r : ℝ) : dot2 (saddlePath r 4) (saddlePath r 1) = Real.sqrt 2 * r * (1 - r ^ 2) / 2 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_1_4 (r : ℝ) : dot2 (saddlePath r 1) (saddlePath r 4) = Real.sqrt 2 * r * (1 - r ^ 2) / 2 := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_4_2 (r : ℝ) : dot2 (saddlePath r 4) (saddlePath r 2) = -(Real.sqrt 2 * r * (r ^ 2 + 4) / 8) := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_2_4 (r : ℝ) : dot2 (saddlePath r 2) (saddlePath r 4) = -(Real.sqrt 2 * r * (r ^ 2 + 4) / 8) := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_4_3 (r : ℝ) : dot2 (saddlePath r 4) (saddlePath r 3) = -(Real.sqrt 2 * r * (r ^ 2 + 4) / 8) := by
  simp [saddlePath, dot2]
  ring

lemma dot2_saddlePath_3_4 (r : ℝ) : dot2 (saddlePath r 3) (saddlePath r 4) = -(Real.sqrt 2 * r * (r ^ 2 + 4) / 8) := by
  simp [saddlePath, dot2]
  ring

lemma reluSq_saddlePath_1_0 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 1) (saddlePath r 0)) ^ 2 = 0 := by
  have h4 : 0 ≤ 4 - r ^ 2 := by nlinarith
  rw [dot2_saddlePath_1_0, relu_of_nonpos (neg_nonpos.mpr (div_nonneg (mul_nonneg (by positivity) h4) (by norm_num)))]
  ring

lemma reluSq_saddlePath_0_1 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 0) (saddlePath r 1)) ^ 2 = 0 := by
  have h4 : 0 ≤ 4 - r ^ 2 := by nlinarith
  rw [dot2_saddlePath_0_1, relu_of_nonpos (neg_nonpos.mpr (div_nonneg (mul_nonneg (by positivity) h4) (by norm_num)))]
  ring

lemma reluSq_saddlePath_2_0 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 2) (saddlePath r 0)) ^ 2 = 0 := by
  have h2 := saddle_r2_lt hr0 hr1
  have h4 := saddle_r4_lt hr0 hr1
  rw [dot2_saddlePath_2_0, relu_of_nonpos (by linarith)]
  ring

lemma reluSq_saddlePath_0_2 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 0) (saddlePath r 2)) ^ 2 = 0 := by
  have h2 := saddle_r2_lt hr0 hr1
  have h4 := saddle_r4_lt hr0 hr1
  rw [dot2_saddlePath_0_2, relu_of_nonpos (by linarith)]
  ring

lemma reluSq_saddlePath_3_1 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 3) (saddlePath r 1)) ^ 2 = 0 := by
  have h2 := saddle_r2_lt hr0 hr1
  have h4 := saddle_r4_lt hr0 hr1
  rw [dot2_saddlePath_3_1, relu_of_nonpos (by linarith)]
  ring

lemma reluSq_saddlePath_1_3 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 1) (saddlePath r 3)) ^ 2 = 0 := by
  have h2 := saddle_r2_lt hr0 hr1
  have h4 := saddle_r4_lt hr0 hr1
  rw [dot2_saddlePath_1_3, relu_of_nonpos (by linarith)]
  ring

lemma reluSq_saddlePath_3_0 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 3) (saddlePath r 0)) ^ 2 = (r ^ 2 * (r ^ 2 + 8) / 16) ^ 2 := by
  rw [dot2_saddlePath_3_0, relu_of_nonneg (by positivity)]


lemma reluSq_saddlePath_0_3 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 0) (saddlePath r 3)) ^ 2 = (r ^ 2 * (r ^ 2 + 8) / 16) ^ 2 := by
  rw [dot2_saddlePath_0_3, relu_of_nonneg (by positivity)]


lemma reluSq_saddlePath_2_1 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 2) (saddlePath r 1)) ^ 2 = (r ^ 2 * (r ^ 2 + 8) / 16) ^ 2 := by
  rw [dot2_saddlePath_2_1, relu_of_nonneg (by positivity)]


lemma reluSq_saddlePath_1_2 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 1) (saddlePath r 2)) ^ 2 = (r ^ 2 * (r ^ 2 + 8) / 16) ^ 2 := by
  rw [dot2_saddlePath_1_2, relu_of_nonneg (by positivity)]


lemma reluSq_saddlePath_3_2 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 3) (saddlePath r 2)) ^ 2 = (r ^ 2 / 2) ^ 2 := by
  rw [dot2_saddlePath_3_2, relu_of_nonneg (by positivity)]


lemma reluSq_saddlePath_2_3 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 2) (saddlePath r 3)) ^ 2 = (r ^ 2 / 2) ^ 2 := by
  rw [dot2_saddlePath_2_3, relu_of_nonneg (by positivity)]


lemma reluSq_saddlePath_4_0 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 4) (saddlePath r 0)) ^ 2 = r ^ 2 * (1 - r ^ 2) ^ 2 / 2 := by
  have h1 : 0 ≤ 1 - r ^ 2 := by nlinarith
  rw [dot2_saddlePath_4_0, relu_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hr0.le) h1) (by norm_num))]
  linear_combination (r ^ 2 * (1 - r ^ 2) ^ 2 / 4) * sqrt_two_sq

lemma reluSq_saddlePath_0_4 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 0) (saddlePath r 4)) ^ 2 = r ^ 2 * (1 - r ^ 2) ^ 2 / 2 := by
  have h1 : 0 ≤ 1 - r ^ 2 := by nlinarith
  rw [dot2_saddlePath_0_4, relu_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hr0.le) h1) (by norm_num))]
  linear_combination (r ^ 2 * (1 - r ^ 2) ^ 2 / 4) * sqrt_two_sq

lemma reluSq_saddlePath_4_1 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 4) (saddlePath r 1)) ^ 2 = r ^ 2 * (1 - r ^ 2) ^ 2 / 2 := by
  have h1 : 0 ≤ 1 - r ^ 2 := by nlinarith
  rw [dot2_saddlePath_4_1, relu_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hr0.le) h1) (by norm_num))]
  linear_combination (r ^ 2 * (1 - r ^ 2) ^ 2 / 4) * sqrt_two_sq

lemma reluSq_saddlePath_1_4 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 1) (saddlePath r 4)) ^ 2 = r ^ 2 * (1 - r ^ 2) ^ 2 / 2 := by
  have h1 : 0 ≤ 1 - r ^ 2 := by nlinarith
  rw [dot2_saddlePath_1_4, relu_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hr0.le) h1) (by norm_num))]
  linear_combination (r ^ 2 * (1 - r ^ 2) ^ 2 / 4) * sqrt_two_sq

lemma reluSq_saddlePath_4_2 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 4) (saddlePath r 2)) ^ 2 = 0 := by
  rw [dot2_saddlePath_4_2, relu_of_nonpos (neg_nonpos.mpr (by positivity))]
  ring

lemma reluSq_saddlePath_2_4 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 2) (saddlePath r 4)) ^ 2 = 0 := by
  rw [dot2_saddlePath_2_4, relu_of_nonpos (neg_nonpos.mpr (by positivity))]
  ring

lemma reluSq_saddlePath_4_3 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 4) (saddlePath r 3)) ^ 2 = 0 := by
  rw [dot2_saddlePath_4_3, relu_of_nonpos (neg_nonpos.mpr (by positivity))]
  ring

lemma reluSq_saddlePath_3_4 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    relu (dot2 (saddlePath r 3) (saddlePath r 4)) ^ 2 = 0 := by
  rw [dot2_saddlePath_3_4, relu_of_nonpos (neg_nonpos.mpr (by positivity))]
  ring

lemma featureLoss_saddlePath_0 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    featureLoss (saddlePath r) 0 = 101*r^8/768 - r^6/48 - r^4/6 + r^2/6 := by
  simp only [featureLoss, Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  rw [sqNorm_saddlePath_0, reluSq_saddlePath_1_0 hr0 hr1, reluSq_saddlePath_2_0 hr0 hr1, reluSq_saddlePath_3_0 hr0 hr1, reluSq_saddlePath_4_0 hr0 hr1]
  ring

lemma featureLoss_saddlePath_1 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    featureLoss (saddlePath r) 1 = 101*r^8/768 - r^6/48 - r^4/6 + r^2/6 := by
  simp only [featureLoss, Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  rw [sqNorm_saddlePath_1, reluSq_saddlePath_0_1 hr0 hr1, reluSq_saddlePath_2_1 hr0 hr1, reluSq_saddlePath_3_1 hr0 hr1, reluSq_saddlePath_4_1 hr0 hr1]
  ring

lemma featureLoss_saddlePath_2 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    featureLoss (saddlePath r) 2 = r^8/384 + r^6/48 + r^4/6 := by
  simp only [featureLoss, Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  rw [sqNorm_saddlePath_2, reluSq_saddlePath_0_2 hr0 hr1, reluSq_saddlePath_1_2 hr0 hr1, reluSq_saddlePath_3_2 hr0 hr1, reluSq_saddlePath_4_2 hr0 hr1]
  ring

lemma featureLoss_saddlePath_3 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    featureLoss (saddlePath r) 3 = r^8/384 + r^6/48 + r^4/6 := by
  simp only [featureLoss, Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  rw [sqNorm_saddlePath_3, reluSq_saddlePath_0_3 hr0 hr1, reluSq_saddlePath_1_3 hr0 hr1, reluSq_saddlePath_2_3 hr0 hr1, reluSq_saddlePath_4_3 hr0 hr1]
  ring

lemma featureLoss_saddlePath_4 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    featureLoss (saddlePath r) 4 = r^6/3 - r^4/3 - r^2/3 + 1/3 := by
  simp only [featureLoss, Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  rw [sqNorm_saddlePath_4, reluSq_saddlePath_0_4 hr0 hr1, reluSq_saddlePath_1_4 hr0 hr1, reluSq_saddlePath_2_4 hr0 hr1, reluSq_saddlePath_3_4 hr0 hr1]
  ring

/-- **Proposition 11.1 (v), exact form.** Along the descending path, at uniform `h`,
`L_h(W(r)) - L_h(4-gon) = -r⁴/15 + r⁶/15 + 103 r⁸/1920` for `0 < r < 1`. -/
theorem weightedLoss_saddlePath {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    weightedLoss (fun _ => 1 / 5) (saddlePath r) - weightedLoss (fun _ => 1 / 5) (fourGon 0 0)
      = -(r ^ 4 / 15) + r ^ 6 / 15 + 103 * r ^ 8 / 1920 := by
  simp only [weightedLoss, Fin.sum_univ_five, featureLoss_fourGon_0, featureLoss_fourGon_1,
    featureLoss_fourGon_2, featureLoss_fourGon_3, featureLoss_fourGon_4, neg_zero, relu_zero,
    featureLoss_saddlePath_0 hr0 hr1, featureLoss_saddlePath_1 hr0 hr1,
    featureLoss_saddlePath_2 hr0 hr1, featureLoss_saddlePath_3 hr0 hr1,
    featureLoss_saddlePath_4 hr0 hr1]
  ring

/-- **The 4-gon is not a local minimum of the full loss**: the path descends for `0 < r < 1/2`. -/
theorem saddlePath_descends {r : ℝ} (hr0 : 0 < r) (hr : r < 1 / 2) :
    weightedLoss (fun _ => 1 / 5) (saddlePath r) < weightedLoss (fun _ => 1 / 5) (fourGon 0 0) := by
  have hr1 : r < 1 := by linarith
  have h := weightedLoss_saddlePath hr0 hr1
  have hr2 : r ^ 2 < 1 / 4 := by nlinarith
  have hr4 : 0 < r ^ 4 := by positivity
  have hr4' : r ^ 4 < 1 / 16 := by nlinarith
  have hneg : -(r ^ 4 / 15) + r ^ 6 / 15 + 103 * r ^ 8 / 1920 < 0 := by
    have : r ^ 6 = r ^ 4 * r ^ 2 := by ring
    have : r ^ 8 = r ^ 4 * r ^ 4 := by ring
    nlinarith
  linarith

end Laplace.Patterning
