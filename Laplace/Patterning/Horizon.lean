/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib

/-!
# The finite-horizon response of gradient descent to a constant force

Formalises Proposition 3.1 of the working note *Patterning flow* (learning-theory/local/directsgld):
gradient descent from a minimizer under an additive constant force realizes, to first order, the
displacement `-(ε η) F_T(H) b` with the spectral filter `F_T(λ) = (1 - (1 - ηλ)^T)/λ`, and `η T`
on the null space.

* `horizonIter H η c b` is one step of the linearized recursion `δ ↦ (1 - η H) δ - c • b`.
* `horizon_iterate_zero` : the `T`-th iterate from `0` is `-(c • (∑_{k<T} (1 - ηH)^k)) b`.
* `horizonFilter_mulVec_eigen` : on an eigenvector `H v = λ v` with `λ ≠ 0` the filter acts as
  `(1 - (1 - ηλ)^T)/λ`; on a null vector it acts as `η T` (`horizonFilter_mulVec_null`).
-/

namespace Laplace.Patterning

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-- One linearized gradient-descent step under a constant force: `δ ↦ (1 - η H) δ - c • b`. -/
def horizonIter (H : Matrix ι ι ℝ) (η c : ℝ) (b : ι → ℝ) (δ : ι → ℝ) : ι → ℝ :=
  (1 - η • H).mulVec δ - c • b

/-- The finite-horizon filter `F_T(H) = η ∑_{k<T} (1 - η H)^k`. -/
def horizonFilter (H : Matrix ι ι ℝ) (η : ℝ) (T : ℕ) : Matrix ι ι ℝ :=
  η • ∑ k ∈ range T, (1 - η • H) ^ k

/-- **Finite-horizon response.** The `T`-th iterate from `δ_0 = 0` is `-(c • ∑_{k<T} A^k) b`
with `A = 1 - η H`. -/
theorem horizon_iterate_zero (H : Matrix ι ι ℝ) (η c : ℝ) (b : ι → ℝ) (T : ℕ) :
    (horizonIter H η c b)^[T] 0 = -(c • (∑ k ∈ range T, (1 - η • H) ^ k).mulVec b) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [horizonIter, Finset.sum_range_succ', pow_zero, pow_succ', Matrix.sum_mulVec,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_neg, Matrix.mulVec_smul,
      Matrix.mulVec_sum, Matrix.mulVec_mulVec, smul_add, neg_add, sub_eq_add_neg]

/-- The displacement after `T` steps equals `-(c/η) • F_T(H) b`, i.e. `-(ε η) F_T b/η`; stated in
the note's normalization `c = ε η`: `δ_T = -ε • F_T(H) b`. -/
theorem horizon_iterate_zero_filter (H : Matrix ι ι ℝ) (η ε : ℝ) (b : ι → ℝ) (T : ℕ) :
    (horizonIter H η (ε * η) b)^[T] 0 = -(ε • (horizonFilter H η T).mulVec b) := by
  rw [horizon_iterate_zero, horizonFilter, Matrix.smul_mulVec, smul_smul, mul_comm]

/-- On an eigenvector `H v = λ v`, `(1 - ηH)^k v = (1 - ηλ)^k v`. -/
lemma pow_one_sub_smul_mulVec_eigen (H : Matrix ι ι ℝ) (η lam : ℝ) (v : ι → ℝ)
    (hv : H.mulVec v = lam • v) (k : ℕ) :
    ((1 - η • H) ^ k).mulVec v = (1 - η * lam) ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec, hv, pow_succ']
    simp only [smul_sub, smul_smul]
    rw [← sub_smul]
    congr 1
    ring

/-- Scalar form of the filter: `η ∑_{k<T} (1 - ηλ)^k = (1 - (1 - ηλ)^T)/λ` for `λ ≠ 0`
(including `η = 0`, where both sides vanish). -/
lemma horizonFilter_scalar (η lam : ℝ) (hlam : lam ≠ 0) (T : ℕ) :
    η * ∑ k ∈ range T, (1 - η * lam) ^ k = (1 - (1 - η * lam) ^ T) / lam := by
  rcases eq_or_ne η 0 with hη | hη
  · subst hη; simp
  · have hx : (1 - η * lam) ≠ 1 := by
      intro h
      exact mul_ne_zero hη hlam (by linarith)
    rw [geom_sum_eq hx]
    field_simp
    ring

/-- **Eigen-form of the filter.** For `H v = λ v` with `λ ≠ 0`,
`F_T(H) v = ((1 - (1 - ηλ)^T)/λ) • v`. -/
theorem horizonFilter_mulVec_eigen (H : Matrix ι ι ℝ) (η lam : ℝ) (v : ι → ℝ)
    (hv : H.mulVec v = lam • v) (hlam : lam ≠ 0) (T : ℕ) :
    (horizonFilter H η T).mulVec v = ((1 - (1 - η * lam) ^ T) / lam) • v := by
  unfold horizonFilter
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [pow_one_sub_smul_mulVec_eigen H η lam v hv]
  rw [← Finset.sum_smul, smul_smul, horizonFilter_scalar η lam hlam]

/-- **Null-space form of the filter.** For `H v = 0`, `F_T(H) v = (η T) • v`. -/
theorem horizonFilter_mulVec_null (H : Matrix ι ι ℝ) (η : ℝ) (v : ι → ℝ)
    (hv : H.mulVec v = 0) (T : ℕ) :
    (horizonFilter H η T).mulVec v = (η * T) • v := by
  unfold horizonFilter
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  have h0 : H.mulVec v = (0 : ℝ) • v := by rw [hv, zero_smul]
  simp only [pow_one_sub_smul_mulVec_eigen H η 0 v h0, mul_zero, sub_zero, one_pow, one_smul]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]


/-! ### The gradient-flow filter and the saturation mismatch -/

/-- **Gradient flow in an eigendirection.** `δ(t) = -ε ((1 - e^{-λt})/λ) b` solves
`δ' = -λ δ - ε b`, `δ(0) = 0`: the gradient-flow filter is `(1 - e^{-λt})/λ` (Prop. 3.1). -/
theorem gradientFlow_filter (lam ε b : ℝ) (hlam : lam ≠ 0) :
    (∀ t, HasDerivAt (fun t => -(ε * ((1 - Real.exp (-(lam * t))) / lam) * b))
      (-lam * (-(ε * ((1 - Real.exp (-(lam * t))) / lam) * b)) - ε * b) t) ∧
    -(ε * ((1 - Real.exp (-(lam * 0))) / lam) * b) = 0 := by
  refine ⟨fun t => ?_, by simp⟩
  have h := ((((hasDerivAt_id t).const_mul lam).neg.exp.const_sub 1).div_const lam).const_mul ε
    |>.mul_const b |>.neg
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, id_eq]
  field_simp
  ring

/-- On the null space (`λ = 0`) the filter is `t`: `δ(t) = -ε t b` solves `δ' = -ε b`. -/
theorem gradientFlow_filter_null (ε b : ℝ) :
    ∀ t, HasDerivAt (fun t : ℝ => -(ε * t * b)) (-(ε * b)) t := by
  intro t
  have h := (((hasDerivAt_id t).const_mul ε).mul_const b).neg
  refine h.congr_deriv ?_
  simp

/-- **The 26% mismatch of Corollary 3.3.** At `λ = ρ` and `ηT = 1/ρ` the gradient-flow filter
`(1 - e^{-1})/ρ` exceeds the posterior filter `1/(2ρ)` by a factor between `1.26` and `1.27`. -/
theorem mismatch_ratio_bounds :
    (1.26 : ℝ) < 2 * (1 - Real.exp (-1)) ∧ 2 * (1 - Real.exp (-1)) < 1.27 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  rw [Real.exp_neg]
  constructor
  · have : (Real.exp 1)⁻¹ < 0.37 := by
      rw [inv_lt_comm₀ hpos (by norm_num)]
      norm_num at h1 ⊢
      linarith
    linarith
  · have : (0.365 : ℝ) < (Real.exp 1)⁻¹ := by
      rw [lt_inv_comm₀ (by norm_num) hpos]
      norm_num at h2 ⊢
      linarith
    linarith

end

end Laplace.Patterning
