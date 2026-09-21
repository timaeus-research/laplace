/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib

/-!
# Jacobi's formula: the derivative of a determinant and of a log-determinant

Lemma 5.1 and the log-volume derivative of Proposition 5.2 of the working note *Patterning
flow* rest on Jacobi's formula `d/ds log det H(s) = tr(H(s)⁻¹ H'(s))`. Mathlib (v4.33) has no
determinant calculus, so we prove it from the Leibniz expansion `det M = ∑ σ, ε σ ∏ i, M (σ i) i`:

* `hasDerivAt_det`: `d/ds det H(s) = ∑ i, det (H with column i replaced by H' column i)`;
* `sum_det_updateCol_eq_trace`: that sum is `tr(adjugate H · H')`;
* `hasDerivAt_det_trace` / `hasDerivAt_log_det`: `d/ds det H = tr(adj H · H')` and, for
  invertible `H`, `d/ds log det H = tr(H⁻¹ H')` (as `Real.log |det|` when `det < 0`);
* `logdet_response_algebra`: the identification behind Proposition 5.2,
  `tr(Σ (B - H)) + tr(Σ (T·v)) = tr(BΣ) - d + (T:Σ)·v` for `Σ H = 1`.
-/

namespace Laplace.Patterning

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Derivative of a finite product: `(∏ f_i)' = ∑_i (∏_{j ≠ i} f_j) f_i'`. -/
theorem hasDerivAt_finset_prod {κ : Type*} [DecidableEq κ] (u : Finset κ) (f : κ → ℝ → ℝ)
    (f' : κ → ℝ) (x : ℝ) (hf : ∀ i ∈ u, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y => ∏ i ∈ u, f i y) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) * f' i) x := by
  induction u using Finset.induction_on with
  | empty => simp [hasDerivAt_const]
  | insert a u ha ih =>
    have hfa := hf a (Finset.mem_insert_self a u)
    have hrest := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h := hfa.mul hrest
    simp only [Finset.prod_insert ha]
    refine h.congr_deriv ?_
    rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hia : a ≠ i := fun h => ha (by rw [h]; exact hi)
      rw [Finset.erase_insert_of_ne hia, Finset.prod_insert fun h => ha (Finset.mem_of_mem_erase h)]
      ring

/-- The Leibniz product along a permutation with column `i` replaced. -/
lemma prod_updateCol_perm (M : Matrix ι ι ℝ) (i : ι) (c : ι → ℝ) (σ : Equiv.Perm ι) :
    ∏ j, (M.updateCol i c) (σ j) j = c (σ i) * ∏ j ∈ univ.erase i, M (σ j) j := by
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i), Matrix.updateCol_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)

/-- **Jacobi's formula, column form.** If every entry of `H s` is differentiable at `s₀` with
derivative `H'`, then `d/ds det H(s) = ∑ i, det (updateCol (H s₀) i (H'ᵀ i))`. -/
theorem hasDerivAt_det (H : ℝ → Matrix ι ι ℝ) (H' : Matrix ι ι ℝ) (s₀ : ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) s₀) :
    HasDerivAt (fun s => (H s).det)
      (∑ i, ((H s₀).updateCol i (fun j => H' j i)).det) s₀ := by
  have hprod : ∀ σ : Equiv.Perm ι, HasDerivAt (fun s => ∏ j, H s (σ j) j)
      (∑ i, (∏ j ∈ univ.erase i, H s₀ (σ j) j) * H' (σ i) i) s₀ :=
    fun σ => hasDerivAt_finset_prod univ (fun j s => H s (σ j) j) (fun j => H' (σ j) j) s₀
      (fun j _ => hH (σ j) j)
  have h0 := HasDerivAt.sum (u := univ) (fun σ _ => (hprod σ).const_mul
    ((Equiv.Perm.sign σ : ℤ) : ℝ))
  have h : HasDerivAt (fun s => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, H s (σ j) j)
      (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i, (∏ j ∈ univ.erase i, H s₀ (σ j) j) * H' (σ i) i) s₀ := by
    refine h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp [Finset.sum_apply]
  have hdet : (fun s => (H s).det)
      = fun s => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, H s (σ j) j := by
    funext s
    rw [Matrix.det_apply']
  rw [hdet]
  refine h.congr_deriv ?_
  simp_rw [Matrix.det_apply', prod_updateCol_perm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- `∑ i, det (updateCol A i (Bᵀ i)) = tr(adjugate A · B)`. -/
theorem sum_det_updateCol_eq_trace (A B : Matrix ι ι ℝ) :
    ∑ i, (A.updateCol i (fun j => B j i)).det = (A.adjugate * B).trace := by
  simp only [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- **Jacobi's formula.** `d/ds det H(s) = tr(adjugate H(s₀) · H')`. -/
theorem hasDerivAt_det_trace (H : ℝ → Matrix ι ι ℝ) (H' : Matrix ι ι ℝ) (s₀ : ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) s₀) :
    HasDerivAt (fun s => (H s).det) (((H s₀).adjugate * H').trace) s₀ := by
  rw [← sum_det_updateCol_eq_trace]
  exact hasDerivAt_det H H' s₀ hH

/-- `adjugate A = det A • A⁻¹` for invertible `A`. -/
lemma adjugate_eq_det_smul_inv (A : Matrix ι ι ℝ) (hA : IsUnit A.det) :
    A.adjugate = A.det • A⁻¹ := by
  have h := Matrix.mul_adjugate A
  calc A.adjugate = A⁻¹ * (A * A.adjugate) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA, Matrix.one_mul]
    _ = A.det • A⁻¹ := by rw [h, Matrix.mul_smul, Matrix.mul_one]

/-- **Jacobi's formula for the log-determinant.** For `det H(s₀) ≠ 0`,
`d/ds log det H(s) = tr(H(s₀)⁻¹ H')` (with `Real.log` of a negative determinant read as
`log |det|`). -/
theorem hasDerivAt_log_det (H : ℝ → Matrix ι ι ℝ) (H' : Matrix ι ι ℝ) (s₀ : ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) s₀) (hdet : (H s₀).det ≠ 0) :
    HasDerivAt (fun s => Real.log (H s).det) (((H s₀)⁻¹ * H').trace) s₀ := by
  have h := (hasDerivAt_det_trace H H' s₀ hH).log hdet
  refine h.congr_deriv ?_
  rw [adjugate_eq_det_smul_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  field_simp

/-- The derivative of the log-volume `½ log det H(s)` is `½ tr(H⁻¹ H')`. -/
theorem hasDerivAt_half_log_det (H : ℝ → Matrix ι ι ℝ) (H' : Matrix ι ι ℝ) (s₀ : ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) s₀) (hdet : (H s₀).det ≠ 0) :
    HasDerivAt (fun s => (1 / 2) * Real.log (H s).det) ((1 / 2) * ((H s₀)⁻¹ * H').trace) s₀ :=
  (hasDerivAt_log_det H H' s₀ hH hdet).const_mul _

/-- `tr(Σ M) = ∑ k l, Σ_kl M_lk`, the coordinate form of Lemma 5.1. -/
theorem trace_mul_eq_double_sum (S M : Matrix ι ι ℝ) :
    (S * M).trace = ∑ k, ∑ l, S k l * M l k := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-- The contraction `(T:Σ)_j = ∑ k l, T j k l Σ_kl` of a 3-tensor with a matrix. -/
def tensorContract (T : ι → ι → ι → ℝ) (S : Matrix ι ι ℝ) (j : ι) : ℝ :=
  ∑ k, ∑ l, T j k l * S k l

/-- The matrix `(T·v)_kl = ∑ j, T j k l v j`. -/
def tensorApply (T : ι → ι → ι → ℝ) (v : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun k l => ∑ j, T j k l * v j

/-- **The algebra of Proposition 5.2.** If `H'(0) = (B - H) + T·v` (the Hessian of the
deformed loss at the moving minimiser) and `Σ H = 1` with `Σ` symmetric, then
`tr(Σ H') = tr(B Σ) - d + (T:Σ)·v`. -/
theorem logdet_response_algebra (S H B : Matrix ι ι ℝ) (T : ι → ι → ι → ℝ) (v : ι → ℝ)
    (hS : S * H = 1) (hsymm : Sᵀ = S) :
    (S * ((B - H) + tensorApply T v)).trace
      = (B * S).trace - Fintype.card ι + ∑ j, tensorContract T S j * v j := by
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_sub, hS, Matrix.trace_sub, Matrix.trace_one,
    Matrix.trace_mul_comm S B]
  congr 1
  have hS' : ∀ p q, S p q = S q p := fun p q => by
    have h := congrFun (congrFun hsymm q) p
    rw [Matrix.transpose_apply] at h
    exact h
  rw [trace_mul_eq_double_sum]
  simp only [tensorApply, tensorContract, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext x; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun j _ => ?_
  rw [hS' y x]
  ring

end Laplace.Patterning
