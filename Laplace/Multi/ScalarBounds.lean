/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.CoeffFn

/-!
# Scalar quantitative bounds for the numerator expansion

Stage 5b of the forward-expansion programme, kept scalar/algebraic per
the architecture consult. Three reusable results:

- the **unrestricted exponential Taylor remainder**
  `|exp x - ∑_{i≤N} x^i/i!| ≤ |x|^(N+1) · exp|x| / (N+1)!` for all
  real `x` — the replacement for `Real.exp_bound`'s `|x| ≤ 1`
  hypothesis, which fails on the mesoscopic window where the exponent
  correction is only small relative to the quadratic;
- the **perturbation bound**
  `|exp(-(A+δ)) - exp(-A)| ≤ |δ| · exp(|A|+|δ|)`, coarse but exactly
  shaped for absorption into a weakened Gaussian;
- the **polynomial tail bound** for the graded exp polynomial, with
  the uniform indexing bound `N·N + 1` so that the tail constant does
  not depend syntactically on the point after instantiation.
-/

open Real Filter Topology Asymptotics Polynomial

namespace Laplace.Multi

/-- `m! · k! ≤ (m+k)!`. -/
theorem factorial_mul_factorial_le_factorial_add (m k : ℕ) :
    m.factorial * k.factorial ≤ (m + k).factorial :=
  Nat.le_of_dvd (m + k).factorial_pos
    (Nat.factorial_mul_factorial_dvd_factorial_add m k)

set_option maxHeartbeats 1600000 in
-- the `NormedSpace.exp` instance unification is whnf-heavy on ℝ:
-- deterministic elaboration cost, not a wrong approach
/-- The exponential as its power series. -/
theorem real_exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
  have h : HasSum (fun n : ℕ ↦ x ^ n / (n.factorial : ℝ))
      (NormedSpace.exp x) := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h.tsum_eq.symm

set_option maxHeartbeats 1600000 in
-- the tsum comparison chain (shifted summability + termwise division
-- bounds) is whnf-heavy; deterministic elaboration cost
/-- **The unrestricted exponential Taylor remainder**: valid for all
real `x`, unlike `Real.exp_bound`. -/
theorem abs_exp_sub_sum_le (N : ℕ) (x : ℝ) :
    |Real.exp x - ∑ i ∈ Finset.range (N + 1), x ^ i / (i.factorial : ℝ)| ≤
      |x| ^ (N + 1) * Real.exp |x| / ((N + 1).factorial : ℝ) := by
  have hsum : Summable (fun n : ℕ ↦ x ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial x
  have hshift : Summable
      (fun i : ℕ ↦ x ^ (i + (N + 1)) / ((i + (N + 1)).factorial : ℝ)) :=
    (summable_nat_add_iff (N + 1)).mpr hsum
  have habs_sum : Summable (fun n : ℕ ↦ |x| ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial |x|
  have hrem : Real.exp x -
      ∑ i ∈ Finset.range (N + 1), x ^ i / (i.factorial : ℝ) =
      ∑' i : ℕ, x ^ (i + (N + 1)) / ((i + (N + 1)).factorial : ℝ) := by
    have hadd := hsum.sum_add_tsum_nat_add (N + 1)
    rw [real_exp_eq_tsum]
    linarith
  rw [hrem]
  have hterm : ∀ i : ℕ,
      |x ^ (i + (N + 1)) / ((i + (N + 1)).factorial : ℝ)| ≤
      |x| ^ (N + 1) / ((N + 1).factorial : ℝ) *
        (|x| ^ i / (i.factorial : ℝ)) := by
    intro i
    rw [abs_div, abs_pow, Nat.abs_cast, div_mul_div_comm, ← pow_add]
    have hexp : N + 1 + i = i + (N + 1) := by omega
    rw [hexp]
    have hfac : ((N + 1).factorial : ℝ) * (i.factorial : ℝ) ≤
        ((i + (N + 1)).factorial : ℝ) := by
      have := factorial_mul_factorial_le_factorial_add (N + 1) i
      rw [Nat.add_comm (N + 1) i] at this
      exact_mod_cast this
    exact div_le_div_of_nonneg_left (by positivity)
      (by positivity) hfac
  have hsum_le := (hshift.abs).tsum_le_tsum hterm
    ((habs_sum).mul_left _)
  calc |∑' i : ℕ, x ^ (i + (N + 1)) / ((i + (N + 1)).factorial : ℝ)|
      ≤ ∑' i : ℕ, |x ^ (i + (N + 1)) / ((i + (N + 1)).factorial : ℝ)| :=
        norm_tsum_le_tsum_norm (f := fun i : ℕ ↦
          x ^ (i + (N + 1)) / ((i + (N + 1)).factorial : ℝ)) hshift.abs
    _ ≤ ∑' i : ℕ, |x| ^ (N + 1) / ((N + 1).factorial : ℝ) *
          (|x| ^ i / (i.factorial : ℝ)) := hsum_le
    _ = |x| ^ (N + 1) / ((N + 1).factorial : ℝ) *
          ∑' i : ℕ, |x| ^ i / (i.factorial : ℝ) := tsum_mul_left
    _ = |x| ^ (N + 1) * Real.exp |x| / ((N + 1).factorial : ℝ) := by
        rw [← real_exp_eq_tsum]
        ring

/-- Unrestricted first-order exponential bound:
`|e^y - 1| ≤ |y| e^|y|`. -/
theorem abs_exp_sub_one_le' (y : ℝ) :
    |Real.exp y - 1| ≤ |y| * Real.exp |y| := by
  rcases le_or_gt 0 y with hy | hy
  · have hone : 1 ≤ Real.exp y := Real.one_le_exp hy
    have heq : Real.exp (-y) * Real.exp y = 1 := by
      rw [← Real.exp_add]
      simp
    have hkey : Real.exp y - 1 ≤ y * Real.exp y := by
      have h1 : -y + 1 ≤ Real.exp (-y) := Real.add_one_le_exp (-y)
      nlinarith [Real.exp_pos y]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hy]
    exact hkey
  · have h1 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
    have h2 : Real.exp y < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hy
    have habs : |Real.exp y - 1| = 1 - Real.exp y := by
      rw [abs_of_neg (by linarith)]
      ring
    rw [habs, abs_of_neg hy]
    have hexp1 : (1 : ℝ) ≤ Real.exp (-y) :=
      Real.one_le_exp (by linarith)
    nlinarith

/-- **The perturbation bound**: coarse but exactly shaped for Gaussian
absorption. -/
theorem abs_exp_neg_add_sub_exp_neg_le (A δ : ℝ) :
    |Real.exp (-(A + δ)) - Real.exp (-A)| ≤
      |δ| * Real.exp (|A| + |δ|) := by
  have hsplit : Real.exp (-(A + δ)) - Real.exp (-A) =
      Real.exp (-A) * (Real.exp (-δ) - 1) := by
    rw [neg_add, Real.exp_add]
    ring
  rw [hsplit, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |Real.exp (-δ) - 1| ≤ |δ| * Real.exp |δ| := by
    have := abs_exp_sub_one_le' (-δ)
    rwa [abs_neg] at this
  have h2 : Real.exp (-A) ≤ Real.exp |A| :=
    Real.exp_le_exp.mpr (neg_le_abs A)
  calc Real.exp (-A) * |Real.exp (-δ) - 1|
      ≤ Real.exp |A| * (|δ| * Real.exp |δ|) :=
        mul_le_mul h2 h1 (abs_nonneg _) (Real.exp_pos _).le
    _ = |δ| * Real.exp (|A| + |δ|) := by
        rw [Real.exp_add]
        ring

/-- Degree bound for the exponent polynomial. -/
theorem natDegree_exponentPoly_le (a : ℕ → ℝ) (N : ℕ) :
    (exponentPoly a N).natDegree ≤ N := by
  unfold exponentPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs ↦ ?_
  calc (Polynomial.C (a s) * Polynomial.X ^ s).natDegree
      ≤ (Polynomial.X ^ s : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
    _ = s := Polynomial.natDegree_X_pow s
    _ ≤ N := (Finset.mem_Icc.mp hs).2

/-- Degree bound for the graded exp polynomial: at most `N·N`. -/
theorem natDegree_gradedExpPoly_le (a : ℕ → ℝ) (N : ℕ) :
    (gradedExpPoly a N).natDegree ≤ N * N := by
  unfold gradedExpPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
  calc (Polynomial.C ((-1 : ℝ) ^ i / (i.factorial : ℝ)) *
        exponentPoly a N ^ i).natDegree
      ≤ (exponentPoly a N ^ i).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
    _ ≤ i * (exponentPoly a N).natDegree := Polynomial.natDegree_pow_le
    _ ≤ i * N := Nat.mul_le_mul_left i (natDegree_exponentPoly_le a N)
    _ ≤ N * N := by
        have hi' : i ≤ N := by
          have := Finset.mem_range.mp hi
          omega
        exact Nat.mul_le_mul_right N hi'

/-- **The polynomial tail bound**, with the uniform indexing bound
`N·N + 1` so the tail constant does not depend on the instantiation
point. -/
theorem gradedExpPoly_tail_bound (a : ℕ → ℝ) (N : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |(gradedExpPoly a N).eval q -
        ∑ j ∈ Finset.range (N + 1), expCorrectionCoeff a N j * q ^ j| ≤
      q ^ (N + 1) *
        ∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
          |expCorrectionCoeff a N j| := by
  have hdeg : (gradedExpPoly a N).natDegree < N * N + 1 :=
    Nat.lt_succ_of_le (natDegree_gradedExpPoly_le a N)
  have hNn : N + 1 ≤ N * N + 1 := by
    have hNsq : N ≤ N * N := by
      cases N with
      | zero => exact le_rfl
      | succ n => exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg]
  have hsplit : ∑ j ∈ Finset.range (N * N + 1),
      (gradedExpPoly a N).coeff j * q ^ j =
      (∑ j ∈ Finset.range (N + 1),
        (gradedExpPoly a N).coeff j * q ^ j) +
        ∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
          (gradedExpPoly a N).coeff j * q ^ j := by
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) hNn]
  have hc : ∀ j, expCorrectionCoeff a N j = (gradedExpPoly a N).coeff j :=
    fun _ ↦ rfl
  simp only [hc]
  rw [hsplit, add_sub_cancel_left]
  calc |∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
        (gradedExpPoly a N).coeff j * q ^ j|
      ≤ ∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
          |(gradedExpPoly a N).coeff j * q ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
          |(gradedExpPoly a N).coeff j| * q ^ (N + 1) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 j)]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hq0 hq1 (Finset.mem_Ico.mp hj).1)
          (abs_nonneg _)
    _ = q ^ (N + 1) *
          ∑ j ∈ Finset.Ico (N + 1) (N * N + 1),
            |(gradedExpPoly a N).coeff j| := by
        rw [← Finset.sum_mul]
        ring

end Laplace.Multi
