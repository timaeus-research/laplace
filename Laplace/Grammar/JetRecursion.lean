/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Derivative
import Laplace.Grammar.TwoDCutoff

/-!
# The coefficient recursion for the exponential jets (grammar §4.2, jet algebra)

The exponential jets `E_n(s) = ∑_{m<R} (βs)^m/m! · [X^n](g_R^m)` (unit 94) satisfy the recursion

  `n E_n(s) = βs ∑_{i=1}^{n} i x_i E_{n-i}(s)`,   `1 ≤ n < R`,

which is the computational interface recommended in Astra #3/#4 (the paper's tree recursion in
disguise). The proof is finite polynomial algebra: with `T_R = ∑_{m<R} (βs)^m/m! g_R^m`,
`T_R' − βs g_R' T_R = −(βs)^R/(R−1)! · g_R' g_R^{R−1}` is divisible by `X^{R−1}` because `g_R` is
divisible by `X`, so the coefficients below `R − 1` of `T_R'` and `βs g_R' T_R` agree.
No power-series exponential is needed. Zero `sorry`/`axiom`.
-/

open Polynomial Finset

namespace Laplace.Grammar

/-- The truncated exponential polynomial `T_R = ∑_{m<R} (βs)^m/m! · g_R^m`. -/
noncomputable def expPoly (β : ℝ) (x : ℕ → ℝ) (R : ℕ) (s : ℝ) : ℝ[X] :=
  ∑ m ∈ range R, C ((β * s) ^ m / (m.factorial : ℝ)) * (gPoly x R) ^ m

theorem coeff_expPoly (β : ℝ) (x : ℕ → ℝ) (R n : ℕ) (s : ℝ) :
    (expPoly β x R s).coeff n = expJet β x R n s := by
  unfold expPoly expJet
  rw [finsetSum_coeff]
  exact Finset.sum_congr rfl fun m _ => coeff_C_mul _

theorem X_dvd_gPoly (x : ℕ → ℝ) (R : ℕ) : (X : ℝ[X]) ∣ gPoly x R := by
  rw [X_dvd_iff, gPoly, coeff_jetPoly']
  split_ifs <;> simp [shiftSeq]

/-- The derivative identity `T_R' = βs g_R' (T_R − (βs)^{R-1}/(R-1)! g_R^{R-1})`. -/
theorem derivative_expPoly (β : ℝ) (x : ℕ → ℝ) (R : ℕ) (s : ℝ) :
    derivative (expPoly β x (R + 1) s)
      = C (β * s) * derivative (gPoly x (R + 1))
        * (expPoly β x (R + 1) s
          - C ((β * s) ^ R / (R.factorial : ℝ)) * (gPoly x (R + 1)) ^ R) := by
  unfold expPoly
  rw [derivative_sum, Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, one_mul,
    derivative_one, add_zero, add_sub_cancel_right]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [derivative_C_mul, derivative_pow, Nat.add_sub_cancel]
  have hfac : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  simp only [C_mul', smul_smul, smul_mul_assoc, mul_smul_comm]
  rw [mul_comm (gPoly x (R + 1) ^ m)]
  congr 1
  rw [hfac]
  have hne : (m.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The coefficients of `g_R'`: `[X^{i}] g_R' = (i+1) x_{i+1}` for `i + 1 < R`. -/
theorem coeff_derivative_gPoly (x : ℕ → ℝ) (R i : ℕ) (hi : i + 1 < R) :
    (derivative (gPoly x R)).coeff i = ((i : ℝ) + 1) * x (i + 1) := by
  rw [coeff_derivative, gPoly, coeff_jetPoly', if_pos hi]
  simp [shiftSeq]
  ring

/-- **The coefficient recursion**: `n E_n = βs ∑_{i<n} (i+1) x_{i+1} E_{n-1-i}` for `1 ≤ n < R`. -/
theorem expJet_recursion (β : ℝ) (x : ℕ → ℝ) (R n : ℕ) (hn : 0 < n) (hnR : n < R) (s : ℝ) :
    (n : ℝ) * expJet β x R n s
      = β * s * ∑ i ∈ range n, ((i : ℝ) + 1) * x (i + 1) * expJet β x R (n - 1 - i) s := by
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hkey := congrArg (fun p : ℝ[X] => p.coeff n') (derivative_expPoly β x R' s)
  rw [coeff_derivative, coeff_expPoly] at hkey
  -- the right side: the correction term has no coefficients below `R'`
  have hX : (X : ℝ[X]) ^ R' ∣ derivative (gPoly x (R' + 1)) * gPoly x (R' + 1) ^ R' :=
    (pow_dvd_pow_of_dvd (X_dvd_gPoly x (R' + 1)) R').mul_left _
  obtain ⟨q, hq⟩ := hX
  have hzero : (C (β * s) * derivative (gPoly x (R' + 1))
      * (C ((β * s) ^ R' / (R'.factorial : ℝ)) * gPoly x (R' + 1) ^ R')).coeff n' = 0 := by
    simp only [C_mul', smul_smul, smul_mul_assoc, mul_smul_comm]
    rw [hq, coeff_smul, coeff_X_pow_mul', if_neg (by omega), smul_zero]
  rw [mul_sub, coeff_sub, hzero, sub_zero, mul_assoc, coeff_C_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => (derivative (gPoly x (R' + 1))).coeff i * (expPoly β x (R' + 1) s).coeff k) n']
    at hkey
  have hterm : ∀ i ∈ range (n' + 1),
      (derivative (gPoly x (R' + 1))).coeff i * (expPoly β x (R' + 1) s).coeff (n' - i)
        = ((i : ℝ) + 1) * x (i + 1) * expJet β x (R' + 1) (n' + 1 - 1 - i) s := by
    intro i hi
    have hi' : i + 1 < R' + 1 := by
      have := Finset.mem_range.1 hi
      omega
    rw [coeff_derivative_gPoly x (R' + 1) i hi', coeff_expPoly, Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hterm] at hkey
  simp only [Nat.add_sub_cancel] at hkey ⊢
  push_cast
  linear_combination hkey

end Laplace.Grammar
