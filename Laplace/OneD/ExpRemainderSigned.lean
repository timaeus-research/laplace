/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.RecoveryAllOrder

/-!
# The exponential Taylor remainder for signed arguments

Stage 1 of the gamma-rung programme. The all-order remainder bound
`|e^(-s) - ∑_{j<n} (-s)^j/j!| ≤ s^n/n!` holds for `s ≥ 0`; the rescaled
anharmonic perturbation `s_t(u) = A·u³/√t + B·u⁴/t` is sign-indefinite,
so the second-order `J_n` expansions need the two-sided endpoint-maximum
form `|expRemainder n s| ≤ |s|^n/n! · max 1 (e^(-s))`
(`abs_expRemainder_le_max`), valid for every real `s`. The negative
branch carries the sharper inductive form
`|expRemainder n s| ≤ |s|^n/n! · e^(-s)` for `s ≤ 0`
(`abs_expRemainder_le_of_nonpos`), by the same fundamental-theorem
induction as the nonnegative case: on `[s, 0]` the previous remainder is
controlled by `e^(-u) ≤ e^(-s)`, and the polynomial integral evaluates
by reflection.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- The exponential Taylor remainder bound on the nonpositive axis, in
its sharp form: for `s ≤ 0`, `|expRemainder n s| ≤ |s|^n/n! · e^(-s)`. -/
theorem abs_expRemainder_le_of_nonpos :
    ∀ (n : ℕ) {s : ℝ}, s ≤ 0 →
      |expRemainder n s| ≤ |s| ^ n / (Nat.factorial n : ℝ) *
        Real.exp (-s) := by
  intro n
  induction n with
  | zero =>
    intro s _
    have h2 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
    simp only [expRemainder, Finset.range_zero, Finset.sum_empty, sub_zero,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    rw [abs_of_pos h2]
  | succ n ih =>
    intro s hs
    have hFTC : expRemainder (n + 1) s - expRemainder (n + 1) 0 =
        ∫ u in (0 : ℝ)..s, -(expRemainder n u) :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ ↦ hasDerivAt_expRemainder n u)
        (((expRemainder_continuous n).neg).intervalIntegrable 0 s)).symm
    rw [expRemainder_succ_zero, sub_zero] at hFTC
    have habs : |∫ u in (0 : ℝ)..s, -(expRemainder n u)| =
        |∫ u in s..(0 : ℝ), -(expRemainder n u)| := by
      rw [intervalIntegral.integral_symm s 0, abs_neg]
    have h1 : |∫ u in s..(0 : ℝ), -(expRemainder n u)| ≤
        ∫ u in s..(0 : ℝ), |expRemainder n u| := by
      have h := intervalIntegral.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume)
        (f := fun u ↦ -(expRemainder n u)) (a := s) (b := (0 : ℝ)) hs
      simpa [Real.norm_eq_abs] using h
    have h2 : (∫ u in s..(0 : ℝ), |expRemainder n u|) ≤
        ∫ u in s..(0 : ℝ),
          (-u) ^ n / (Nat.factorial n : ℝ) * Real.exp (-s) := by
      have hcont : Continuous fun u : ℝ ↦
          (-u) ^ n / (Nat.factorial n : ℝ) * Real.exp (-s) := by
        fun_prop
      apply intervalIntegral.integral_mono_on hs
        ((expRemainder_continuous n).abs.intervalIntegrable s 0)
        (hcont.intervalIntegrable s 0)
      intro u hu
      have hu0 : u ≤ 0 := hu.2
      have hus : s ≤ u := hu.1
      calc |expRemainder n u|
          ≤ |u| ^ n / (Nat.factorial n : ℝ) * Real.exp (-u) :=
            ih hu0
        _ ≤ (-u) ^ n / (Nat.factorial n : ℝ) * Real.exp (-s) := by
            rw [abs_of_nonpos hu0]
            apply mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by linarith))
            exact div_nonneg (pow_nonneg (by linarith) n)
              (Nat.cast_nonneg _)
    have hval : (∫ u in s..(0 : ℝ),
        (-u) ^ n / (Nat.factorial n : ℝ) * Real.exp (-s)) =
        |s| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) * Real.exp (-s) := by
      rw [show (fun u : ℝ ↦ (-u) ^ n / (Nat.factorial n : ℝ) *
          Real.exp (-s)) = fun u : ℝ ↦
          (Real.exp (-s) / (Nat.factorial n : ℝ)) * (-u) ^ n by
        funext u; ring]
      rw [intervalIntegral.integral_const_mul]
      have hpoly : (∫ u in s..(0 : ℝ), (-u) ^ n) =
          (-s) ^ (n + 1) / ((n : ℝ) + 1) := by
        have h := intervalIntegral.integral_comp_neg
          (a := s) (b := (0 : ℝ)) (fun v : ℝ ↦ v ^ n)
        simpa using h
      rw [hpoly, Nat.factorial_succ, abs_of_nonpos hs]
      push_cast
      have hnf : (Nat.factorial n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos n).ne'
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    calc |expRemainder (n + 1) s|
        = |∫ u in s..(0 : ℝ), -(expRemainder n u)| := by
          rw [hFTC, habs]
      _ ≤ ∫ u in s..(0 : ℝ), |expRemainder n u| := h1
      _ ≤ ∫ u in s..(0 : ℝ),
            (-u) ^ n / (Nat.factorial n : ℝ) * Real.exp (-s) := h2
      _ = |s| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
            Real.exp (-s) := hval

/-- **Two-sided exponential Taylor remainder** (endpoint-maximum form):
for every real `s`,
`|e^(-s) - ∑_{j<n} (-s)^j/j!| ≤ |s|^n/n! · max 1 (e^(-s))`. -/
theorem abs_expRemainder_le_max (n : ℕ) (s : ℝ) :
    |expRemainder n s| ≤ |s| ^ n / (Nat.factorial n : ℝ) *
      max 1 (Real.exp (-s)) := by
  rcases le_total 0 s with hs | hs
  · calc |expRemainder n s|
        ≤ s ^ n / (Nat.factorial n : ℝ) := abs_expRemainder_le n hs
      _ = |s| ^ n / (Nat.factorial n : ℝ) * 1 := by
          rw [abs_of_nonneg hs, mul_one]
      _ ≤ |s| ^ n / (Nat.factorial n : ℝ) *
            max 1 (Real.exp (-s)) := by
          apply mul_le_mul_of_nonneg_left (le_max_left _ _)
          positivity
  · calc |expRemainder n s|
        ≤ |s| ^ n / (Nat.factorial n : ℝ) * Real.exp (-s) :=
          abs_expRemainder_le_of_nonpos n hs
      _ ≤ |s| ^ n / (Nat.factorial n : ℝ) *
            max 1 (Real.exp (-s)) := by
          apply mul_le_mul_of_nonneg_left (le_max_right _ _)
          positivity

end Laplace.OneD
