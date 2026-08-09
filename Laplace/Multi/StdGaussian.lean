/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.Dilation

/-!
# The standard isotropic Gaussian package

Stage H2a of the multivariate programme, first installment: the
standard kernel `k₀(y) = e^(-‖y‖²/2)` on `EuclidD d`, its explicit
partition value `(2π)^(d/2)` (from Mathlib's inner-product-space
Gaussian integral), and integrability of every polynomial weight
`‖y‖^n·k₀` — by the elementary series bound
`t^(2m) ≤ 8^m·m!·e^(t²/8)`, so the weighted kernel is dominated by a
constant multiple of `e^(-3‖y‖²/8)`, with no Fubini and no
coordinates. The coordinate moments (the flagged hardest step) follow
in the next installment.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

/-- The standard isotropic Gaussian kernel. -/
noncomputable def stdKernel {d : ℕ} (y : EuclidD d) : ℝ :=
  Real.exp (-‖y‖ ^ 2 / 2)

theorem stdKernel_pos {d : ℕ} (y : EuclidD d) : 0 < stdKernel y :=
  Real.exp_pos _

theorem stdKernel_continuous {d : ℕ} :
    Continuous (stdKernel (d := d)) := by
  unfold stdKernel
  fun_prop

/-- Integrability of `e^(-b‖y‖²)` for `b > 0`, real form. -/
theorem integrable_exp_neg_mul_sq_norm {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : EuclidD d ↦ Real.exp (-b * ‖y‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclidD d) (b := (b : ℂ)) (by simpa using hb) 0 (0 : EuclidD d)
  have h2 := h.re
  refine h2.congr (Filter.Eventually.of_forall fun y ↦ ?_)
  simp [Complex.exp_re, ← Complex.ofReal_pow, neg_mul]

/-- The standard kernel is integrable. -/
theorem stdKernel_integrable {d : ℕ} :
    Integrable (stdKernel (d := d)) := by
  have h := integrable_exp_neg_mul_sq_norm (d := d)
    (b := 1 / 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun y ↦ ?_)
  have harg : -(1 / 2 : ℝ) * ‖y‖ ^ 2 = -‖y‖ ^ 2 / 2 := by ring
  unfold stdKernel
  simp only [harg]

/-- **The standard partition value**: `∫ k₀ = (2π)^(d/2)`. -/
theorem integral_stdKernel {d : ℕ} :
    ∫ y : EuclidD d, stdKernel y = (2 * π) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclidD d) (b := 1 / 2) (by norm_num)
  rw [finrank_euclideanSpace_fin] at h
  have heq : (fun y : EuclidD d ↦ Real.exp (-(1 / 2) * ‖y‖ ^ 2)) =
      stdKernel := by
    funext y
    unfold stdKernel
    congr 1
    ring
  rw [heq] at h
  rw [h]
  congr 1
  ring

/-- The standard partition value is positive. -/
theorem integral_stdKernel_pos {d : ℕ} :
    0 < ∫ y : EuclidD d, stdKernel y := by
  rw [integral_stdKernel]
  positivity

/-- The elementary tail bound: `t^(2m) ≤ 8^m·m!·e^(t²/8)`, from the
single-term exponential series bound. -/
theorem pow_le_exp_sq_bound (m : ℕ) (t : ℝ) :
    t ^ (2 * m) ≤ 8 ^ m * (Nat.factorial m : ℝ) *
      Real.exp (t ^ 2 / 8) := by
  have hterm : (t ^ 2 / 8) ^ m / (Nat.factorial m : ℝ) ≤
      Real.exp (t ^ 2 / 8) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg
      (by positivity) (m + 1))
    exact Finset.single_le_sum
      (f := fun i ↦ (t ^ 2 / 8) ^ i / (Nat.factorial i : ℝ))
      (fun i _ ↦ by positivity) (Finset.self_mem_range_succ m)
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hkey : t ^ (2 * m) = (t ^ 2) ^ m := by
    rw [pow_mul]
  rw [hkey]
  calc (t ^ 2) ^ m = 8 ^ m * (Nat.factorial m : ℝ) *
        ((t ^ 2 / 8) ^ m / (Nat.factorial m : ℝ)) := by
        rw [div_pow]
        field_simp
    _ ≤ 8 ^ m * (Nat.factorial m : ℝ) * Real.exp (t ^ 2 / 8) := by
        apply mul_le_mul_of_nonneg_left hterm (by positivity)

/-- **All polynomial weights are integrable** against the standard
kernel: `‖y‖^n·k₀(y)` is dominated by a constant multiple of
`e^(-3‖y‖²/8)`. -/
theorem stdKernel_integrable_pow {d : ℕ} (n : ℕ) :
    Integrable (fun y : EuclidD d ↦ ‖y‖ ^ n * stdKernel y) := by
  set m : ℕ := n / 2 + 1 with hm_def
  have hn2m : n < 2 * m := by omega
  have hdom : Integrable (fun y : EuclidD d ↦
      (1 + 8 ^ m * (Nat.factorial m : ℝ)) *
        Real.exp (-(3 / 8) * ‖y‖ ^ 2)) :=
    (integrable_exp_neg_mul_sq_norm (by norm_num)).const_mul _
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y ↦ ?_)
  · exact ((continuous_norm.pow n).mul
      stdKernel_continuous).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm,
      abs_of_pos (stdKernel_pos y)]
    unfold stdKernel
    have hcases : ‖y‖ ^ n ≤ 1 + ‖y‖ ^ (2 * m) := by
      rcases le_total ‖y‖ 1 with hy | hy
      · have : ‖y‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg y) hy
        have h2 : (0 : ℝ) ≤ ‖y‖ ^ (2 * m) := by positivity
        linarith
      · have : ‖y‖ ^ n ≤ ‖y‖ ^ (2 * m) :=
          pow_le_pow_right₀ hy (by omega)
        linarith
    have hbound := pow_le_exp_sq_bound m ‖y‖
    calc ‖y‖ ^ n * Real.exp (-‖y‖ ^ 2 / 2)
        ≤ (1 + ‖y‖ ^ (2 * m)) * Real.exp (-‖y‖ ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_right hcases (Real.exp_pos _).le
      _ ≤ (1 + 8 ^ m * (Nat.factorial m : ℝ) *
            Real.exp (‖y‖ ^ 2 / 8)) * Real.exp (-‖y‖ ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          linarith
      _ = Real.exp (-‖y‖ ^ 2 / 2) + 8 ^ m * (Nat.factorial m : ℝ) *
            Real.exp (-(3 / 8) * ‖y‖ ^ 2) := by
          rw [add_mul, one_mul, mul_assoc, ← Real.exp_add]
          have harg : ‖y‖ ^ 2 / 8 + -‖y‖ ^ 2 / 2 = -(3 / 8) * ‖y‖ ^ 2 := by
            ring
          rw [harg]
      _ ≤ (1 + 8 ^ m * (Nat.factorial m : ℝ)) *
            Real.exp (-(3 / 8) * ‖y‖ ^ 2) := by
          have hmono : Real.exp (-‖y‖ ^ 2 / 2) ≤
              Real.exp (-(3 / 8) * ‖y‖ ^ 2) := by
            apply Real.exp_le_exp.mpr
            nlinarith [sq_nonneg ‖y‖]
          nlinarith [Real.exp_pos (-(3 / 8) * ‖y‖ ^ 2),
            (by positivity : (0:ℝ) ≤ 8 ^ m * (Nat.factorial m : ℝ))]

end Laplace.Multi
