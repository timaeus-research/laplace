/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.IteratedLogPrimitive

/-!
# The squeeze for iterated logarithmic primitives (grammar §4.2, general multiplicity)

With `H_m = iterLogPrim β a m`, `A = quadMass β a`, `E = e^{βa²/2}`, `M = quadMoment β a`, we prove
by induction the uniform estimate

  `|H_{k+1}(L) - A (log L)^{k+1}/(k+1)!| ≤ C_{k+1} (1 + log L)^k`   for `L ≥ 1`,

with `C₁ = E + M` and `C_{m+1} = E + C_m/m`. The step integrates the previous estimate against
`dx/x`, using `∫₁^L (log x)^k/x = (log L)^{k+1}/(k+1)` and
`∫₁^L (1+log x)^k/x = ((1+log L)^{k+1} - 1)/(k+1)`. This is the analytic engine behind the general
multiplicity theorem `Z_d ~ (S_{1/2}(a)/(2^d (d-1)!)) n^{-1/2} (log n)^{d-1}`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- `∫₁^L (log x)^k/x dx = (log L)^{k+1}/(k+1)`. -/
theorem integral_log_pow_div (k : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    (∫ x in (1 : ℝ)..L, Real.log x ^ k / x) = Real.log L ^ (k + 1) / ((k : ℝ) + 1) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) L,
      HasDerivAt (fun x => Real.log x ^ (k + 1) / ((k : ℝ) + 1)) (Real.log x ^ k / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hL] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
    have h := ((Real.hasDerivAt_log hx0.ne').pow (k + 1)).div_const ((k : ℝ) + 1)
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x ^ k / x) volume 1 L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL]
    exact ((Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne').pow k).div
      continuousOn_id fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- `∫₁^L (1 + log x)^k/x dx = ((1 + log L)^{k+1} - 1)/(k+1)`. -/
theorem integral_one_add_log_pow_div (k : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    (∫ x in (1 : ℝ)..L, (1 + Real.log x) ^ k / x)
      = ((1 + Real.log L) ^ (k + 1) - 1) / ((k : ℝ) + 1) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) L,
      HasDerivAt (fun x => (1 + Real.log x) ^ (k + 1) / ((k : ℝ) + 1))
        ((1 + Real.log x) ^ k / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hL] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
    have h := (((hasDerivAt_const x (1 : ℝ)).add
      (Real.hasDerivAt_log hx0.ne')).pow (k + 1)).div_const ((k : ℝ) + 1)
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel, Pi.add_apply, zero_add]
    push_cast
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => (1 + Real.log x) ^ k / x) volume 1 L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL]
    exact ((continuousOn_const.add
      (Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne')).pow k).div
      continuousOn_id fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [sub_div]

/-- The constants of the squeeze: `C₁ = E + M`, `C_{m+1} = E + C_m/m`. -/
noncomputable def iterConst (β a : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => Real.exp (β * a ^ 2 / 2) + quadMoment β a
  | (m + 2) => Real.exp (β * a ^ 2 / 2) + iterConst β a (m + 1) / ((m : ℝ) + 1)

theorem iterConst_one (β a : ℝ) : iterConst β a 1 = Real.exp (β * a ^ 2 / 2) + quadMoment β a := rfl

theorem iterConst_succ_succ (β a : ℝ) (m : ℕ) :
    iterConst β a (m + 1 + 1) = Real.exp (β * a ^ 2 / 2) + iterConst β a (m + 1) / ((m : ℝ) + 1) :=
  rfl

theorem iterConst_nonneg (β a : ℝ) (m : ℕ) : 0 ≤ iterConst β a (m + 1) := by
  induction m with
  | zero => rw [iterConst_one]; exact add_nonneg (Real.exp_pos _).le (quadMoment_nonneg β a)
  | succ m ih => rw [iterConst_succ_succ]; positivity

/-- **The iterated squeeze**: for `L ≥ 1`,
`|H_{k+1}(L) - A (log L)^{k+1}/(k+1)!| ≤ C_{k+1} (1 + log L)^k`. -/
theorem iterLogPrim_sub_le (β a : ℝ) (hβ : 0 < β) (k : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    |iterLogPrim β a (k + 1) L - quadMass β a * Real.log L ^ (k + 1) / ((k + 1).factorial : ℝ)|
      ≤ iterConst β a (k + 1) * (1 + Real.log L) ^ k := by
  induction k generalizing L with
  | zero =>
    rw [iterLogPrim_one β a L (zero_le_one.trans hL), iterConst_one]
    simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one, pow_zero, mul_one]
    have h := logPrimitive_bounds β a L hβ hL
    have hE0 : 0 < Real.exp (β * a ^ 2 / 2) := Real.exp_pos _
    have hM0 := quadMoment_nonneg β a
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  | succ k ih =>
    have hE0 : 0 < Real.exp (β * a ^ 2 / 2) := Real.exp_pos _
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
    have hC0 := iterConst_nonneg β a k
    set E := Real.exp (β * a ^ 2 / 2) with hE
    set A := quadMass β a with hA
    set C := iterConst β a (k + 1) with hC
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    -- split H_{k+2}(L) = ∫₀¹ + ∫₁^L
    have hsplit : iterLogPrim β a (k + 1 + 1) L
        = (∫ t in (0 : ℝ)..1, iterLogPrim β a (k + 1) t / t)
          + ∫ t in (1 : ℝ)..L, iterLogPrim β a (k + 1) t / t := by
      rw [iterLogPrim_succ, intervalIntegral.integral_add_adjacent_intervals
        (iterLogPrim_div_intervalIntegrable β a hβ (k + 1) 0 1)
        (iterLogPrim_div_intervalIntegrable β a hβ (k + 1) 1 L)]
    -- the piece on [0,1]
    have h1_nonneg : 0 ≤ ∫ t in (0 : ℝ)..1, iterLogPrim β a (k + 1) t / t :=
      intervalIntegral.integral_nonneg zero_le_one fun t ht =>
        div_nonneg (iterLogPrim_nonneg β a (k + 1) t ht.1) ht.1
    have h1_le : (∫ t in (0 : ℝ)..1, iterLogPrim β a (k + 1) t / t) ≤ E := by
      calc (∫ t in (0 : ℝ)..1, iterLogPrim β a (k + 1) t / t) ≤ ∫ _ in (0 : ℝ)..1, E :=
            intervalIntegral.integral_mono_on zero_le_one
              (iterLogPrim_div_intervalIntegrable β a hβ (k + 1) 0 1)
              (continuous_const.intervalIntegrable _ _) fun t _ =>
              (le_abs_self _).trans (iterLogPrim_div_abs_le β a hβ (k + 1) t)
        _ = E := by simp
    -- the piece on [1,L]: main term plus remainder
    have hmain_int : IntervalIntegrable
        (fun t : ℝ => A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ) / t) volume 1 L := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hL]
      exact (((Real.continuousOn_log.mono fun x hx =>
        (lt_of_lt_of_le one_pos hx.1).ne').pow (k + 1)).const_smul A |>.div_const _).div
        continuousOn_id fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
    have hrem_int : IntervalIntegrable (fun t : ℝ => (iterLogPrim β a (k + 1) t
        - A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ)) / t) volume 1 L := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hL]
      exact (((iterLogPrim_continuous β a hβ (k + 1)).continuousOn).sub
        ((((Real.continuousOn_log.mono fun x hx =>
          (lt_of_lt_of_le one_pos hx.1).ne').pow (k + 1)).const_smul A).div_const _)).div
        continuousOn_id fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
    have hdecomp : (∫ t in (1 : ℝ)..L, iterLogPrim β a (k + 1) t / t)
        = (∫ t in (1 : ℝ)..L, A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ) / t)
          + ∫ t in (1 : ℝ)..L, (iterLogPrim β a (k + 1) t
            - A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ)) / t := by
      rw [← intervalIntegral.integral_add hmain_int hrem_int]
      congr 1; funext t; ring
    have hmain_val : (∫ t in (1 : ℝ)..L, A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ) / t)
        = A * Real.log L ^ (k + 1 + 1) / ((k + 1 + 1).factorial : ℝ) := by
      have hfun : (fun t : ℝ => A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ) / t)
          = fun t => (A / ((k + 1).factorial : ℝ)) * (Real.log t ^ (k + 1) / t) := by
        funext t; ring
      rw [hfun, intervalIntegral.integral_const_mul, integral_log_pow_div (k + 1) L hL,
        Nat.factorial_succ (k + 1)]
      have hf0 : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
    have hrem_le : |∫ t in (1 : ℝ)..L, (iterLogPrim β a (k + 1) t
        - A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ)) / t|
        ≤ C * ((1 + Real.log L) ^ (k + 1) - 1) / ((k : ℝ) + 1) := by
      have hbnd_int : IntervalIntegrable (fun t : ℝ => C * ((1 + Real.log t) ^ k / t))
          volume 1 L := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hL]
        exact (((continuousOn_const.add (Real.continuousOn_log.mono fun x hx =>
          (lt_of_lt_of_le one_pos hx.1).ne')).pow k).div continuousOn_id fun x hx =>
          (lt_of_lt_of_le one_pos hx.1).ne').const_smul C
      calc |∫ t in (1 : ℝ)..L, (iterLogPrim β a (k + 1) t
            - A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ)) / t|
          ≤ ∫ t in (1 : ℝ)..L, |(iterLogPrim β a (k + 1) t
            - A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ)) / t| :=
            intervalIntegral.abs_integral_le_integral_abs hL
        _ ≤ ∫ t in (1 : ℝ)..L, C * ((1 + Real.log t) ^ k / t) := by
            apply intervalIntegral.integral_mono_on hL hrem_int.abs hbnd_int
            intro t ht
            have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
            rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
            calc |iterLogPrim β a (k + 1) t - A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ)|
                ≤ C * (1 + Real.log t) ^ k := ih t ht.1
              _ = C * ((1 + Real.log t) ^ k / t) * t := by field_simp
        _ = C * ((1 + Real.log L) ^ (k + 1) - 1) / ((k : ℝ) + 1) := by
            rw [intervalIntegral.integral_const_mul, integral_one_add_log_pow_div k L hL]; ring
    have hpow1 : (1 : ℝ) ≤ (1 + Real.log L) ^ (k + 1) := one_le_pow₀ (by linarith)
    rw [hsplit, hdecomp, hmain_val, iterConst_succ_succ]
    have hI1 : |∫ t in (0 : ℝ)..1, iterLogPrim β a (k + 1) t / t| ≤ E := by
      rw [abs_of_nonneg h1_nonneg]; exact h1_le
    calc |(∫ t in (0 : ℝ)..1, iterLogPrim β a (k + 1) t / t)
          + (A * Real.log L ^ (k + 1 + 1) / ((k + 1 + 1).factorial : ℝ)
            + ∫ t in (1 : ℝ)..L, (iterLogPrim β a (k + 1) t
              - A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ)) / t)
          - A * Real.log L ^ (k + 1 + 1) / ((k + 1 + 1).factorial : ℝ)|
        = |(∫ t in (0 : ℝ)..1, iterLogPrim β a (k + 1) t / t)
          + ∫ t in (1 : ℝ)..L, (iterLogPrim β a (k + 1) t
              - A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ)) / t| := by congr 1; ring
      _ ≤ |∫ t in (0 : ℝ)..1, iterLogPrim β a (k + 1) t / t|
          + |∫ t in (1 : ℝ)..L, (iterLogPrim β a (k + 1) t
              - A * Real.log t ^ (k + 1) / ((k + 1).factorial : ℝ)) / t| := abs_add_le _ _
      _ ≤ E + C * ((1 + Real.log L) ^ (k + 1) - 1) / ((k : ℝ) + 1) := add_le_add hI1 hrem_le
      _ ≤ (E + C / ((k : ℝ) + 1)) * (1 + Real.log L) ^ (k + 1) := by
          have h1 : 0 ≤ E * ((1 + Real.log L) ^ (k + 1) - 1) :=
            mul_nonneg hE0.le (sub_nonneg.2 hpow1)
          have h2 : 0 ≤ C / ((k : ℝ) + 1) := div_nonneg hC0 hk1.le
          have h3 : C * ((1 + Real.log L) ^ (k + 1) - 1) / ((k : ℝ) + 1)
              = C / ((k : ℝ) + 1) * (1 + Real.log L) ^ (k + 1) - C / ((k : ℝ) + 1) := by ring
          rw [h3]
          nlinarith

end Laplace.Grammar
