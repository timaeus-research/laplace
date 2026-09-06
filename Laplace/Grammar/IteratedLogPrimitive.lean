/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogSquaredThreeD

/-!
# Iterated logarithmic primitives (grammar §4.2, towards general multiplicity)

`iterLogPrim β a m` is the `m`-fold iterated logarithmic primitive of the quadratic kernel:
`iterLogPrim 0 = F = ∫₀^x f` and `iterLogPrim (m+1) x = ∫₀^x iterLogPrim m t / t dt`, all as
interval integrals so that continuity is automatic. We prove `|H_m(t)| ≤ E |t|` for every real `t`,
continuity, nonnegativity on `x ≥ 0`, `H_m(0) = 0`, and the "divide and substitute" identity
`∫₀^b H_m(cu)/u du = H_{m+1}(cb)` that drives the reduction of the `d`-dimensional standard
integral. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- Iterated logarithmic primitives of the quadratic kernel. -/
noncomputable def iterLogPrim (β a : ℝ) : ℕ → ℝ → ℝ
  | 0 => quadPrimitive β a
  | m + 1 => fun x => ∫ t in (0 : ℝ)..x, iterLogPrim β a m t / t

theorem iterLogPrim_zero (β a : ℝ) : iterLogPrim β a 0 = quadPrimitive β a := rfl

theorem iterLogPrim_succ (β a : ℝ) (m : ℕ) (x : ℝ) :
    iterLogPrim β a (m + 1) x = ∫ t in (0 : ℝ)..x, iterLogPrim β a m t / t := rfl

/-- `|H_m(t)| ≤ E |t|` for all `t`, and `H_m` is continuous (simultaneous induction). -/
theorem iterLogPrim_abs_le_and_continuous (β a : ℝ) (hβ : 0 < β) (m : ℕ) :
    (∀ t, |iterLogPrim β a m t| ≤ Real.exp (β * a ^ 2 / 2) * |t|) ∧
      Continuous (iterLogPrim β a m) := by
  have hE0 : 0 < Real.exp (β * a ^ 2 / 2) := Real.exp_pos _
  induction m with
  | zero => exact ⟨fun t => abs_quadPrimitive_le β a t hβ, quadPrimitive_continuous β a⟩
  | succ m ih =>
    obtain ⟨hb, hc⟩ := ih
    have hg : ∀ t, |iterLogPrim β a m t / t| ≤ Real.exp (β * a ^ 2 / 2) := by
      intro t
      rcases eq_or_ne t 0 with h0 | h0
      · simp [h0, hE0.le]
      · rw [abs_div, div_le_iff₀ (abs_pos.2 h0)]; exact hb t
    have hgint : ∀ c d, IntervalIntegrable (fun t => iterLogPrim β a m t / t) volume c d := by
      intro c d
      refine (intervalIntegrable_const (c := Real.exp (β * a ^ 2 / 2))).mono_fun
        (hc.measurable.div measurable_id).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun t => ?_
      beta_reduce
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hE0]
      exact hg t
    refine ⟨fun t => ?_, intervalIntegral.continuous_primitive hgint 0⟩
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
      (C := Real.exp (β * a ^ 2 / 2)) (f := fun t => iterLogPrim β a m t / t) fun x _ => by
        rw [Real.norm_eq_abs]; exact hg x
    rw [Real.norm_eq_abs, sub_zero] at this
    exact this

theorem iterLogPrim_abs_le (β a : ℝ) (hβ : 0 < β) (m : ℕ) (t : ℝ) :
    |iterLogPrim β a m t| ≤ Real.exp (β * a ^ 2 / 2) * |t| :=
  (iterLogPrim_abs_le_and_continuous β a hβ m).1 t

theorem iterLogPrim_continuous (β a : ℝ) (hβ : 0 < β) (m : ℕ) :
    Continuous (iterLogPrim β a m) :=
  (iterLogPrim_abs_le_and_continuous β a hβ m).2

theorem iterLogPrim_div_abs_le (β a : ℝ) (hβ : 0 < β) (m : ℕ) (t : ℝ) :
    |iterLogPrim β a m t / t| ≤ Real.exp (β * a ^ 2 / 2) := by
  rcases eq_or_ne t 0 with h0 | h0
  · simp [h0, (Real.exp_pos _).le]
  · rw [abs_div, div_le_iff₀ (abs_pos.2 h0)]; exact iterLogPrim_abs_le β a hβ m t

theorem iterLogPrim_div_intervalIntegrable (β a : ℝ) (hβ : 0 < β) (m : ℕ) (c d : ℝ) :
    IntervalIntegrable (fun t => iterLogPrim β a m t / t) volume c d := by
  refine (intervalIntegrable_const (c := Real.exp (β * a ^ 2 / 2))).mono_fun
    ((iterLogPrim_continuous β a hβ m).measurable.div measurable_id).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  beta_reduce
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact iterLogPrim_div_abs_le β a hβ m t

theorem iterLogPrim_nonneg (β a : ℝ) (m : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ iterLogPrim β a m x := by
  induction m generalizing x with
  | zero => exact quadPrimitive_nonneg β a x hx
  | succ m ih =>
    rw [iterLogPrim_succ]
    exact intervalIntegral.integral_nonneg hx fun t ht => div_nonneg (ih t ht.1) ht.1

theorem iterLogPrim_le_linear (β a : ℝ) (hβ : 0 < β) (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    iterLogPrim β a m x ≤ Real.exp (β * a ^ 2 / 2) * x := by
  have := iterLogPrim_abs_le β a hβ m x
  rw [abs_of_nonneg hx] at this
  exact (le_abs_self _).trans this

theorem iterLogPrim_zero_val (β a : ℝ) (m : ℕ) : iterLogPrim β a m 0 = 0 := by
  cases m with
  | zero => simp [iterLogPrim_zero, quadPrimitive]
  | succ m => simp [iterLogPrim_succ]

/-- `H_1` is the logarithmic primitive of `LogTwoD.lean` on `x ≥ 0`. -/
theorem iterLogPrim_one (β a x : ℝ) (hx : 0 ≤ x) : iterLogPrim β a 1 x = logPrimitive β a x := by
  rw [iterLogPrim_succ, iterLogPrim_zero, logPrimitive_eq_intervalIntegral β a x hx]

/-- **Divide and substitute**: `∫₀^b H_m(cu)/u du = H_{m+1}(cb)`. -/
theorem integral_iterLogPrim_div_eq (β a : ℝ) (m : ℕ) (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    (∫ u in Ioc (0 : ℝ) b, iterLogPrim β a m (c * u) / u) = iterLogPrim β a (m + 1) (c * b) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hpt : ∀ u, iterLogPrim β a m (c * u) / u
      = c * (iterLogPrim β a m (c * u) / (c * u)) := by
    intro u
    rcases eq_or_ne u 0 with h0 | h0
    · simp [h0, iterLogPrim_zero_val]
    · field_simp
  simp_rw [hpt]
  have hsub : (∫ u in (0 : ℝ)..b, iterLogPrim β a m (c * u) / (c * u))
      = c⁻¹ • ∫ x in (c * 0)..(c * b), iterLogPrim β a m x / x :=
    intervalIntegral.integral_comp_mul_left (fun x => iterLogPrim β a m x / x) hc0
  rw [← intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_const_mul, hsub, mul_zero,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul, iterLogPrim_succ]

end Laplace.Grammar
