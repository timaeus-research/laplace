/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.GaussianMoments
import Laplace.OneD.MonomialPotential
import Laplace.Gibbs

/-!
# The all-order expansion of the quartic-perturbed Gaussian

The complete dimension-one ladder of the germbij note's Section 7.4 for
the potential `x²/2 + b·x⁴`: every coefficient of the asymptotic
expansion of the partition function, explicit, with an elementary
remainder at every order. The analytic input is the exponential Taylor
remainder `|e^(-s) - ∑_{j<n} (-s)^j/j!| ≤ s^n/n!` for `s ≥ 0`
(`abs_expRemainder_le`, by induction via the fundamental theorem of
calculus: the remainder at order `n+1` is minus the integral of the
remainder at order `n`). The expansion
(`quartic_partition_expansion_allOrder`) then follows from the scale-`t`
Gaussian moments term by term:
`Z_b(t) = √(2π) · ∑_{j≤n} (-b)^j (4j-1)‼/j! · t^(-(j+1/2))` up to an
error of at most `√(2π) · b^(n+1) (4n+3)‼/(n+1)! · t^(-(n+3/2))`.
-/

open Real MeasureTheory
open scoped Nat

namespace Laplace.OneD

/-- The exponential Taylor remainder
`E_n(s) = e^(-s) - ∑_{j<n} (-s)^j/j!`. -/
noncomputable def expRemainder (n : ℕ) (s : ℝ) : ℝ :=
  Real.exp (-s) - ∑ j ∈ Finset.range n, (-s) ^ j / (Nat.factorial j : ℝ)

lemma expRemainder_continuous (n : ℕ) : Continuous (expRemainder n) := by
  unfold expRemainder
  fun_prop

lemma expRemainder_succ_zero (n : ℕ) : expRemainder (n + 1) 0 = 0 := by
  unfold expRemainder
  rw [Finset.sum_range_succ']
  simp

/-- The remainder at order `n+1` differentiates to minus the remainder
at order `n`. -/
lemma hasDerivAt_expRemainder (n : ℕ) (u : ℝ) :
    HasDerivAt (expRemainder (n + 1)) (-(expRemainder n u)) u := by
  have hneg : HasDerivAt (fun v : ℝ ↦ -v) (-1 : ℝ) u := (hasDerivAt_id u).neg
  have hexp : HasDerivAt (fun v : ℝ ↦ Real.exp (-v)) (-Real.exp (-u)) u := by
    simpa using (Real.hasDerivAt_exp (-u)).comp u hneg
  have hterm : ∀ j ∈ Finset.range (n + 1),
      HasDerivAt (fun v : ℝ ↦ (-v) ^ j / (Nat.factorial j : ℝ))
        ((j : ℝ) * (-u) ^ (j - 1) * (-1) / (Nat.factorial j : ℝ)) u := by
    intro j _
    exact (hneg.pow j).div_const _
  have hsum := HasDerivAt.sum hterm
  have hval : (∑ j ∈ Finset.range (n + 1),
      (j : ℝ) * (-u) ^ (j - 1) * (-1) / (Nat.factorial j : ℝ)) =
      -(∑ j ∈ Finset.range n, (-u) ^ j / (Nat.factorial j : ℝ)) := by
    rw [Finset.sum_range_succ']
    have hstep : ∀ i : ℕ,
        ((i + 1 : ℕ) : ℝ) * (-u) ^ (i + 1 - 1) * (-1) /
          (Nat.factorial (i + 1) : ℝ) =
        -((-u) ^ i / (Nat.factorial i : ℝ)) := by
      intro i
      have hfac : (Nat.factorial i : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos i).ne'
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl fun i _ ↦ hstep i]
    simp
  rw [hval] at hsum
  have hcomb := hexp.sub hsum
  have hrw : -Real.exp (-u) -
      -(∑ j ∈ Finset.range n, (-u) ^ j / (Nat.factorial j : ℝ)) =
      -(expRemainder n u) := by
    unfold expRemainder
    ring
  rw [hrw] at hcomb
  have hfe : expRemainder (n + 1) =
      ((fun v : ℝ ↦ Real.exp (-v)) - ∑ i ∈ Finset.range (n + 1),
        fun v : ℝ ↦ (-v) ^ i / (Nat.factorial i : ℝ)) := by
    funext v
    simp [expRemainder, Finset.sum_apply]
  rw [hfe]
  exact hcomb

/-- **Exponential Taylor remainder bound** (all orders, `s ≥ 0`):
`|e^(-s) - ∑_{j<n} (-s)^j/j!| ≤ s^n/n!`. -/
theorem abs_expRemainder_le :
    ∀ (n : ℕ) {s : ℝ}, 0 ≤ s →
      |expRemainder n s| ≤ s ^ n / (Nat.factorial n : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    have h1 : Real.exp (-s) ≤ 1 := by
      have := Real.exp_le_exp.mpr (neg_nonpos.mpr hs)
      simpa using this
    have h2 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
    simp only [expRemainder, Finset.range_zero, Finset.sum_empty, sub_zero,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [abs_of_pos h2]
    exact h1
  | succ n ih =>
    intro s hs
    have hFTC : expRemainder (n + 1) s - expRemainder (n + 1) 0 =
        ∫ u in (0 : ℝ)..s, -(expRemainder n u) :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ ↦ hasDerivAt_expRemainder n u)
        (((expRemainder_continuous n).neg).intervalIntegrable 0 s)).symm
    rw [expRemainder_succ_zero, sub_zero] at hFTC
    have h1 : |∫ u in (0 : ℝ)..s, -(expRemainder n u)| ≤
        ∫ u in (0 : ℝ)..s, |expRemainder n u| := by
      have h := intervalIntegral.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume)
        (f := fun u ↦ -(expRemainder n u)) (a := (0 : ℝ)) (b := s) hs
      simpa [Real.norm_eq_abs] using h
    have h2 : (∫ u in (0 : ℝ)..s, |expRemainder n u|) ≤
        ∫ u in (0 : ℝ)..s, u ^ n / (Nat.factorial n : ℝ) := by
      apply intervalIntegral.integral_mono_on hs
        ((expRemainder_continuous n).abs.intervalIntegrable 0 s)
        (((continuous_pow n).div_const _).intervalIntegrable 0 s)
      intro u hu
      exact ih hu.1
    have hval : (∫ u in (0 : ℝ)..s, u ^ n / (Nat.factorial n : ℝ)) =
        s ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
      rw [intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
      push_cast
      have hnf : (Nat.factorial n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos n).ne'
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hFTC]
    exact (h1.trans h2).trans_eq hval

/-- rpow bookkeeping: `t^j · t^(-(2j+1/2)) = t^(-(j+1/2))`. -/
lemma rpow_shift {t : ℝ} (ht : 0 < t) (j : ℕ) :
    t ^ j * t ^ (-(2 * (j : ℝ) + 1 / 2)) = t ^ (-((j : ℝ) + 1 / 2)) := by
  rw [← Real.rpow_natCast t j, ← Real.rpow_add ht]
  congr 1
  ring

/-- **All-order expansion of the quartic-perturbed Gaussian** (germbij
Section 7.4 ladder, complete for this potential). Every coefficient of
the asymptotic expansion is explicit, with an elementary remainder at
every order. -/
theorem quartic_partition_expansion_allOrder {b t : ℝ} (hb : 0 ≤ b)
    (ht : 0 < t) (n : ℕ) :
    |partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t
      - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 1),
          (-b) ^ j * ((4 * j - 1)‼ : ℝ) / (Nat.factorial j : ℝ) *
            t ^ (-((j : ℝ) + 1 / 2))|
    ≤ Real.sqrt (2 * π) * b ^ (n + 1) * ((4 * (n + 1) - 1)‼ : ℝ)
        / (Nat.factorial (n + 1) : ℝ) *
        t ^ (-(((n + 1) : ℕ) : ℝ) - 1 / 2) := by
  set q : ℝ → ℝ := fun x ↦ Real.exp (-(t * x ^ 2) / 2) with hq_def
  have hq_pos : ∀ x : ℝ, 0 < q x := fun x ↦ Real.exp_pos _
  -- Integrability of the moment family (k = 1 monomial potential).
  have hint_pow : ∀ m : ℕ, Integrable (fun x : ℝ ↦ x ^ m * q x) := by
    intro m
    have h := kth_integrable_pow (k := 1) le_rfl m ht
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [hq_def]
    congr 2
    rw [show ((Nat.factorial (2 * 1) : ℕ) : ℝ) = 2 by
      norm_num [Nat.factorial]]
    ring
  -- Scale-t moments in the form needed here.
  have hmom : ∀ j : ℕ, (∫ x, x ^ (4 * j) * q x) =
      ((4 * j - 1)‼ : ℝ) * Real.sqrt (2 * π) *
        t ^ (-(2 * (j : ℝ) + 1 / 2)) := by
    intro j
    have h := integral_pow_mul_exp_neg_t_sq_half (2 * j) ht
    simp only [hq_def]
    rw [show 2 * (2 * j) = 4 * j by ring] at h
    rw [h]
    congr 2
    push_cast
    ring
  -- Pointwise expansion of the quartic exponential factor.
  have hsplit : ∀ x : ℝ,
      Real.exp (-(t * (x ^ 2 / 2 + b * x ^ 4))) =
      (∑ j ∈ Finset.range (n + 1),
        (-(t * b)) ^ j / (Nat.factorial j : ℝ) * (x ^ (4 * j) * q x)) +
      q x * expRemainder (n + 1) (t * b * x ^ 4) := by
    intro x
    rw [show -(t * (x ^ 2 / 2 + b * x ^ 4)) =
        -(t * x ^ 2) / 2 + -(t * b * x ^ 4) by ring, Real.exp_add]
    unfold expRemainder
    simp only [hq_def]
    rw [mul_sub, Finset.mul_sum]
    have hterm : ∀ j ∈ Finset.range (n + 1),
        Real.exp (-(t * x ^ 2) / 2) *
          ((-(t * b * x ^ 4)) ^ j / (Nat.factorial j : ℝ)) =
        (-(t * b)) ^ j / (Nat.factorial j : ℝ) *
          (x ^ (4 * j) * Real.exp (-(t * x ^ 2) / 2)) := by
      intro j _
      rw [show -(t * b * x ^ 4) = -(t * b) * x ^ 4 by ring, mul_pow,
        ← pow_mul]
      ring
    rw [Finset.sum_congr rfl hterm]
    ring
  -- Integrability of the pieces.
  have hint_term : ∀ j : ℕ, Integrable (fun x : ℝ ↦
      (-(t * b)) ^ j / (Nat.factorial j : ℝ) * (x ^ (4 * j) * q x)) :=
    fun j ↦ (hint_pow (4 * j)).const_mul _
  have hint_sum : Integrable (fun x : ℝ ↦ ∑ j ∈ Finset.range (n + 1),
      (-(t * b)) ^ j / (Nat.factorial j : ℝ) * (x ^ (4 * j) * q x)) :=
    integrable_finset_sum _ fun j _ ↦ hint_term j
  have hrem_bound : ∀ x : ℝ,
      |q x * expRemainder (n + 1) (t * b * x ^ 4)| ≤
      (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
        (x ^ (4 * (n + 1)) * q x) := by
    intro x
    have hs : 0 ≤ t * b * x ^ 4 := by positivity
    have h1 := abs_expRemainder_le (n + 1) hs
    rw [abs_mul, abs_of_pos (hq_pos x)]
    calc q x * |expRemainder (n + 1) (t * b * x ^ 4)|
        ≤ q x * ((t * b * x ^ 4) ^ (n + 1) /
            (Nat.factorial (n + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (hq_pos x).le
      _ = (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
            (x ^ (4 * (n + 1)) * q x) := by
          rw [mul_pow, ← pow_mul]
          ring
  have hcont_rem : Continuous
      (fun x : ℝ ↦ q x * expRemainder (n + 1) (t * b * x ^ 4)) := by
    have h1 : Continuous fun x : ℝ ↦ t * b * x ^ 4 := by fun_prop
    have h2 := (expRemainder_continuous (n + 1)).comp h1
    have h3 : Continuous q := by
      simp only [hq_def]
      fun_prop
    exact h3.mul h2
  have hint_rem : Integrable
      (fun x ↦ q x * expRemainder (n + 1) (t * b * x ^ 4)) := by
    have hg : Integrable (fun x : ℝ ↦
        (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
          (x ^ (4 * (n + 1)) * q x)) :=
      (hint_pow (4 * (n + 1))).const_mul _
    apply hg.mono' hcont_rem.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hrem_bound x
  -- Assemble the integral.
  have hZ : partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t =
      (∑ j ∈ Finset.range (n + 1),
        (-(t * b)) ^ j / (Nat.factorial j : ℝ) * ∫ x, x ^ (4 * j) * q x) +
      ∫ x, q x * expRemainder (n + 1) (t * b * x ^ 4) := by
    unfold partitionFunction
    have hfun : (∫ x : ℝ, Real.exp (-(t * (x ^ 2 / 2 + b * x ^ 4)))) =
        ∫ x, ((∑ j ∈ Finset.range (n + 1),
          (-(t * b)) ^ j / (Nat.factorial j : ℝ) * (x ^ (4 * j) * q x)) +
          q x * expRemainder (n + 1) (t * b * x ^ 4)) := by
      congr 1
      funext x
      exact hsplit x
    rw [hfun, MeasureTheory.integral_add hint_sum hint_rem,
      MeasureTheory.integral_finset_sum _ fun j _ ↦ hint_term j]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦
      MeasureTheory.integral_const_mul _ _
  -- Evaluate each term against the moments.
  have hcoeff : ∀ j ∈ Finset.range (n + 1),
      (-(t * b)) ^ j / (Nat.factorial j : ℝ) * ∫ x, x ^ (4 * j) * q x =
      Real.sqrt (2 * π) * ((-b) ^ j * ((4 * j - 1)‼ : ℝ) /
        (Nat.factorial j : ℝ) * t ^ (-((j : ℝ) + 1 / 2))) := by
    intro j _
    rw [hmom j, show (-(t * b)) = t * (-b) by ring, mul_pow]
    calc t ^ j * (-b) ^ j / (Nat.factorial j : ℝ) *
          (((4 * j - 1)‼ : ℝ) * Real.sqrt (2 * π) *
            t ^ (-(2 * (j : ℝ) + 1 / 2)))
        = Real.sqrt (2 * π) * ((-b) ^ j * ((4 * j - 1)‼ : ℝ) /
            (Nat.factorial j : ℝ)) *
            (t ^ j * t ^ (-(2 * (j : ℝ) + 1 / 2))) := by ring
      _ = Real.sqrt (2 * π) * ((-b) ^ j * ((4 * j - 1)‼ : ℝ) /
            (Nat.factorial j : ℝ) * t ^ (-((j : ℝ) + 1 / 2))) := by
          rw [rpow_shift ht]
          ring
  -- The expansion error is exactly the remainder integral.
  have hE : partitionFunction (fun x ↦ x ^ 2 / 2 + b * x ^ 4) t
      - Real.sqrt (2 * π) * ∑ j ∈ Finset.range (n + 1),
          (-b) ^ j * ((4 * j - 1)‼ : ℝ) / (Nat.factorial j : ℝ) *
            t ^ (-((j : ℝ) + 1 / 2)) =
      ∫ x, q x * expRemainder (n + 1) (t * b * x ^ 4) := by
    rw [hZ, Finset.sum_congr rfl hcoeff, ← Finset.mul_sum]
    ring
  rw [hE]
  -- Bound the remainder integral by the (n+1)-st moment.
  have hg : Integrable (fun x : ℝ ↦
      (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
        (x ^ (4 * (n + 1)) * q x)) :=
    (hint_pow (4 * (n + 1))).const_mul _
  have h1 : |∫ x, q x * expRemainder (n + 1) (t * b * x ^ 4)| ≤
      ∫ x, (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
        (x ^ (4 * (n + 1)) * q x) := by
    calc |∫ x, q x * expRemainder (n + 1) (t * b * x ^ 4)|
        ≤ ∫ x, |q x * expRemainder (n + 1) (t * b * x ^ 4)| := by
          have := MeasureTheory.norm_integral_le_integral_norm
            (f := fun x ↦ q x * expRemainder (n + 1) (t * b * x ^ 4))
            (μ := volume)
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∫ x, (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
            (x ^ (4 * (n + 1)) * q x) :=
          MeasureTheory.integral_mono hint_rem.abs hg fun x ↦ hrem_bound x
  refine h1.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, hmom (n + 1)]
  have hb' : (t * b) ^ (n + 1) = t ^ (n + 1) * b ^ (n + 1) := mul_pow t b _
  calc (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
        (((4 * (n + 1) - 1)‼ : ℝ) * Real.sqrt (2 * π) *
          t ^ (-(2 * ((n + 1 : ℕ) : ℝ) + 1 / 2)))
      = Real.sqrt (2 * π) * b ^ (n + 1) * ((4 * (n + 1) - 1)‼ : ℝ) /
          (Nat.factorial (n + 1) : ℝ) *
          (t ^ (n + 1) * t ^ (-(2 * ((n + 1 : ℕ) : ℝ) + 1 / 2))) := by
        rw [hb']
        ring
    _ = Real.sqrt (2 * π) * b ^ (n + 1) * ((4 * (n + 1) - 1)‼ : ℝ) /
          (Nat.factorial (n + 1) : ℝ) *
          t ^ (-(((n + 1) : ℕ) : ℝ) - 1 / 2) := by
        rw [rpow_shift ht (n + 1)]
        congr 1
        congr 1
        push_cast
        ring

end Laplace.OneD
