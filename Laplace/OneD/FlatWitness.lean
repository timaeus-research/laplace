/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.FlatInvisible

/-!
# The classic flat witness `e^(-1/x²)`

The germbij note's Proposition 4.1 counterexample, witnessed: the
function `x ↦ e^(-1/x²)` (extended by `0` at `0`) is continuous,
bounded by `1`, nonnegative, and flat at `0` — dominated by
`n! * x^(2n)` for every `n`, *globally*, via the single-term bound
`sⁿ/n! ≤ eˢ` at `s = 1/x²`. Feeding it to
`flat_perturbation_invisible` gives a concrete smooth-category
perturbation that no expansion order can see
(`flat_witness_invisible`, `flat_witness_superpolynomial`).
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- The classic flat function: `e^(-1/x²)` for `x ≠ 0`, extended by
`0` at `x = 0`. -/
noncomputable def flatWitness (x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.exp (-(1 / x ^ 2))

theorem flatWitness_nonneg (x : ℝ) : 0 ≤ flatWitness x := by
  unfold flatWitness
  split_ifs
  · exact le_refl 0
  · exact (Real.exp_pos _).le

theorem flatWitness_le_one (x : ℝ) : flatWitness x ≤ 1 := by
  unfold flatWitness
  split_ifs with hx
  · norm_num
  · have h : -(1 / x ^ 2) ≤ 0 := neg_nonpos.mpr (by positivity)
    calc Real.exp (-(1 / x ^ 2)) ≤ Real.exp 0 := Real.exp_le_exp.mpr h
      _ = 1 := Real.exp_zero

/-- The global factorial bound: `e^(-1/x²) ≤ n! · x^(2n)` for every
`x` and every `n`. From the single term of the exponential series,
`sⁿ/n! ≤ eˢ` at `s = 1/x²`. -/
theorem flatWitness_le_factorial_mul_pow (n : ℕ) (x : ℝ) :
    flatWitness x ≤ (n.factorial : ℝ) * x ^ (2 * n) := by
  unfold flatWitness
  split_ifs with hx
  · subst hx
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · rw [zero_pow (by omega : 2 * n ≠ 0), mul_zero]
  · have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    set s : ℝ := 1 / x ^ 2 with hs
    have hs0 : (0 : ℝ) < s := by positivity
    have hterm : s ^ n / (n.factorial : ℝ) ≤ Real.exp s := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg hs0.le (n + 1))
      exact Finset.single_le_sum
        (f := fun i ↦ s ^ i / (i.factorial : ℝ))
        (fun i _ ↦ by positivity) (Finset.self_mem_range_succ n)
    have hxs : x ^ 2 * s = 1 := by
      rw [hs]
      field_simp
    have h2 : x ^ (2 * n) * s ^ n = 1 := by
      rw [pow_mul, ← mul_pow, hxs, one_pow]
    have hpow : (0 : ℝ) ≤ x ^ (2 * n) := by
      rw [pow_mul]
      positivity
    have hfact : (0 : ℝ) < (n.factorial : ℝ) :=
      Nat.cast_pos.mpr n.factorial_pos
    have hkey : (1 : ℝ) ≤ (n.factorial : ℝ) * x ^ (2 * n) * Real.exp s := by
      calc (1 : ℝ) = x ^ (2 * n) * s ^ n := h2.symm
        _ = (n.factorial : ℝ) * x ^ (2 * n) *
            (s ^ n / (n.factorial : ℝ)) := by
              field_simp
        _ ≤ (n.factorial : ℝ) * x ^ (2 * n) * Real.exp s :=
              mul_le_mul_of_nonneg_left hterm
                (mul_nonneg hfact.le hpow)
    rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos s)]
    linarith

theorem flatWitness_continuous : Continuous flatWitness := by
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx₀ : x₀ = 0
  · subst hx₀
    have h0 : flatWitness 0 = 0 := by simp [flatWitness]
    rw [ContinuousAt, h0]
    apply squeeze_zero flatWitness_nonneg (g := fun x : ℝ ↦ x ^ 2)
    · intro x
      calc flatWitness x
          ≤ ((Nat.factorial 1 : ℕ) : ℝ) * x ^ (2 * 1) :=
            flatWitness_le_factorial_mul_pow 1 x
        _ = x ^ 2 := by norm_num
    · simpa using (continuous_pow 2).tendsto (0 : ℝ)
  · have hc : ContinuousAt (fun x : ℝ ↦ Real.exp (-(1 / x ^ 2))) x₀ := by
      apply Real.continuous_exp.continuousAt.comp
      apply ContinuousAt.neg
      exact continuousAt_const.div (continuousAt_pow x₀ 2)
        (pow_ne_zero 2 hx₀)
    apply hc.congr
    filter_upwards [eventually_ne_nhds hx₀] with x hx
    simp [flatWitness, hx]

/-- The local-flatness hypothesis of `flat_perturbation_invisible`,
witnessed globally with `C = n!` and `δ = 1`. -/
theorem flatWitness_flat (n : ℕ) : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
    ∀ x : ℝ, |x| ≤ δ → flatWitness x ≤ C * x ^ (2 * n) :=
  ⟨(n.factorial : ℝ), 1, Nat.cast_nonneg _, one_pos,
    fun x _ ↦ flatWitness_le_factorial_mul_pow n x⟩

/-- **The germbij Proposition 4.1 counterexample, witnessed.**
Perturbing the harmonic potential by `e^(-1/x²)` changes every
compactly-supported-observable integral by `O(t^(-N))` for every
`N`. -/
theorem flat_witness_invisible {φ : ℝ → ℝ}
    (hφ_c : Continuous φ) (hφ_s : HasCompactSupport φ) :
    ∀ N : ℕ, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |(∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2)))) -
        ∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2 + flatWitness x)))| ≤
      K / t ^ N :=
  flat_perturbation_invisible flatWitness_continuous flatWitness_nonneg
    flatWitness_le_one flatWitness_flat hφ_c hφ_s

/-- The witnessed difference decays superpolynomially, in the
`Laplace.Decay` vocabulary. -/
theorem flat_witness_superpolynomial {φ : ℝ → ℝ}
    (hφ_c : Continuous φ) (hφ_s : HasCompactSupport φ) :
    ∀ N : ℕ,
      (fun t : ℝ ↦ (∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2)))) -
        ∫ x : ℝ, φ x * Real.exp (-(t * (x ^ 2 / 2 + flatWitness x))))
        =o[Filter.atTop] fun t : ℝ ↦ t ^ (-(N : ℝ)) :=
  flat_perturbation_superpolynomial flatWitness_continuous
    flatWitness_nonneg flatWitness_le_one flatWitness_flat hφ_c hφ_s

end Laplace.OneD
