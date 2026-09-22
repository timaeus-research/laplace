/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CovKOrder2
import Laplace.Multi.LocalisedAnharmonicLLC

/-!
# The localised anharmonic mean to second order

Tides 65–67 certified `t⟨x⟩_loc = c + O(1/t)` on the exact localised anharmonic measure,
`c = −α/(2λ²) + g x₀/λ`. This file identifies the next coefficient: `t⟨x⟩_loc = c + c'/t + O(t⁻²)`
(eq:mean's `O(S²)` term on the localised measure).
-/

open Real MeasureTheory Filter Topology
open scoped Nat

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

/-! ### Taylor remainders of the exponential, to any order -/

section Taylor

/-- `|e^y − ∑_{m<n} y^m/m!| ≤ (e^M + n)|y|^n` for `y ≤ M` and `n ≥ 2`. -/
theorem abs_exp_sub_taylor_le {y M : ℝ} {n : ℕ} (hn : 2 ≤ n) (hy : y ≤ M) :
    |Real.exp y - ∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ)| ≤
      (Real.exp M + n) * |y| ^ n := by
  have hn0 : 0 < n := by omega
  have hyn : 0 ≤ |y| ^ n := by positivity
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt |y| 1 with h1 | h1
  · have h := Real.exp_bound h1 hn0
    have hc : (((n.succ : ℕ) : ℝ) / ((n.factorial : ℝ) * (n : ℝ))) ≤ 2 := by
      have hf : (1 : ℝ) ≤ n.factorial := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.factorial_ne_zero
      have hn1 : (1 : ℝ) ≤ n := by linarith
      rw [div_le_iff₀ (by positivity)]
      push_cast
      nlinarith
    calc |Real.exp y - ∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ)|
        ≤ |y| ^ n * (((n.succ : ℕ) : ℝ) / ((n.factorial : ℝ) * (n : ℝ))) := h
      _ ≤ |y| ^ n * 2 := by gcongr
      _ ≤ (Real.exp M + n) * |y| ^ n := by nlinarith [Real.exp_pos M]
  · have hexp : Real.exp y ≤ Real.exp M := Real.exp_le_exp.mpr hy
    have hterm : ∀ m ∈ Finset.range n, |y ^ m / (m.factorial : ℝ)| ≤ |y| ^ n := by
      intro m hm
      rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < m.factorial)]
      have hf : (1 : ℝ) ≤ m.factorial := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr m.factorial_ne_zero
      have hpow : |y| ^ m ≤ |y| ^ n :=
        pow_le_pow_right₀ h1.le (Finset.mem_range.mp hm).le
      calc |y| ^ m / (m.factorial : ℝ) ≤ |y| ^ m / 1 := by
            gcongr
        _ = |y| ^ m := div_one _
        _ ≤ |y| ^ n := hpow
    have hsum : |∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ)| ≤ n * |y| ^ n := by
      calc |∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ)|
          ≤ ∑ m ∈ Finset.range n, |y ^ m / (m.factorial : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _m ∈ Finset.range n, |y| ^ n := Finset.sum_le_sum hterm
        _ = n * |y| ^ n := by simp
    have h1n : 1 ≤ |y| ^ n := one_le_pow₀ h1.le
    calc |Real.exp y - ∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ)|
        ≤ |Real.exp y| + |∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ)| := abs_sub _ _
      _ ≤ Real.exp M + n * |y| ^ n := by
          gcongr
          rw [abs_of_pos (Real.exp_pos _)]; exact hexp
      _ ≤ (Real.exp M + n) * |y| ^ n := by nlinarith [Real.exp_pos M]

/-- `(p + q)^n ≤ 2^n (p^n + q^n)` for `p, q ≥ 0`. -/
theorem add_pow_le_two_pow_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (n : ℕ) :
    (p + q) ^ n ≤ 2 ^ n * (p ^ n + q ^ n) := by
  have h : p + q ≤ 2 * max p q := by
    have := le_max_left p q
    have := le_max_right p q
    linarith
  calc (p + q) ^ n ≤ (2 * max p q) ^ n := by gcongr
    _ = 2 ^ n * max p q ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (p ^ n + q ^ n) := by
        gcongr
        rcases le_total p q with hpq | hpq
        · rw [max_eq_right hpq]; nlinarith [pow_nonneg hp n]
        · rw [max_eq_left hpq]; nlinarith [pow_nonneg hq n]

/-- `|ax − bx²|^n ≤ 2^n(|a|^n |x|^n + |b|^n x^{2n})`. -/
theorem abs_locExponent_pow_le (a b x : ℝ) (n : ℕ) :
    |a * x - b * x ^ 2| ^ n ≤ 2 ^ n * (|a| ^ n * |x| ^ n + |b| ^ n * (x ^ 2) ^ n) := by
  have h1 : |a * x - b * x ^ 2| ≤ |a| * |x| + |b| * x ^ 2 := by
    calc |a * x - b * x ^ 2| ≤ |a * x| + |b * x ^ 2| := abs_sub _ _
      _ = |a| * |x| + |b| * x ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x)]
  calc |a * x - b * x ^ 2| ^ n ≤ (|a| * |x| + |b| * x ^ 2) ^ n := by gcongr
    _ ≤ 2 ^ n * ((|a| * |x|) ^ n + (|b| * x ^ 2) ^ n) :=
        add_pow_le_two_pow_mul (by positivity) (by positivity) n
    _ = 2 ^ n * (|a| ^ n * |x| ^ n + |b| ^ n * (x ^ 2) ^ n) := by ring

end Taylor

/-! ### The localised weight to fourth order -/

section Weight

variable {g x₀ : ℝ}

/-- `|φ − ∑_{m<n} y^m/m!| ≤ (e^{g x₀²/2} + n)|y|^n`, `y = g x₀ x − (g/2)x²`, `n ≥ 2`. -/
theorem locWeight_taylor_le (hg : 0 ≤ g) {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    |locWeight g x₀ x -
        ∑ m ∈ Finset.range n, (g * x₀ * x - g / 2 * x ^ 2) ^ m / (m.factorial : ℝ)| ≤
      (Real.exp (g * x₀ ^ 2 / 2) + n) * |g * x₀ * x - g / 2 * x ^ 2| ^ n := by
  have hyM : g * x₀ * x - g / 2 * x ^ 2 ≤ g * x₀ ^ 2 / 2 := by
    nlinarith [mul_nonneg hg (sq_nonneg (x - x₀))]
  exact abs_exp_sub_taylor_le hn hyM

/-- The coefficients of `x·P₄(y)` (`a = g x₀`, `b = g/2`). -/
noncomputable def locP₃ (g x₀ : ℝ) : ℝ := (g * x₀) ^ 2 / 2 - g / 2
noncomputable def locP₄ (g x₀ : ℝ) : ℝ := (g * x₀) ^ 3 / 6 - g * x₀ * (g / 2)
noncomputable def locP₅ (g x₀ : ℝ) : ℝ :=
  (g * x₀) ^ 4 / 24 - (g * x₀) ^ 2 * (g / 2) / 2 + (g / 2) ^ 2 / 2
noncomputable def locQ₆' (g x₀ : ℝ) : ℝ := g * x₀ * (g / 2) ^ 2 / 2 - (g * x₀) ^ 3 * (g / 2) / 6
noncomputable def locQ₇' (g x₀ : ℝ) : ℝ := (g * x₀) ^ 2 * (g / 2) ^ 2 / 4 - (g / 2) ^ 3 / 6
noncomputable def locQ₈' (g x₀ : ℝ) : ℝ := -(g * x₀ * (g / 2) ^ 3 / 6)
noncomputable def locQ₉' (g : ℝ) : ℝ := (g / 2) ^ 4 / 24

theorem mul_P4_eq (g x₀ x : ℝ) :
    x * ∑ m ∈ Finset.range 5, (g * x₀ * x - g / 2 * x ^ 2) ^ m / (m.factorial : ℝ) =
      x + g * x₀ * x ^ 2 + locP₃ g x₀ * x ^ 3 + locP₄ g x₀ * x ^ 4 + locP₅ g x₀ * x ^ 5 +
        (locQ₆' g x₀ * x ^ 6 + locQ₇' g x₀ * x ^ 7 + locQ₈' g x₀ * x ^ 8 + locQ₉' g * x ^ 9) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  unfold locP₃ locP₄ locP₅ locQ₆' locQ₇' locQ₈' locQ₉'
  push_cast
  ring

/-- The even envelope of the numerator's remainder. -/
noncomputable def locE₆ (g x₀ : ℝ) : ℝ :=
  |locQ₆' g x₀| + |locQ₇' g x₀| / 2 + 32 * (Real.exp (g * x₀ ^ 2 / 2) + 5) * |g * x₀| ^ 5
noncomputable def locE₈ (g x₀ : ℝ) : ℝ := |locQ₇' g x₀| / 2 + |locQ₈' g x₀| + |locQ₉' g| / 2
noncomputable def locE₁₀ (g x₀ : ℝ) : ℝ :=
  |locQ₉' g| / 2 + 16 * (Real.exp (g * x₀ ^ 2 / 2) + 5) * |g / 2| ^ 5
noncomputable def locE₁₂ (g x₀ : ℝ) : ℝ := 16 * (Real.exp (g * x₀ ^ 2 / 2) + 5) * |g / 2| ^ 5

theorem locE₆_nonneg (g x₀ : ℝ) : 0 ≤ locE₆ g x₀ := by unfold locE₆; positivity
theorem locE₈_nonneg (g x₀ : ℝ) : 0 ≤ locE₈ g x₀ := by unfold locE₈; positivity
theorem locE₁₀_nonneg (g x₀ : ℝ) : 0 ≤ locE₁₀ g x₀ := by unfold locE₁₀; positivity
theorem locE₁₂_nonneg (g x₀ : ℝ) : 0 ≤ locE₁₂ g x₀ := by unfold locE₁₂; positivity

/-- **The numerator to degree five**:
`|xφ − (x + ax² + p₃x³ + p₄x⁴ + p₅x⁵)| ≤ E₆x⁶ + E₈x⁸ + E₁₀x¹⁰ + E₁₂x¹²`. -/
theorem locNumerator_pointwise5 (hg : 0 ≤ g) (x : ℝ) :
    |x * locWeight g x₀ x - (x + g * x₀ * x ^ 2 + locP₃ g x₀ * x ^ 3 + locP₄ g x₀ * x ^ 4 +
        locP₅ g x₀ * x ^ 5)| ≤
      locE₆ g x₀ * x ^ 6 + locE₈ g x₀ * x ^ 8 + locE₁₀ g x₀ * x ^ 10 + locE₁₂ g x₀ * x ^ 12 := by
  set y := g * x₀ * x - g / 2 * x ^ 2 with hy
  set C := Real.exp (g * x₀ ^ 2 / 2) + 5 with hC
  have hC0 : 0 ≤ C := by positivity
  have hT : |locWeight g x₀ x - ∑ m ∈ Finset.range 5, y ^ m / (m.factorial : ℝ)| ≤ C * |y| ^ 5 := by
    have := locWeight_taylor_le (x₀ := x₀) hg (n := 5) (by norm_num) x
    simpa using this
  have hy5 : |y| ^ 5 ≤ 2 ^ 5 * (|g * x₀| ^ 5 * |x| ^ 5 + |g / 2| ^ 5 * (x ^ 2) ^ 5) :=
    abs_locExponent_pow_le (g * x₀) (g / 2) x 5
  have e : x * locWeight g x₀ x - (x + g * x₀ * x ^ 2 + locP₃ g x₀ * x ^ 3 + locP₄ g x₀ * x ^ 4 +
      locP₅ g x₀ * x ^ 5) =
      x * (locWeight g x₀ x - ∑ m ∈ Finset.range 5, y ^ m / (m.factorial : ℝ)) +
        (locQ₆' g x₀ * x ^ 6 + locQ₇' g x₀ * x ^ 7 + locQ₈' g x₀ * x ^ 8 + locQ₉' g * x ^ 9) := by
    have := mul_P4_eq g x₀ x
    rw [← hy] at this
    linear_combination this
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hx6 : x ^ 6 = |x| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : x ^ 8 = |x| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx10 : x ^ 10 = |x| ^ 10 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx12 : x ^ 12 = |x| ^ 12 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h7 : |x| ^ 7 ≤ (|x| ^ 6 + |x| ^ 8) / 2 := by nlinarith [sq_nonneg (|x| ^ 3 - |x| ^ 4)]
  have h9 : |x| ^ 9 ≤ (|x| ^ 8 + |x| ^ 10) / 2 := by nlinarith [sq_nonneg (|x| ^ 4 - |x| ^ 5)]
  have h11 : |x| ^ 11 ≤ (|x| ^ 10 + |x| ^ 12) / 2 := by nlinarith [sq_nonneg (|x| ^ 5 - |x| ^ 6)]
  have hmain : |x * (locWeight g x₀ x - ∑ m ∈ Finset.range 5, y ^ m / (m.factorial : ℝ)) +
        (locQ₆' g x₀ * x ^ 6 + locQ₇' g x₀ * x ^ 7 + locQ₈' g x₀ * x ^ 8 + locQ₉' g * x ^ 9)|
      ≤ |x| * (C * (2 ^ 5 * (|g * x₀| ^ 5 * |x| ^ 5 + |g / 2| ^ 5 * (x ^ 2) ^ 5))) +
        (|locQ₆' g x₀| * |x| ^ 6 + |locQ₇' g x₀| * |x| ^ 7 + |locQ₈' g x₀| * |x| ^ 8 +
          |locQ₉' g| * |x| ^ 9) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul x]
    gcongr
    · exact hT.trans (mul_le_mul_of_nonneg_left hy5 hC0)
    · calc |locQ₆' g x₀ * x ^ 6 + locQ₇' g x₀ * x ^ 7 + locQ₈' g x₀ * x ^ 8 + locQ₉' g * x ^ 9|
          ≤ |locQ₆' g x₀ * x ^ 6 + locQ₇' g x₀ * x ^ 7 + locQ₈' g x₀ * x ^ 8| +
            |locQ₉' g * x ^ 9| := abs_add_le _ _
        _ ≤ |locQ₆' g x₀ * x ^ 6| + |locQ₇' g x₀ * x ^ 7| + |locQ₈' g x₀ * x ^ 8| +
            |locQ₉' g * x ^ 9| := add_le_add (abs_add_three _ _ _) le_rfl
        _ = |locQ₆' g x₀| * |x| ^ 6 + |locQ₇' g x₀| * |x| ^ 7 + |locQ₈' g x₀| * |x| ^ 8 +
            |locQ₉' g| * |x| ^ 9 := by simp only [abs_mul, abs_pow]
  rw [e]
  refine hmain.trans ?_
  rw [hx2, hx6, hx8, hx10, hx12]
  have hgx : 0 ≤ |g * x₀| ^ 5 := by positivity
  have hgb : 0 ≤ |g / 2| ^ 5 := by positivity
  calc _ = 32 * C * |g * x₀| ^ 5 * |x| ^ 6 + 32 * C * |g / 2| ^ 5 * |x| ^ 11 +
        (|locQ₆' g x₀| * |x| ^ 6 + |locQ₇' g x₀| * |x| ^ 7 + |locQ₈' g x₀| * |x| ^ 8 +
          |locQ₉' g| * |x| ^ 9) := by ring
    _ ≤ 32 * C * |g * x₀| ^ 5 * |x| ^ 6 + 32 * C * |g / 2| ^ 5 * ((|x| ^ 10 + |x| ^ 12) / 2) +
        (|locQ₆' g x₀| * |x| ^ 6 + |locQ₇' g x₀| * ((|x| ^ 6 + |x| ^ 8) / 2) +
          |locQ₈' g x₀| * |x| ^ 8 + |locQ₉' g| * ((|x| ^ 8 + |x| ^ 10) / 2)) := by gcongr
    _ = locE₆ g x₀ * |x| ^ 6 + locE₈ g x₀ * |x| ^ 8 + locE₁₀ g x₀ * |x| ^ 10 +
        locE₁₂ g x₀ * |x| ^ 12 := by
        rw [hC]
        unfold locE₆ locE₈ locE₁₀ locE₁₂
        ring

/-- The coefficients of `P₃(y)` beyond degree two. -/
noncomputable def locR₃' (g x₀ : ℝ) : ℝ := (g * x₀) ^ 3 / 6 - g * x₀ * (g / 2)
noncomputable def locR₄' (g x₀ : ℝ) : ℝ := -((g / 2) * ((g * x₀) ^ 2 - g / 2) / 2)
noncomputable def locR₅' (g x₀ : ℝ) : ℝ := g * x₀ * (g / 2) ^ 2 / 2
noncomputable def locR₆' (g : ℝ) : ℝ := -((g / 2) ^ 3 / 6)

theorem P3_eq (g x₀ x : ℝ) :
    ∑ m ∈ Finset.range 4, (g * x₀ * x - g / 2 * x ^ 2) ^ m / (m.factorial : ℝ) =
      1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 +
        (locR₃' g x₀ * x ^ 3 + locR₄' g x₀ * x ^ 4 + locR₅' g x₀ * x ^ 5 + locR₆' g * x ^ 6) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  unfold locP₃ locR₃' locR₄' locR₅' locR₆'
  push_cast
  ring

/-- **The weight to degree six with an even remainder**:
`|φ − (1 + ax + p₃x² + r₃x³ + r₄x⁴ + r₅x⁵ + r₆x⁶)| ≤ F₄x⁴ + F₈x⁸`. -/
theorem locDenominator_pointwise3 (hg : 0 ≤ g) (x : ℝ) :
    |locWeight g x₀ x - (1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 + locR₃' g x₀ * x ^ 3 +
        locR₄' g x₀ * x ^ 4 + locR₅' g x₀ * x ^ 5 + locR₆' g * x ^ 6)| ≤
      16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 * x ^ 4 +
        16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * x ^ 8 := by
  set y := g * x₀ * x - g / 2 * x ^ 2 with hy
  set C := Real.exp (g * x₀ ^ 2 / 2) + 4 with hC
  have hC0 : 0 ≤ C := by positivity
  have hT : |locWeight g x₀ x - ∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)| ≤ C * |y| ^ 4 := by
    have := locWeight_taylor_le (x₀ := x₀) hg (n := 4) (by norm_num) x
    simpa using this
  have hy4 : |y| ^ 4 ≤ 2 ^ 4 * (|g * x₀| ^ 4 * |x| ^ 4 + |g / 2| ^ 4 * (x ^ 2) ^ 4) :=
    abs_locExponent_pow_le (g * x₀) (g / 2) x 4
  have e : locWeight g x₀ x - (1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 + locR₃' g x₀ * x ^ 3 +
      locR₄' g x₀ * x ^ 4 + locR₅' g x₀ * x ^ 5 + locR₆' g * x ^ 6) =
      locWeight g x₀ x - ∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ) := by
    have := P3_eq g x₀ x
    rw [← hy] at this
    linear_combination this
  have hx4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : (x ^ 2) ^ 4 = x ^ 8 := by ring
  rw [e]
  calc |locWeight g x₀ x - ∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)|
      ≤ C * (2 ^ 4 * (|g * x₀| ^ 4 * |x| ^ 4 + |g / 2| ^ 4 * (x ^ 2) ^ 4)) :=
        hT.trans (mul_le_mul_of_nonneg_left hy4 hC0)
    _ = _ := by
        rw [hx4, hx8, hC]
        ring

end Weight

/-! ### Linearity helpers -/

section Lin

variable {L : ℝ → ℝ} {t : ℝ}

theorem gibbs_add' {f h : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * L x))))
    (hh : Integrable (fun x => h x * Real.exp (-(t * L x)))) :
    _root_.Laplace.gibbsExpectation L t (fun x => f x + h x) =
      _root_.Laplace.gibbsExpectation L t f + _root_.Laplace.gibbsExpectation L t h := by
  have e : (fun x => f x + h x) = fun x => 1 * f x + 1 * h x := by funext x; ring
  rw [e, gibbsExpectation_lin hf hh]
  ring

theorem gibbs_sub' {f h : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * L x))))
    (hh : Integrable (fun x => h x * Real.exp (-(t * L x)))) :
    _root_.Laplace.gibbsExpectation L t (fun x => f x - h x) =
      _root_.Laplace.gibbsExpectation L t f - _root_.Laplace.gibbsExpectation L t h := by
  have e : (fun x => f x - h x) = fun x => 1 * f x + (-1) * h x := by funext x; ring
  rw [e, gibbsExpectation_lin hf hh]
  ring

theorem gibbs_lin4 {a b c d : ℝ} {f h k l : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * L x))))
    (hh : Integrable (fun x => h x * Real.exp (-(t * L x))))
    (hk : Integrable (fun x => k x * Real.exp (-(t * L x))))
    (hl : Integrable (fun x => l x * Real.exp (-(t * L x)))) :
    _root_.Laplace.gibbsExpectation L t (fun x => a * f x + b * h x + c * k x + d * l x) =
      a * _root_.Laplace.gibbsExpectation L t f + b * _root_.Laplace.gibbsExpectation L t h +
        c * _root_.Laplace.gibbsExpectation L t k + d * _root_.Laplace.gibbsExpectation L t l := by
  have h3 : Integrable (fun x => (a * f x + b * h x + c * k x) * Real.exp (-(t * L x))) := by
    have := ((hf.const_mul a).add (hh.const_mul b)).add (hk.const_mul c)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have e : (fun x => a * f x + b * h x + c * k x + d * l x) =
      fun x => 1 * (a * f x + b * h x + c * k x) + d * l x := by funext x; ring
  rw [e, gibbsExpectation_lin h3 hl, gibbs_lin3 hf hh hk]
  ring

theorem gibbs_lin5 {a b c d e : ℝ} {f h k l m : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * L x))))
    (hh : Integrable (fun x => h x * Real.exp (-(t * L x))))
    (hk : Integrable (fun x => k x * Real.exp (-(t * L x))))
    (hl : Integrable (fun x => l x * Real.exp (-(t * L x))))
    (hm : Integrable (fun x => m x * Real.exp (-(t * L x)))) :
    _root_.Laplace.gibbsExpectation L t
        (fun x => a * f x + b * h x + c * k x + d * l x + e * m x) =
      a * _root_.Laplace.gibbsExpectation L t f + b * _root_.Laplace.gibbsExpectation L t h +
        c * _root_.Laplace.gibbsExpectation L t k + d * _root_.Laplace.gibbsExpectation L t l +
        e * _root_.Laplace.gibbsExpectation L t m := by
  have h4 : Integrable (fun x => (a * f x + b * h x + c * k x + d * l x) *
      Real.exp (-(t * L x))) := by
    have := (((hf.const_mul a).add (hh.const_mul b)).add (hk.const_mul c)).add (hl.const_mul d)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have e' : (fun x => a * f x + b * h x + c * k x + d * l x + e * m x) =
      fun x => 1 * (a * f x + b * h x + c * k x + d * l x) + e * m x := by funext x; ring
  rw [e', gibbsExpectation_lin h4 hm, gibbs_lin4 hf hh hk hl]
  ring

end Lin

/-! ### The numerator and denominator to second order -/

section Expansions

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `|⟨xφ⟩ − (⟨x⟩ + a⟨x²⟩ + p₃⟨x³⟩ + p₄⟨x⁴⟩ + p₅⟨x⁵⟩)| ≤ E₆⟨x⁶⟩ + E₈⟨x⁸⟩ + E₁₀⟨x¹⁰⟩ + E₁₂⟨x¹²⟩`. -/
theorem locNumerator_expansion5 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x * locWeight g x₀ x) -
      (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) +
        locP₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locP₅ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5))| ≤
      locE₆ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locE₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) +
        locE₁₀ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 10) +
        locE₁₂ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 12) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_mul_locWeight hlam hgamma hdisc hg ht (x₀ := x₀)
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht
  have h1 := hp 1
  simp only [pow_one] at h1
  have hP : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x + g * x₀ * x ^ 2 + locP₃ g x₀ * x ^ 3 + locP₄ g x₀ * x ^ 4 + locP₅ g x₀ * x ^ 5) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) +
        locP₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locP₅ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) := by
    have e : (fun x : ℝ => x + g * x₀ * x ^ 2 + locP₃ g x₀ * x ^ 3 + locP₄ g x₀ * x ^ 4 +
        locP₅ g x₀ * x ^ 5) = fun x => 1 * x + g * x₀ * x ^ 2 + locP₃ g x₀ * x ^ 3 +
          locP₄ g x₀ * x ^ 4 + locP₅ g x₀ * x ^ 5 := by funext x; ring
    rw [e, gibbs_lin5 h1 (hp 2) (hp 3) (hp 4) (hp 5)]
    ring
  have hPint : Integrable (fun x => (x + g * x₀ * x ^ 2 + locP₃ g x₀ * x ^ 3 +
      locP₄ g x₀ * x ^ 4 + locP₅ g x₀ * x ^ 5) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (((h1.add ((hp 2).const_mul (g * x₀))).add ((hp 3).const_mul (locP₃ g x₀))).add
      ((hp 4).const_mul (locP₄ g x₀))).add ((hp 5).const_mul (locP₅ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hF : Integrable (fun x => (x * locWeight g x₀ x - (x + g * x₀ * x ^ 2 +
      locP₃ g x₀ * x ^ 3 + locP₄ g x₀ * x ^ 4 + locP₅ g x₀ * x ^ 5)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hf.sub hPint).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locE₆ g x₀ * x ^ 6 + locE₈ g x₀ * x ^ 8 + locE₁₀ g x₀ * x ^ 10 +
      locE₁₂ g x₀ * x ^ 12) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((((hp 6).const_mul (locE₆ g x₀)).add ((hp 8).const_mul (locE₈ g x₀))).add
      ((hp 10).const_mul (locE₁₀ g x₀))).add ((hp 12).const_mul (locE₁₂ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← hP, ← gibbs_sub' hf hPint, ← gibbs_lin4 (hp 6) (hp 8) (hp 10) (hp 12)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x =>
      locNumerator_pointwise5 hg x)

/-- `|⟨φ⟩ − (1 + a⟨x⟩ + p₃⟨x²⟩ + r₃⟨x³⟩ + r₄⟨x⁴⟩ + r₅⟨x⁵⟩ + r₆⟨x⁶⟩)| ≤ F₄⟨x⁴⟩ + F₈⟨x⁸⟩`. -/
theorem locDenominator_expansion3 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (locWeight g x₀) -
      (1 + g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2) +
        locR₃' g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) +
        locR₄' g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locR₅' g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) +
        locR₆' g * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6))| ≤
      16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ 4) +
        16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ 8) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_locWeight hlam hgamma hdisc hg ht (x₀ := x₀)
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht
  have h0 := hp 0
  simp only [pow_zero] at h0
  have h1 := hp 1
  simp only [pow_one] at h1
  have hA : Integrable (fun x => (1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 + locR₃' g x₀ * x ^ 3) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((h0.add (h1.const_mul (g * x₀))).add ((hp 2).const_mul (locP₃ g x₀))).add
      ((hp 3).const_mul (locR₃' g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hB : Integrable (fun x => (locR₄' g x₀ * x ^ 4 + locR₅' g x₀ * x ^ 5 + locR₆' g * x ^ 6) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (((hp 4).const_mul (locR₄' g x₀)).add ((hp 5).const_mul (locR₅' g x₀))).add
      ((hp 6).const_mul (locR₆' g))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hP : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => 1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 + locR₃' g x₀ * x ^ 3 + locR₄' g x₀ * x ^ 4 +
        locR₅' g x₀ * x ^ 5 + locR₆' g * x ^ 6) =
      1 + g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2) +
        locR₃' g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) +
        locR₄' g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locR₅' g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) +
        locR₆' g * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) := by
    have e : (fun x : ℝ => 1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 + locR₃' g x₀ * x ^ 3 +
        locR₄' g x₀ * x ^ 4 + locR₅' g x₀ * x ^ 5 + locR₆' g * x ^ 6) =
        fun x => (1 * 1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 + locR₃' g x₀ * x ^ 3) +
          (locR₄' g x₀ * x ^ 4 + locR₅' g x₀ * x ^ 5 + locR₆' g * x ^ 6) := by funext x; ring
    have hA' : Integrable (fun x => (1 * 1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 +
        locR₃' g x₀ * x ^ 3) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
      refine hA.congr (Eventually.of_forall fun x => ?_)
      ring
    rw [e, gibbs_add' hA' hB, gibbs_lin4 h0 h1 (hp 2) (hp 3), gibbs_lin3 (hp 4) (hp 5) (hp 6),
      gibbsExpectation_one' hZ]
    ring
  have hPint : Integrable (fun x => (1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 + locR₃' g x₀ * x ^ 3 +
      locR₄' g x₀ * x ^ 4 + locR₅' g x₀ * x ^ 5 + locR₆' g * x ^ 6) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hA.add hB).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hF : Integrable (fun x => (locWeight g x₀ x - (1 + g * x₀ * x + locP₃ g x₀ * x ^ 2 +
      locR₃' g x₀ * x ^ 3 + locR₄' g x₀ * x ^ 4 + locR₅' g x₀ * x ^ 5 + locR₆' g * x ^ 6)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hf.sub hPint).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 * x ^ 4 +
      16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * x ^ 8) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((hp 4).const_mul (16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4)).add
      ((hp 8).const_mul (16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← hP, ← gibbs_sub' hf hPint, ← gibbsExpectation_lin (hp 4) (hp 8)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x =>
      locDenominator_pointwise3 hg x)

end Expansions

/-! ### The coefficients and the rates -/

section Rates

variable {lam alpha gamma g x₀ : ℝ}

/-- `n₁ = B₁ + aB₂ + p₃c₃ + 3p₄/λ²`: the `1/t` coefficient of `t⟨xφ⟩`. -/
noncomputable def locN1 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  meanCoeff2 lam alpha gamma + g * x₀ * (5 * alpha ^ 2 / (4 * lam ^ 4) - gamma / (2 * lam ^ 3)) +
    locP₃ g x₀ * (-(5 * alpha / (2 * lam ^ 3))) + 3 * locP₄ g x₀ / lam ^ 2

/-- `d₁ = a·(−α/(2λ²)) + p₃/λ`: the `1/t` coefficient of `⟨φ⟩`. -/
noncomputable def locD1 (lam alpha g x₀ : ℝ) : ℝ :=
  g * x₀ * (-alpha / (2 * lam ^ 2)) + locP₃ g x₀ / lam

/-- The second-order coefficient of the localised mean: `t⟨x⟩_loc = c + c'/t + O(t⁻²)`. -/
noncomputable def meanLocCoeff2 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  locN1 lam alpha gamma g x₀ - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) * locD1 lam alpha g x₀

/-- The closed form: with `a = g x₀`,
`c' = B₁ + aα²/λ⁴ − aγ/(2λ³) + αg/λ³ − αa²/(2λ³) − ag/λ²`. -/
theorem meanLocCoeff2_eq (hlam : 0 < lam) :
    meanLocCoeff2 lam alpha gamma g x₀ =
      meanCoeff2 lam alpha gamma + g * x₀ * alpha ^ 2 / lam ^ 4 - g * x₀ * gamma / (2 * lam ^ 3) +
        alpha * g / lam ^ 3 - alpha * (g * x₀) ^ 2 / (2 * lam ^ 3) - g * x₀ * g / lam ^ 2 := by
  unfold meanLocCoeff2 locN1 locD1 locP₃ locP₄
  field_simp
  ring

/-- The algebra of the numerator's residual. -/
theorem locNumerator_key (lam alpha gamma g x₀ t N M₁ M₂ M₃ M₄ M₅ : ℝ) (hlam : lam ≠ 0)
    (ht : t ≠ 0) :
    t * N - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) - locN1 lam alpha gamma g x₀ / t =
      (t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t) +
        g * x₀ * (t * M₂ - 1 / lam -
          (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)) +
        locP₃ g x₀ * ((t ^ 2 * M₃ - -(5 * alpha / (2 * lam ^ 3))) / t) +
        locP₄ g x₀ * ((t ^ 2 * M₄ - 3 / lam ^ 2) / t) +
        locP₅ g x₀ * (t ^ 3 * M₅ / t ^ 2) +
        t * (N - (M₁ + g * x₀ * M₂ + locP₃ g x₀ * M₃ + locP₄ g x₀ * M₄ + locP₅ g x₀ * M₅)) := by
  unfold locN1
  field_simp
  ring

/-- The algebra of the denominator's residual. -/
theorem locDenominator_key (lam alpha g x₀ t D M₁ M₂ M₃ M₄ M₅ M₆ : ℝ) (hlam : lam ≠ 0)
    (ht : t ≠ 0) :
    D - 1 - locD1 lam alpha g x₀ / t =
      g * x₀ * ((t * M₁ - -alpha / (2 * lam ^ 2)) / t) + locP₃ g x₀ * ((t * M₂ - 1 / lam) / t) +
        locR₃' g x₀ * (t ^ 2 * M₃ / t ^ 2) + locR₄' g x₀ * M₄ +
        locR₅' g x₀ * (t ^ 3 * M₅ / t ^ 3) + locR₆' g * M₆ +
        (D - (1 + g * x₀ * M₁ + locP₃ g x₀ * M₂ + locR₃' g x₀ * M₃ + locR₄' g x₀ * M₄ +
          locR₅' g x₀ * M₅ + locR₆' g * M₆)) := by
  unfold locD1
  field_simp
  ring

/-- The algebra of the ratio. -/
theorem ratio_key (t N D c c' d₁ n₁ : ℝ) (hn : n₁ = c' + c * d₁) (ht : t ≠ 0) (hD : D ≠ 0) :
    t * (N / D) - c - c' / t =
      ((t * N - c - n₁ / t) - c * (D - 1 - d₁ / t) - c' * d₁ / t ^ 2 -
        c' / t * (D - 1 - d₁ / t)) / D := by
  rw [hn]
  field_simp
  ring

/-- The numerator's assembly, on abstract reals: the residual inequality from the five moment
inputs and the remainder envelope. -/
theorem numerator_assembly (lam alpha gamma g x₀ t N M₁ M₂ M₃ M₄ M₅ K₁ K₂ K₃ K₄ K₅' KR : ℝ)
    (hlam : 0 < lam) (ht1 : 1 ≤ t)
    (e₁ : |t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t| ≤ K₁ / t ^ 2)
    (e₂ : |t * M₂ - 1 / lam - (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)|
      ≤ K₂ / t ^ 2)
    (e₃ : |t ^ 2 * M₃ - -(5 * alpha / (2 * lam ^ 3))| ≤ K₃ / t)
    (e₄ : |t ^ 2 * M₄ - 3 / lam ^ 2| ≤ K₄ / t)
    (e₅ : |t ^ 3 * M₅| ≤ K₅')
    (hR : |N - (M₁ + g * x₀ * M₂ + locP₃ g x₀ * M₃ + locP₄ g x₀ * M₄ + locP₅ g x₀ * M₅)| ≤
      KR / t ^ 3) :
    |t * N - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) - locN1 lam alpha gamma g x₀ / t| ≤
      (K₁ + |g * x₀| * K₂ + |locP₃ g x₀| * K₃ + |locP₄ g x₀| * K₄ + |locP₅ g x₀| * K₅' + KR) /
        t ^ 2 := by
  have ht0 : 0 < t := by linarith
  rw [locNumerator_key lam alpha gamma g x₀ t N M₁ M₂ M₃ M₄ M₅ hlam.ne' ht0.ne']
  have b₁ : |t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t| ≤ K₁ / t ^ 2 := e₁
  have b₂ : |g * x₀ * (t * M₂ - 1 / lam -
      (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t))| ≤
      |g * x₀| * (K₂ / t ^ 2) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e₂ (abs_nonneg _)
  have b₃ : |locP₃ g x₀ * ((t ^ 2 * M₃ - -(5 * alpha / (2 * lam ^ 3))) / t)| ≤
      |locP₃ g x₀| * (K₃ / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ K₃ / t / t := div_le_div_of_nonneg_right e₃ ht0.le
      _ = K₃ / t ^ 2 := by ring
  have b₄ : |locP₄ g x₀ * ((t ^ 2 * M₄ - 3 / lam ^ 2) / t)| ≤ |locP₄ g x₀| * (K₄ / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ K₄ / t / t := div_le_div_of_nonneg_right e₄ ht0.le
      _ = K₄ / t ^ 2 := by ring
  have b₅ : |locP₅ g x₀ * (t ^ 3 * M₅ / t ^ 2)| ≤ |locP₅ g x₀| * (K₅' / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₅ (by positivity)) (abs_nonneg _)
  have bR : |t * (N - (M₁ + g * x₀ * M₂ + locP₃ g x₀ * M₃ + locP₄ g x₀ * M₄ + locP₅ g x₀ * M₅))| ≤
      KR / t ^ 2 := by
    rw [abs_mul, abs_of_pos ht0]
    calc t * |N - (M₁ + g * x₀ * M₂ + locP₃ g x₀ * M₃ + locP₄ g x₀ * M₄ + locP₅ g x₀ * M₅)|
        ≤ t * (KR / t ^ 3) := mul_le_mul_of_nonneg_left hR ht0.le
      _ = KR / t ^ 2 := by field_simp
  calc _ ≤ K₁ / t ^ 2 + |g * x₀| * (K₂ / t ^ 2) + |locP₃ g x₀| * (K₃ / t ^ 2) +
        |locP₄ g x₀| * (K₄ / t ^ 2) + |locP₅ g x₀| * (K₅' / t ^ 2) + KR / t ^ 2 := by
        refine (abs_add_le _ _).trans (add_le_add ?_ bR)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₅)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₄)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₃)
        exact (abs_add_le _ _).trans (add_le_add b₁ b₂)
    _ = _ := by ring

/-- The denominator's assembly, on abstract reals. -/
theorem denominator_assembly (lam alpha g x₀ t D M₁ M₂ M₃ M₄ M₅ M₆ K₁ K₂ K₃' C₄ K₅' C₆ KR : ℝ)
    (hlam : 0 < lam) (ht1 : 1 ≤ t) (hK₅ : 0 ≤ K₅') (hC₆ : 0 ≤ C₆) (hM₄0 : 0 ≤ M₄) (hM₆0 : 0 ≤ M₆)
    (e₁ : |t * M₁ - -alpha / (2 * lam ^ 2)| ≤ K₁ / t)
    (e₂ : |t * M₂ - 1 / lam| ≤ K₂ / t)
    (e₃ : |t ^ 2 * M₃| ≤ K₃')
    (e₄ : M₄ ≤ C₄ / t ^ 2)
    (e₅ : |t ^ 3 * M₅| ≤ K₅')
    (e₆ : M₆ ≤ C₆ / t ^ 3)
    (hR : |D - (1 + g * x₀ * M₁ + locP₃ g x₀ * M₂ + locR₃' g x₀ * M₃ + locR₄' g x₀ * M₄ +
      locR₅' g x₀ * M₅ + locR₆' g * M₆)| ≤ KR / t ^ 2) :
    |D - 1 - locD1 lam alpha g x₀ / t| ≤
      (|g * x₀| * K₁ + |locP₃ g x₀| * K₂ + |locR₃' g x₀| * K₃' + |locR₄' g x₀| * C₄ +
        |locR₅' g x₀| * K₅' + |locR₆' g| * C₆ + KR) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  rw [locDenominator_key lam alpha g x₀ t D M₁ M₂ M₃ M₄ M₅ M₆ hlam.ne' ht0.ne']
  have b₁ : |g * x₀ * ((t * M₁ - -alpha / (2 * lam ^ 2)) / t)| ≤ |g * x₀| * (K₁ / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ K₁ / t / t := div_le_div_of_nonneg_right e₁ ht0.le
      _ = K₁ / t ^ 2 := by ring
  have b₂ : |locP₃ g x₀ * ((t * M₂ - 1 / lam) / t)| ≤ |locP₃ g x₀| * (K₂ / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ K₂ / t / t := div_le_div_of_nonneg_right e₂ ht0.le
      _ = K₂ / t ^ 2 := by ring
  have b₃ : |locR₃' g x₀ * (t ^ 2 * M₃ / t ^ 2)| ≤ |locR₃' g x₀| * (K₃' / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₃ (by positivity)) (abs_nonneg _)
  have b₄ : |locR₄' g x₀ * M₄| ≤ |locR₄' g x₀| * (C₄ / t ^ 2) := by
    rw [abs_mul, abs_of_nonneg hM₄0]
    exact mul_le_mul_of_nonneg_left e₄ (abs_nonneg _)
  have b₅ : |locR₅' g x₀ * (t ^ 3 * M₅ / t ^ 3)| ≤ |locR₅' g x₀| * (K₅' / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 3)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ K₅' / t ^ 3 := div_le_div_of_nonneg_right e₅ (by positivity)
      _ ≤ K₅' / t ^ 2 :=
          div_le_div_of_nonneg_left hK₅ (by positivity) (pow_le_pow_right₀ ht1 (by norm_num))
  have b₆ : |locR₆' g * M₆| ≤ |locR₆' g| * (C₆ / t ^ 2) := by
    rw [abs_mul, abs_of_nonneg hM₆0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact e₆.trans (div_le_div_of_nonneg_left hC₆ (by positivity)
      (pow_le_pow_right₀ ht1 (by norm_num)))
  calc _ ≤ |g * x₀| * (K₁ / t ^ 2) + |locP₃ g x₀| * (K₂ / t ^ 2) + |locR₃' g x₀| * (K₃' / t ^ 2) +
        |locR₄' g x₀| * (C₄ / t ^ 2) + |locR₅' g x₀| * (K₅' / t ^ 2) + |locR₆' g| * (C₆ / t ^ 2) +
        KR / t ^ 2 := by
        refine (abs_add_le _ _).trans (add_le_add ?_ hR)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₆)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₅)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₄)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₃)
        exact (abs_add_le _ _).trans (add_le_add b₁ b₂)
    _ = _ := by ring

variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- **The numerator to second order**: `|t⟨xφ⟩ − c − n₁/t| ≤ K/t²`. -/
theorem locNumerator_rate2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x * locWeight g x₀ x) - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) -
        locN1 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := mean_anharmonic_order2_rate hlam hgamma hdisc
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ :=
    Laplace.OneD.secondMoment_anharmonic_order3_rate hlam hgamma hdisc
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := thirdMoment_lead hlam hgamma hdisc
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_lead hlam hgamma hdisc
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  obtain ⟨C₁₀, T₁₀, hC₁₀, hT₁₀, h₁₀⟩ := evenMoment_bound hlam hgamma hdisc 5
  obtain ⟨C₁₂, T₁₂, hC₁₂, hT₁₂, h₁₂⟩ := evenMoment_bound hlam hgamma hdisc 6
  simp only [show (2 * 3 : ℕ) = 6 from rfl, show (2 * 4 : ℕ) = 8 from rfl,
    show (2 * 5 : ℕ) = 10 from rfl, show (2 * 6 : ℕ) = 12 from rfl] at h₆ h₈ h₁₀ h₁₂
  have hE₆ := locE₆_nonneg g x₀
  have hE₈ := locE₈_nonneg g x₀
  have hE₁₀ := locE₁₀_nonneg g x₀
  have hE₁₂ := locE₁₂_nonneg g x₀
  have hKR0 : 0 ≤ locE₆ g x₀ * C₆ + locE₈ g x₀ * C₈ + locE₁₀ g x₀ * C₁₀ + locE₁₂ g x₀ * C₁₂ := by
    positivity
  have hK₅'0 : 0 ≤ |-(35 * alpha / (2 * lam ^ 4))| + K₅ := by positivity
  have h1T : (1 : ℝ) ≤ T₁ + T₂ + T₃ + T₄ + T₅ + T₆ + T₈ + T₁₀ + T₁₂ := by linarith
  refine ⟨K₁ + |g * x₀| * K₂ + |locP₃ g x₀| * K₃ + |locP₄ g x₀| * K₄ +
      |locP₅ g x₀| * (|-(35 * alpha / (2 * lam ^ 4))| + K₅) +
      (locE₆ g x₀ * C₆ + locE₈ g x₀ * C₈ + locE₁₀ g x₀ * C₁₀ + locE₁₂ g x₀ * C₁₂),
    T₁ + T₂ + T₃ + T₄ + T₅ + T₆ + T₈ + T₁₀ + T₁₂, by positivity, h1T,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have e₂ := h₂ (t := t) (by linarith)
  rw [secondMoment_coeff_eq hlam] at e₂
  have hR := (locNumerator_expansion5 hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h₆ (t := t) (by linarith)) hE₆)
      (mul_le_mul_of_nonneg_left (h₈ (t := t) (by linarith)) hE₈))
      (mul_le_mul_of_nonneg_left (h₁₀ (t := t) (by linarith)) hE₁₀))
      (mul_le_mul_of_nonneg_left (h₁₂ (t := t) (by linarith)) hE₁₂))
  have hRt : locE₆ g x₀ * (C₆ / t ^ 3) + locE₈ g x₀ * (C₈ / t ^ 4) +
      locE₁₀ g x₀ * (C₁₀ / t ^ 5) + locE₁₂ g x₀ * (C₁₂ / t ^ 6) ≤
      (locE₆ g x₀ * C₆ + locE₈ g x₀ * C₈ + locE₁₀ g x₀ * C₁₀ + locE₁₂ g x₀ * C₁₂) / t ^ 3 := by
    have h8 : locE₈ g x₀ * (C₈ / t ^ 4) ≤ locE₈ g x₀ * (C₈ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₈ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hE₈
    have h10 : locE₁₀ g x₀ * (C₁₀ / t ^ 5) ≤ locE₁₀ g x₀ * (C₁₀ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₀ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hE₁₀
    have h12 : locE₁₂ g x₀ * (C₁₂ / t ^ 6) ≤ locE₁₂ g x₀ * (C₁₂ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₂ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hE₁₂
    have e : (locE₆ g x₀ * C₆ + locE₈ g x₀ * C₈ + locE₁₀ g x₀ * C₁₀ + locE₁₂ g x₀ * C₁₂) / t ^ 3 =
        locE₆ g x₀ * (C₆ / t ^ 3) + locE₈ g x₀ * (C₈ / t ^ 3) + locE₁₀ g x₀ * (C₁₀ / t ^ 3) +
          locE₁₂ g x₀ * (C₁₂ / t ^ 3) := by ring
    rw [e]
    linarith
  exact numerator_assembly lam alpha gamma g x₀ t
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x * locWeight g x₀ x))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5))
    K₁ K₂ K₃ K₄ (|-(35 * alpha / (2 * lam ^ 4))| + K₅)
    (locE₆ g x₀ * C₆ + locE₈ g x₀ * C₈ + locE₁₀ g x₀ * C₁₀ + locE₁₂ g x₀ * C₁₂) hlam ht1
    (h₁ (t := t) (by linarith)) e₂ (h₃ (t := t) (by linarith))
    (h₄ (t := t) (by linarith)) (Laplace.OneD.rate_bounded ht1 hK₅ (h₅ (t := t) (by linarith)))
    (hR.trans hRt)

/-- **The denominator to second order**: `|⟨φ⟩ − 1 − d₁/t| ≤ K/t²`. -/
theorem locDenominator_rate2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (locWeight g x₀) -
        1 - locD1 lam alpha g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := Laplace.OneD.mean_anharmonic_O2_rate hlam hgamma hdisc
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := secondMoment_lead hlam hgamma hdisc
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := thirdMoment_lead hlam hgamma hdisc
  obtain ⟨C₄, T₄, hC₄, hT₄, h₄⟩ := evenMoment_bound hlam hgamma hdisc 2
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  simp only [show (2 * 2 : ℕ) = 4 from rfl, show (2 * 3 : ℕ) = 6 from rfl,
    show (2 * 4 : ℕ) = 8 from rfl] at h₄ h₆ h₈
  have hF₄0 : 0 ≤ 16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 := by positivity
  have hF₈0 : 0 ≤ 16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 := by positivity
  have hK₃'0 : 0 ≤ |-(5 * alpha / (2 * lam ^ 3))| + K₃ := by positivity
  have hK₅'0 : 0 ≤ |-(35 * alpha / (2 * lam ^ 4))| + K₅ := by positivity
  have hKR0 : 0 ≤ 16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 * C₄ +
      16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * C₈ := by positivity
  have h1T : (1 : ℝ) ≤ T₁ + T₂ + T₃ + T₄ + T₅ + T₆ + T₈ := by linarith
  refine ⟨|g * x₀| * K₁ + |locP₃ g x₀| * K₂ +
      |locR₃' g x₀| * (|-(5 * alpha / (2 * lam ^ 3))| + K₃) +
      |locR₄' g x₀| * C₄ + |locR₅' g x₀| * (|-(35 * alpha / (2 * lam ^ 4))| + K₅) +
      |locR₆' g| * C₆ + (16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 * C₄ +
        16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * C₈),
    T₁ + T₂ + T₃ + T₄ + T₅ + T₆ + T₈, by positivity, h1T, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hZ := partition_pos' hlam hgamma hdisc ht0
  have hM₄0 : 0 ≤ _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 4) := gibbsExpectation_nonneg' hZ fun x => by positivity
  have hM₆0 : 0 ≤ _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 6) := gibbsExpectation_nonneg' hZ fun x => by positivity
  have hR := (locDenominator_expansion3 hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (mul_le_mul_of_nonneg_left (h₄ (t := t) (by linarith)) hF₄0)
      (mul_le_mul_of_nonneg_left (h₈ (t := t) (by linarith)) hF₈0))
  have hRt : 16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 * (C₄ / t ^ 2) +
      16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * (C₈ / t ^ 4) ≤
      (16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 * C₄ +
        16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * C₈) / t ^ 2 := by
    have h8 : 16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * (C₈ / t ^ 4) ≤
        16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * (C₈ / t ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₈ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hF₈0
    have e : (16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 * C₄ +
        16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * C₈) / t ^ 2 =
        16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 * (C₄ / t ^ 2) +
          16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * (C₈ / t ^ 2) := by ring
    rw [e]
    linarith
  exact denominator_assembly lam alpha g x₀ t
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (locWeight g x₀))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 6))
    K₁ K₂ (|-(5 * alpha / (2 * lam ^ 3))| + K₃) C₄ (|-(35 * alpha / (2 * lam ^ 4))| + K₅) C₆
    (16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4 * C₄ +
      16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4 * C₈) hlam ht1
    hK₅'0 hC₆ hM₄0 hM₆0 (h₁ (t := t) (by linarith)) (h₂ (t := t) (by linarith))
    (Laplace.OneD.rate_bounded ht1 hK₃ (h₃ (t := t) (by linarith))) (h₄ (t := t) (by linarith))
    (Laplace.OneD.rate_bounded ht1 hK₅ (h₅ (t := t) (by linarith))) (h₆ (t := t) (by linarith))
    (hR.trans hRt)

/-- **The localised mean to second order**: `|t⟨x⟩_loc − c − c'/t| ≤ K/t²`,
`c = −α/(2λ²) + g x₀/λ`, `c' = meanLocCoeff2` (eq:mean's `O(S²)` coefficient on the exact localised
anharmonic measure). -/
theorem localisedMean_order2_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * localisedMean lam alpha gamma g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) -
        meanLocCoeff2 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨KN, TN, hKN, hTN, hN⟩ := locNumerator_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  set c := -alpha / (2 * lam ^ 2) + g * x₀ / lam with hc
  set c' := meanLocCoeff2 lam alpha gamma g x₀ with hc'
  set d₁ := locD1 lam alpha g x₀ with hd₁
  set n₁ := locN1 lam alpha gamma g x₀ with hn₁
  have hn₁e : n₁ = c' + c * d₁ := by
    rw [hc', meanLocCoeff2]
    ring
  have hd₁0 : 0 ≤ |d₁| := abs_nonneg d₁
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hc'0 : 0 ≤ |c'| := abs_nonneg c'
  have hTD0 : 0 ≤ TD := by linarith
  have hTN0 : 0 ≤ TN := by linarith
  have h1T : (1 : ℝ) ≤ TN + TD + 2 * (|d₁| + KD) := by linarith
  refine ⟨2 * (KN + |c| * KD + |c'| * |d₁| + |c'| * KD), TN + TD + 2 * (|d₁| + KD),
    by positivity, h1T, fun {t} ht => ?_⟩
  have hTNt : TN ≤ t := by linarith
  have hTDt : TD ≤ t := by linarith
  have h2 : 2 * (|d₁| + KD) ≤ t := by linarith
  have ht1 : 1 ≤ t := hTN.trans hTNt
  have ht0 : 0 < t := by linarith
  rw [localisedMean_eq_ratio hlam hgamma hdisc ht0]
  have eN := hN hTNt
  have eD := hD hTDt
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x * locWeight g x₀ x) with hNdef
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
  have hDhalf : 1 / 2 ≤ D := by
    have h1 : |D - 1| ≤ (|d₁| + KD) / t := by
      calc |D - 1| = |(D - 1 - d₁ / t) + d₁ / t| := by ring_nf
        _ ≤ |D - 1 - d₁ / t| + |d₁ / t| := abs_add_le _ _
        _ ≤ KD / t ^ 2 + |d₁| / t := by
            gcongr
            rw [abs_div, abs_of_pos ht0]
        _ ≤ KD / t + |d₁| / t := by
            gcongr
            nlinarith
        _ = (|d₁| + KD) / t := by ring
    have h3 : (|d₁| + KD) / t ≤ 1 / 2 := by
      rw [div_le_iff₀ ht0]
      linarith [h2]
    have h4 := (abs_le.mp (h1.trans h3)).1
    linarith
  have hD0 : 0 < D := by linarith
  rw [ratio_key t N D c c' d₁ n₁ hn₁e ht0.ne' hD0.ne', abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  have h3 : |c' * d₁ / t ^ 2| = |c'| * |d₁| / t ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  have h4 : |c' / t * (D - 1 - d₁ / t)| ≤ |c'| * KD / t ^ 2 := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    calc |c'| / t * |D - 1 - d₁ / t| ≤ |c'| / t * (KD / t ^ 2) := by gcongr
      _ = (|c'| * KD / t ^ 2) / t := by ring
      _ ≤ |c'| * KD / t ^ 2 := div_le_self (by positivity) ht1
  calc |(t * N - c - n₁ / t) - c * (D - 1 - d₁ / t) - c' * d₁ / t ^ 2 -
        c' / t * (D - 1 - d₁ / t)|
      ≤ |t * N - c - n₁ / t| + |c * (D - 1 - d₁ / t)| + |c' * d₁ / t ^ 2| +
        |c' / t * (D - 1 - d₁ / t)| := by
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          exact abs_sub _ _
    _ ≤ KN / t ^ 2 + |c| * (KD / t ^ 2) + |c'| * |d₁| / t ^ 2 + |c'| * KD / t ^ 2 := by
          rw [abs_mul c, h3]
          gcongr
    _ = (KN + |c| * KD + |c'| * |d₁| + |c'| * KD) / t ^ 2 := by ring
    _ = 2 * (KN + |c| * KD + |c'| * |d₁| + |c'| * KD) / t ^ 2 * (1 / 2) := by ring
    _ ≤ 2 * (KN + |c| * KD + |c'| * |d₁| + |c'| * KD) / t ^ 2 * D := by gcongr

end Rates

end Laplace.Multi
