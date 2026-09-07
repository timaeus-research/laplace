/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.QuadraticMixedBridge

/-!
# Taylor tail control for the phase factor

Unit 199, first unit of the general-`d` phase programme (Astra #20 programme A). The plan is to
expand the phase factor `e^{βsξ(u)}` (`s = N u^k`) of the dressed normal integral
`∫ η(u) u^h e^{-βN²u^{2k} + βN u^k ξ(u)} du` in a Taylor series, so that each term is an existing
continuous-amplitude theorem at shifted exponents, and to control the tail uniformly. This file
provides the elementary tail estimates:

* `abs_exp_sub_sum_le`: `|e^x - Σ_{j<J} x^j/j!| ≤ |x|^J e^{|x|} / J!` for all real `x`;
* `pow_mul_exp_neg_sq_le`: `s^{2K} e^{-cs²} ≤ K!/c^K`;
* `exp_linear_sub_sq_le`: `e^{bs - βs²} ≤ e^{b²/(2β)} e^{-βs²/2}`;
* `tailCoeff`, `tendsto_tailCoeff`: the tail constant `(b²)^K/(2K)! · K!/(β/4)^K · e^{b²/(2β)}`
  tends to zero as `K → ∞`;
* `phase_tail_le`: for `s ≥ 0` and `|x| ≤ b`,
  `|e^{sx} - Σ_{j<2K} (sx)^j/j!| e^{-βs²} ≤ tailCoeff β b K · e^{-(β/4)s²}`.

Zero `sorry`/`axiom`.
-/

open Real Filter Topology

namespace Laplace.Grammar

/-- Taylor remainder of the exponential, valid for every real `x`. -/
theorem abs_exp_sub_sum_le (x : ℝ) (J : ℕ) :
    |Real.exp x - ∑ j ∈ Finset.range J, x ^ j / (j.factorial : ℝ)| ≤
      |x| ^ J / (J.factorial : ℝ) * Real.exp |x| := by
  have hS : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hS' : HasSum (fun n : ℕ => |x| ^ n / (n.factorial : ℝ)) (Real.exp |x|) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp |x|
  have htail := Summable.sum_add_tsum_nat_add J hS.summable
  rw [hS.tsum_eq] at htail
  have hrem : Real.exp x - ∑ j ∈ Finset.range J, x ^ j / (j.factorial : ℝ) =
      ∑' i : ℕ, x ^ (i + J) / ((i + J).factorial : ℝ) := by linarith
  rw [hrem]
  have habs : Summable (fun i : ℕ => |x| ^ (i + J) / ((i + J).factorial : ℝ)) :=
    (summable_nat_add_iff J).2 hS'.summable
  have habs' : Summable (fun i : ℕ => |x ^ (i + J) / ((i + J).factorial : ℝ)|) := by
    refine habs.congr fun i => ?_
    rw [abs_div, abs_pow, Nat.abs_cast]
  have hbound : ∀ i : ℕ, |x ^ (i + J) / ((i + J).factorial : ℝ)| ≤
      |x| ^ J / (J.factorial : ℝ) * (|x| ^ i / (i.factorial : ℝ)) := by
    intro i
    rw [abs_div, abs_pow, Nat.abs_cast, div_mul_div_comm, ← pow_add, add_comm J i]
    have hfac : ((J.factorial : ℝ) * i.factorial) ≤ ((i + J).factorial : ℝ) := by
      have := Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add J i)
      rw [add_comm J i] at this
      exact_mod_cast this
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
  calc |∑' i : ℕ, x ^ (i + J) / ((i + J).factorial : ℝ)|
      ≤ ∑' i : ℕ, |x ^ (i + J) / ((i + J).factorial : ℝ)| := by
        have h := norm_tsum_le_tsum_norm (f := fun i : ℕ => x ^ (i + J) / ((i + J).factorial : ℝ))
          (by simpa only [Real.norm_eq_abs] using habs')
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∑' i : ℕ, |x| ^ J / (J.factorial : ℝ) * (|x| ^ i / (i.factorial : ℝ)) :=
        Summable.tsum_le_tsum hbound habs' (hS'.summable.mul_left _)
    _ = |x| ^ J / (J.factorial : ℝ) * Real.exp |x| := by rw [tsum_mul_left, hS'.tsum_eq]

/-- `s^{2K} e^{-cs²} ≤ K!/c^K` for `s ≥ 0`, `c > 0`. -/
theorem pow_mul_exp_neg_sq_le (c s : ℝ) (hc : 0 < c) (K : ℕ) :
    s ^ (2 * K) * Real.exp (-(c * s ^ 2)) ≤ (K.factorial : ℝ) / c ^ K := by
  have h := Real.pow_div_factorial_le_exp (x := c * s ^ 2) (by positivity) K
  have hpow : (c * s ^ 2) ^ K = c ^ K * s ^ (2 * K) := by rw [mul_pow, ← pow_mul]
  rw [hpow, div_le_iff₀ (by positivity)] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  linarith

/-- Completing the square: `e^{bs - βs²} ≤ e^{b²/(2β)} e^{-(β/2)s²}`. -/
theorem exp_linear_sub_sq_le (β b s : ℝ) (hβ : 0 < β) :
    Real.exp (b * s - β * s ^ 2) ≤ Real.exp (b ^ 2 / (2 * β)) * Real.exp (-(β / 2 * s ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hsq : b ^ 2 / (2 * β) + -(β / 2 * s ^ 2) - (b * s - β * s ^ 2) =
      (β * s - b) ^ 2 / (2 * β) := by
    field_simp
    ring
  have hnn : 0 ≤ (β * s - b) ^ 2 / (2 * β) := by positivity
  linarith

/-- The tail constant `(b²)^K/(2K)! · K!/(β/4)^K · e^{b²/(2β)}`. -/
noncomputable def tailCoeff (β b : ℝ) (K : ℕ) : ℝ :=
  (b ^ 2) ^ K / ((2 * K).factorial : ℝ) * ((K.factorial : ℝ) / (β / 4) ^ K) *
    Real.exp (b ^ 2 / (2 * β))

theorem tailCoeff_nonneg (β b : ℝ) (hβ : 0 < β) (K : ℕ) : 0 ≤ tailCoeff β b K := by
  unfold tailCoeff
  positivity

/-- `(2K)! ≥ (K!)²`. -/
theorem factorial_sq_le_factorial_two_mul (K : ℕ) :
    ((K.factorial : ℝ) * K.factorial) ≤ ((2 * K).factorial : ℝ) := by
  have := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add K K)
  rw [← two_mul] at this
  exact_mod_cast this

/-- The tail constant tends to zero: `tailCoeff β b K ≤ (4b²/β)^K/K! · e^{b²/(2β)}`. -/
theorem tendsto_tailCoeff (β b : ℝ) (hβ : 0 < β) :
    Tendsto (fun K : ℕ => tailCoeff β b K) atTop (𝓝 0) := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (b ^ 2 / (β / 4))).mul_const
    (Real.exp (b ^ 2 / (2 * β)))
  rw [zero_mul] at h
  refine squeeze_zero (fun K => tailCoeff_nonneg β b hβ K) (fun K => ?_) h
  unfold tailCoeff
  have hc : (0 : ℝ) < β / 4 := by positivity
  have hfac := factorial_sq_le_factorial_two_mul K
  have hnn : 0 ≤ (b ^ 2) ^ K * (β / 4) ^ K := by positivity
  have hkey : (b ^ 2) ^ K / ((2 * K).factorial : ℝ) * ((K.factorial : ℝ) / (β / 4) ^ K) ≤
      (b ^ 2 / (β / 4)) ^ K / (K.factorial : ℝ) := by
    rw [div_mul_div_comm]
    conv_rhs => rw [div_pow, div_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hfac hnn]
  exact mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le

/-- **Uniform tail bound for the phase factor**: for `s ≥ 0` and `|x| ≤ b`,
`|e^{sx} - Σ_{j<2K} (sx)^j/j!| e^{-βs²} ≤ tailCoeff β b K · e^{-(β/4)s²}`. -/
theorem phase_tail_le (β b s x : ℝ) (hβ : 0 < β) (hs : 0 ≤ s) (hx : |x| ≤ b) (K : ℕ) :
    |Real.exp (s * x) - ∑ j ∈ Finset.range (2 * K), (s * x) ^ j / (j.factorial : ℝ)| *
        Real.exp (-(β * s ^ 2)) ≤
      tailCoeff β b K * Real.exp (-(β / 4 * s ^ 2)) := by
  have hb : 0 ≤ b := (abs_nonneg x).trans hx
  have hsx : |s * x| ≤ b * s := by
    rw [abs_mul, abs_of_nonneg hs, mul_comm]
    exact mul_le_mul_of_nonneg_right hx hs
  have h1 := abs_exp_sub_sum_le (s * x) (2 * K)
  -- step 1: Taylor remainder, then monotonicity in `|sx| ≤ bs`
  have h2 : |s * x| ^ (2 * K) / ((2 * K).factorial : ℝ) * Real.exp |s * x| *
      Real.exp (-(β * s ^ 2)) ≤
      (b * s) ^ (2 * K) / ((2 * K).factorial : ℝ) * Real.exp (b * s - β * s ^ 2) := by
    rw [sub_eq_add_neg, Real.exp_add, ← mul_assoc]
    gcongr
  -- step 2: complete the square and split the Gaussian
  have h3 : (b * s) ^ (2 * K) / ((2 * K).factorial : ℝ) * Real.exp (b * s - β * s ^ 2) ≤
      (b ^ 2) ^ K / ((2 * K).factorial : ℝ) * Real.exp (b ^ 2 / (2 * β)) *
        (s ^ (2 * K) * Real.exp (-(β / 4 * s ^ 2))) * Real.exp (-(β / 4 * s ^ 2)) := by
    have hE := exp_linear_sub_sq_le β b s hβ
    have hsplit : Real.exp (-(β / 2 * s ^ 2)) =
        Real.exp (-(β / 4 * s ^ 2)) * Real.exp (-(β / 4 * s ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hbs : (b * s) ^ (2 * K) = (b ^ 2) ^ K * s ^ (2 * K) := by
      rw [mul_pow, ← pow_mul, mul_comm 2 K, pow_mul]
    rw [hsplit] at hE
    calc (b * s) ^ (2 * K) / ((2 * K).factorial : ℝ) * Real.exp (b * s - β * s ^ 2)
        ≤ (b * s) ^ (2 * K) / ((2 * K).factorial : ℝ) *
          (Real.exp (b ^ 2 / (2 * β)) * (Real.exp (-(β / 4 * s ^ 2)) *
            Real.exp (-(β / 4 * s ^ 2)))) := by
          gcongr
      _ = (b ^ 2) ^ K / ((2 * K).factorial : ℝ) * Real.exp (b ^ 2 / (2 * β)) *
          (s ^ (2 * K) * Real.exp (-(β / 4 * s ^ 2))) * Real.exp (-(β / 4 * s ^ 2)) := by
          rw [hbs]
          ring
  -- step 3: the polynomial-times-Gaussian bound
  have h4 := pow_mul_exp_neg_sq_le (β / 4) s (by positivity) K
  calc |Real.exp (s * x) - ∑ j ∈ Finset.range (2 * K), (s * x) ^ j / (j.factorial : ℝ)| *
        Real.exp (-(β * s ^ 2))
      ≤ |s * x| ^ (2 * K) / ((2 * K).factorial : ℝ) * Real.exp |s * x| *
          Real.exp (-(β * s ^ 2)) := by gcongr
    _ ≤ (b * s) ^ (2 * K) / ((2 * K).factorial : ℝ) * Real.exp (b * s - β * s ^ 2) := h2
    _ ≤ (b ^ 2) ^ K / ((2 * K).factorial : ℝ) * Real.exp (b ^ 2 / (2 * β)) *
          (s ^ (2 * K) * Real.exp (-(β / 4 * s ^ 2))) * Real.exp (-(β / 4 * s ^ 2)) := h3
    _ ≤ (b ^ 2) ^ K / ((2 * K).factorial : ℝ) * Real.exp (b ^ 2 / (2 * β)) *
          ((K.factorial : ℝ) / (β / 4) ^ K) * Real.exp (-(β / 4 * s ^ 2)) := by
          gcongr
    _ = tailCoeff β b K * Real.exp (-(β / 4 * s ^ 2)) := by
          unfold tailCoeff
          ring

end Laplace.Grammar
