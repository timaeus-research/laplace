import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Moments of the standard 1D Gaussian

This file establishes the closed form of even moments of the standard centred
Gaussian measure on `ℝ`:

  `∫ x^(2k) · exp(-x²/2) / √(2π) dx = (2k-1)‼`

following the **Susceptibility Primer** (Baker et al. 2025), §4.

## Strategy

Reduce the moment integral to the Gamma function via the substitution
`x = √(2u)`, so that `x²/2 = u`, `dx = du / √(2u)`, and `x^(2k) = (2u)^k`.
Then

  `∫_{Ioi 0} x^(2k) · exp(-x²/2) dx = 2^(k - 1/2) · Γ(k + 1/2)`.

Symmetry of the integrand doubles this to `2^(k + 1/2) · Γ(k + 1/2)`. Combined
with Mathlib's `Real.Gamma_nat_add_half`, which gives
`Γ(k + 1/2) = (2k - 1)‼ · √π / 2^k`, the prefactor collapses to `√(2π)`.

## References

* Mathlib: `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
  (in particular `Real.Gamma_nat_add_half`).
* Mathlib: `Mathlib.Data.Nat.Factorial.DoubleFactorial`
  (notation `n‼`, recurrence `(n+2)‼ = (n+2) · n‼`).
-/

open Real MeasureTheory Set
open scoped Nat

namespace Laplace.OneD

/-- The half-line moment integral against `exp(-x²/2)` evaluates to a
half-integer Gamma value:

  `∫ x in Ioi 0, x^(2k) · exp(-x²/2) dx = 2^(k - 1/2) · Γ(k + 1/2)`.

The proof reduces to Mathlib's `integral_rpow_mul_exp_neg_mul_rpow` with
`p = 2`, `q = 2k`, `b = 1/2`. -/
theorem integral_pow_mul_exp_neg_sq_half_Ioi (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * k) * exp (-x ^ 2 / 2) =
      2 ^ (k - 1/2 : ℝ) * Real.Gamma (k + 1/2) := by
  -- Apply Mathlib's master lemma: `∫ x^q * exp(-b*x^p) = b^(-(q+1)/p) * (1/p) * Γ((q+1)/p)`.
  have hk : (-1 : ℝ) < 2 * (k : ℝ) :=
    by have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
  have key := integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := 2 * (k : ℝ)) (b := 1/2)
    (by norm_num) hk (by norm_num)
  -- `key` is in `rpow` form. Rewrite our integrand to match.
  have hLHS : (∫ x in Ioi (0 : ℝ), x ^ (2 * k) * exp (-x ^ 2 / 2)) =
      ∫ x in Ioi (0 : ℝ), x ^ (2 * (k : ℝ)) * exp (-(1/2) * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [mem_Ioi] at hx
    have h2k : x ^ (2 * (k : ℝ)) = x ^ (2 * k) := by
      rw [show (2 * (k : ℝ) : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
          rpow_natCast]
    have h2 : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
      rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
    rw [h2k, h2]
    -- LHS and RHS now have the same `x ^ (2*k)` factor; differ only inside `exp`.
    congr 2
    ring
  rw [hLHS, key]
  -- Simplify RHS: `(1/2)^(-(2k+1)/2) * (1/2) * Γ((2k+1)/2) = 2^(k-1/2) * Γ(k+1/2)`.
  have hg : (2 * (k : ℝ) + 1) / 2 = (k : ℝ) + 1/2 := by ring
  have hexp : -(2 * (k : ℝ) + 1) / 2 = -((k : ℝ) + 1/2) := by ring
  rw [hg, hexp]
  -- Now: `(1/2) ^ (-(k+1/2)) * (1/2) * Γ(k+1/2) = 2^(k-1/2) * Γ(k+1/2)`.
  congr 1
  -- Goal: `(1/2)^(-(↑k + 1/2)) * (1/2) = 2^(↑k - 1/2)`.
  -- Convert `(1/2)^(-(k+1/2))` to `2^(k+1/2)`:
  have step1 : ((1 : ℝ) / 2) ^ (-((k : ℝ) + 1/2)) = (2 : ℝ) ^ ((k : ℝ) + 1/2) := by
    rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num,
        inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
        ← rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [step1]
  -- Goal: `2^(↑k + 1/2) * (1/2) = 2^(↑k - 1/2)`.
  -- Use `(1/2) = 2^(-1)` and combine exponents.
  rw [show ((1 : ℝ) / 2) = (2 : ℝ) ^ (-1 : ℝ) by
        rw [rpow_neg_one]; norm_num,
      ← rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Even moments of the standard Gaussian (un-normalised): for any `k`,

  `∫ x^(2k) · exp(-x²/2) dx = (2k-1)‼ · √(2π)`,

where the integral is over the whole real line.

The integrand is even (since `2k` is even), so `integral_comp_abs` reduces this
to twice the half-line integral, which is computed by
`integral_pow_mul_exp_neg_sq_half_Ioi`. The `Γ(k + 1/2)` factor collapses via
`Real.Gamma_nat_add_half`. -/
theorem integral_pow_mul_exp_neg_sq_half (k : ℕ) :
    ∫ x : ℝ, x ^ (2 * k) * exp (-x ^ 2 / 2) =
      ((2 * k - 1)‼ : ℝ) * sqrt (2 * π) := by
  -- Step 1: rewrite as integral of `f(|x|)` where f is the half-line integrand.
  have heven : (∫ x : ℝ, x ^ (2 * k) * exp (-x ^ 2 / 2)) =
      ∫ x : ℝ, |x| ^ (2 * k) * exp (-|x| ^ 2 / 2) := by
    congr 1
    ext x
    rw [show x ^ (2 * k) = |x| ^ (2 * k) from by
          rw [pow_mul x 2 k, ← sq_abs x, ← pow_mul],
        show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
  rw [heven]
  -- Step 2: apply `integral_comp_abs` to get 2 × half-line integral.
  rw [integral_comp_abs (f := fun t => t ^ (2 * k) * exp (-t ^ 2 / 2))]
  -- Goal: 2 * ∫ x in Ioi 0, x^(2k) * exp(-x²/2) = (2k-1)‼ * √(2π).
  rw [integral_pow_mul_exp_neg_sq_half_Ioi, Real.Gamma_nat_add_half]
  -- Goal:
  --   2 * (2^(↑k - 1/2) * ((2*k - 1 : ℕ)‼ * √π / 2^k)) = (2*k - 1)‼ * √(2π)
  -- Step 3: extract the scalar identity `2 * 2^(↑k - 1/2) / 2^k = √2`,
  -- factor `(2k-1)‼ * √π` from both sides, and close.
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hscalar : (2 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - 1/2) / (2 : ℝ) ^ k = Real.sqrt 2 := by
    rw [show ((2 : ℝ) ^ k : ℝ) = (2 : ℝ) ^ ((k : ℝ)) from (rpow_natCast 2 k).symm,
        Real.sqrt_eq_rpow]
    nth_rewrite 1 [show (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) from (rpow_one 2).symm]
    rw [← rpow_add h2pos, div_eq_mul_inv, ← rpow_neg h2pos.le,
        ← rpow_add h2pos]
    congr 1
    ring
  -- Use `hscalar`: rewrite `√(2π) = √2 * √π`, regroup factors, apply.
  rw [Real.sqrt_mul h2pos.le π]
  -- Goal: 2 * (2^(↑k - 1/2) * ((2*k - 1)‼ * √π / 2^k)) = (2*k - 1)‼ * (√2 * √π)
  -- Reshape LHS and RHS to expose `(2*k-1)‼ * √π * (scalar)` form:
  have : ∀ (a b : ℝ),
      (2 : ℝ) * ((2 : ℝ) ^ ((k : ℝ) - 1/2) * (a * b / (2 : ℝ) ^ k))
        = a * b * ((2 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - 1/2) / (2 : ℝ) ^ k) := by
    intro a b; ring
  rw [this]
  rw [hscalar]
  ring

/-- Normalised even moments of the standard 1D Gaussian:

  `(1/√(2π)) · ∫ x^(2k) · exp(-x²/2) dx = (2k-1)‼`. -/
theorem gaussian_moment_normalized (k : ℕ) :
    (1 / sqrt (2 * π)) * ∫ x : ℝ, x ^ (2 * k) * exp (-x ^ 2 / 2) =
      ((2 * k - 1)‼ : ℝ) := by
  rw [integral_pow_mul_exp_neg_sq_half]
  have h : sqrt (2 * π) ≠ 0 := by positivity
  field_simp

/-- Odd moments of the standard Gaussian vanish by symmetry. -/
theorem integral_pow_mul_exp_neg_sq_odd (k : ℕ) :
    ∫ x : ℝ, x ^ (2 * k + 1) * exp (-x ^ 2 / 2) = 0 := by
  set f : ℝ → ℝ := fun x => x ^ (2 * k + 1) * exp (-x ^ 2 / 2) with hf
  -- `f` is odd: `f(-x) = -f(x)`.
  have hodd : ∀ x : ℝ, f (-x) = -(f x) := by
    intro x
    simp only [hf]
    rw [Odd.neg_pow ⟨k, rfl⟩, neg_sq]
    ring
  -- Hence `∫ f = ∫ f(-·) = ∫ (-f) = -∫ f`, so `∫ f = 0`.
  have heq : (∫ x, f x) = -(∫ x, f x) := by
    conv_lhs => rw [← integral_neg_eq_self f volume]
    rw [show (fun x => f (-x)) = (fun x => -(f x)) from funext hodd]
    rw [integral_neg]
  linarith

/-- Even moments of a rescaled Gaussian: for `t > 0`,

  `∫ x^(2k) · exp(-tx²/2) dx = (2k-1)‼ · √(2π) · t^(-k - 1/2)`.

The proof rescales `x = u/√t` to reduce to the standard Gaussian moment. -/
theorem integral_pow_mul_exp_neg_t_sq_half (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, x ^ (2 * k) * exp (-(t * x ^ 2) / 2) =
      ((2 * k - 1)‼ : ℝ) * sqrt (2 * π) * t ^ (-((k : ℝ) + 1/2)) := by
  -- Substitute `x = u / √t`. The map `x ↦ x * √t` has Jacobian `√t`.
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst_ne : Real.sqrt t ≠ 0 := ne_of_gt hst
  -- Use `integral_comp_mul_right` (linear substitution) on `Real`:
  --   `∫ f(x · c) dx = c⁻¹ • ∫ f y dy` for `c ≠ 0`.
  have hkey : (∫ x : ℝ, (x * sqrt t) ^ (2 * k) * exp (-((x * sqrt t) ^ 2) / 2)) =
      (sqrt t)⁻¹ * ∫ y : ℝ, y ^ (2 * k) * exp (-y ^ 2 / 2) := by
    have := MeasureTheory.Measure.integral_comp_mul_right
      (fun y : ℝ => y ^ (2 * k) * exp (-y ^ 2 / 2)) (sqrt t)
    rw [abs_of_pos (inv_pos.mpr hst), smul_eq_mul] at this
    exact this
  -- Massage the LHS of `hkey` to match our target.
  -- `(x * √t)^(2k) = x^(2k) * (√t)^(2k) = x^(2k) * t^k`
  -- `(x * √t)^2 = x^2 * t`
  have hLHS : (∫ x : ℝ, (x * sqrt t) ^ (2 * k) * exp (-((x * sqrt t) ^ 2) / 2)) =
      t ^ k * ∫ x : ℝ, x ^ (2 * k) * exp (-(t * x ^ 2) / 2) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext x
    rw [show (x * sqrt t) ^ (2 * k) = x ^ (2 * k) * t ^ k by
          rw [mul_pow, show (sqrt t) ^ (2 * k) = t ^ k by
                rw [pow_mul, Real.sq_sqrt ht.le]]]
    rw [show (x * sqrt t) ^ 2 = t * x ^ 2 by
          rw [mul_pow, Real.sq_sqrt ht.le]; ring]
    ring
  -- Combine `hLHS = hkey-LHS` and `hkey-RHS = (1/√t) · standard moment`.
  have hstd := integral_pow_mul_exp_neg_sq_half k
  rw [hLHS] at hkey
  rw [hstd] at hkey
  -- `hkey : t^k * (∫ ...) = (√t)⁻¹ * ((2k-1)‼ * √(2π))`.
  -- Solve for our target: `∫ ... = (1/(t^k √t)) * ((2k-1)‼ * √(2π))`
  --                              = ((2k-1)‼ * √(2π)) * t^(-(k + 1/2))`.
  have htk : (t : ℝ) ^ k ≠ 0 := pow_ne_zero k ht.ne'
  have : ∫ x : ℝ, x ^ (2 * k) * exp (-(t * x ^ 2) / 2) =
      (t ^ k)⁻¹ * ((sqrt t)⁻¹ * (((2 * k - 1)‼ : ℝ) * sqrt (2 * π))) := by
    have := hkey
    field_simp at this ⊢
    linarith
  rw [this]
  -- Simplify the prefactor: (t^k)⁻¹ * (√t)⁻¹ = t^(-(k + 1/2)).
  rw [show ((t : ℝ) ^ k)⁻¹ * ((sqrt t)⁻¹ * (((2 * k - 1)‼ : ℝ) * sqrt (2 * π))) =
        (((2 * k - 1)‼ : ℝ) * sqrt (2 * π)) * ((t ^ k)⁻¹ * (sqrt t)⁻¹) by ring]
  congr 1
  -- Goal: (t^k)⁻¹ * (√t)⁻¹ = t^(-(↑k + 1/2)).
  rw [show ((t : ℝ) ^ k : ℝ) = (t : ℝ) ^ ((k : ℝ)) from (rpow_natCast t k).symm,
      Real.sqrt_eq_rpow]
  rw [← rpow_neg ht.le, ← rpow_neg ht.le, ← rpow_add ht]
  congr 1
  ring

end Laplace.OneD
