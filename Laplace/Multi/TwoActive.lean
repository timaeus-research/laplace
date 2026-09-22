/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.WallCrossover

/-!
# Towards several active variables: the scale-invariant one-variable bound

The chart integrals of a resolution in `d ≥ 2` have several active variables,
`∫ f(u) ∏ |u_j|^{h_j} e^{-t a(u) ∏ u_j^{2k_j}} du`. The route to their leading asymptotics
(Astra, `gpt_responses/research_multi_active_v1.md`) integrates out the coordinate with the smallest
exponent first, at the effective temperature `T = t ∏_{i≠j} u_i^{2k_i}`, which is NOT bounded below.
The lemma that makes this work is a bound valid for EVERY `T > 0`:

  `T^{e} |∫ g(x) |x|^h e^{-T A(x) x^{2k}} dx| ≤ ‖g‖_∞ a₀^{-e} c_{k,h}`,  `e = (h+1)/2k`

(`rpow_mul_abs_integral_le`), with `c_{k,h} = ∫ |u|^h e^{-u^{2k}} du`. It is the one-variable chart
integral's exact scaling, made into an inequality.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- **The scale-invariant bound** for a one-variable chart integral, valid at every temperature. -/
theorem rpow_mul_abs_integral_le {g A : ℝ → ℝ} {M : ℝ} (hgM : ∀ x, |g x| ≤ M)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hAl : ∀ x, a₀ ≤ A x) (k h : ℕ) (hk : 1 ≤ k)
    {T : ℝ} (hT : 0 < T) :
    T ^ (((h : ℝ) + 1) / (2 * k)) * |∫ x, g x * |x| ^ h * Real.exp (-(T * A x * x ^ (2 * k)))| ≤
      M * a₀ ^ (-((h : ℝ) + 1) / (2 * k)) * agmom k h := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hgM 0)
  have hTa : 0 < T * a₀ := mul_pos hT ha₀
  -- the dominating integral in closed form
  have hdom := integral_abs_pow_mul_exp_neg_mul_pow hTa k hk h
  have hint := integrable_abs_pow_mul_exp_neg_mul_pow hTa k hk h
  -- pointwise bound
  have hpt : ∀ x, ‖g x * |x| ^ h * Real.exp (-(T * A x * x ^ (2 * k)))‖ ≤
      M * (|x| ^ h * Real.exp (-(T * a₀ * x ^ (2 * k)))) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (abs_nonneg x) h),
      Real.abs_exp]
    have h2k := even_pow_nonneg x k
    have hexp : Real.exp (-(T * A x * x ^ (2 * k))) ≤ Real.exp (-(T * a₀ * x ^ (2 * k))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hAl x) hT.le) h2k
      linarith
    calc |g x| * |x| ^ h * Real.exp (-(T * A x * x ^ (2 * k)))
        ≤ M * |x| ^ h * Real.exp (-(T * a₀ * x ^ (2 * k))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hgM x) (pow_nonneg (abs_nonneg _) _)) hexp
            (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hle : |∫ x, g x * |x| ^ h * Real.exp (-(T * A x * x ^ (2 * k)))| ≤
      M * ∫ x, |x| ^ h * Real.exp (-(T * a₀ * x ^ (2 * k))) := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hint.const_mul M) (Filter.Eventually.of_forall hpt)
  rw [hdom] at hle
  calc T ^ (((h : ℝ) + 1) / (2 * k)) * |∫ x, g x * |x| ^ h * Real.exp (-(T * A x * x ^ (2 * k)))|
      ≤ T ^ (((h : ℝ) + 1) / (2 * k)) * (M * ((T * a₀) ^ (-((h : ℝ) + 1) / (2 * k)) * agmom k h)) :=
        mul_le_mul_of_nonneg_left hle (Real.rpow_pos_of_pos hT _).le
    _ = M * a₀ ^ (-((h : ℝ) + 1) / (2 * k)) * agmom k h := by
        rw [Real.mul_rpow hT.le ha₀.le, neg_div, Real.rpow_neg hT.le]
        field_simp

end Laplace.Multi
