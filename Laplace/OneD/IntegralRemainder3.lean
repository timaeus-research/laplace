/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.IntegralRemainder2

/-!
# Fourth-order integral remainder

Replacing the quadratisation `e^(-s) ≈ 1 - s + s²/2` by the cubisation
`e^(-s) ≈ 1 - s + s²/2 - s³/6` improves the integrated remainder from `O(1/(t√t))` to `O(1/t²)`
(`perturbation_remainder4_integral_bound`). The pointwise input is `abs_expRemainder_le_max` at
order four. The fourth power of the rescaled perturbation is even, so no odd absolute powers need
absorbing: `|s_t|⁴ ≤ 8(A⁴ + B⁴)(u¹² + u¹⁶)/t²` for `t ≥ 1` (`rescaled_fourth_bound`), by the
convexity inequality `(x + y)⁴ ≤ 8(x⁴ + y⁴)`.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- Pointwise quartic-order remainder bound with the Gaussian weight. -/
theorem perturbation_remainder4_pointwise (n : ℕ) (u s : ℝ) :
    |u ^ n * Real.exp (-(u ^ 2) / 2) * (Real.exp (-s) - (1 - s + s ^ 2 / 2 - s ^ 3 / 6))| ≤
      (|s| ^ 4 / 24) * |u| ^ n * Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s)) := by
  have hexp_pos : 0 < Real.exp (-(u ^ 2) / 2) := Real.exp_pos _
  have hE4 : Real.exp (-s) - (1 - s + s ^ 2 / 2 - s ^ 3 / 6) = expRemainder 4 s := by
    simp only [expRemainder, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    ring
  have hbound : |Real.exp (-s) - (1 - s + s ^ 2 / 2 - s ^ 3 / 6)| ≤
      |s| ^ 4 / 24 * max 1 (Real.exp (-s)) := by
    rw [hE4]
    have h := abs_expRemainder_le_max 4 s
    have h24 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [h24] at h
    exact h
  rw [abs_mul, abs_mul, abs_pow, abs_of_pos hexp_pos]
  rw [show (|s| ^ 4 / 24 * |u| ^ n * Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s)) : ℝ) =
      |u| ^ n * Real.exp (-(u ^ 2) / 2) * (|s| ^ 4 / 24 * max 1 (Real.exp (-s))) by ring]
  apply mul_le_mul_of_nonneg_left hbound
  positivity

/-- `(x + y)⁴ ≤ 8(x⁴ + y⁴)`: `8(x⁴ + y⁴) − (x + y)⁴ = (x − y)²(7x² + 10xy + 7y²)`. -/
lemma add_pow_four_le_eight_mul (x y : ℝ) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h7 : 0 ≤ 7 * x ^ 2 + 10 * x * y + 7 * y ^ 2 := by
    nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
  nlinarith [mul_nonneg (sq_nonneg (x - y)) h7]

/-- The fourth power of the rescaled perturbation at scale `1/t²`: for `t ≥ 1`,
`|s_t(u)|⁴ ≤ 8(A⁴ + B⁴)(u¹² + u¹⁶)/t²`. -/
theorem rescaled_fourth_bound {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) {t : ℝ} (ht : 1 ≤ t) (u : ℝ) :
    |rescaledPerturbation lam alpha gamma t u| ^ 4 ≤
      8 * (cubicScale lam alpha ^ 4 + quarticScale lam gamma ^ 4) * (u ^ 12 + u ^ 16) / t ^ 2 := by
  set A := cubicScale lam alpha with hA_def
  set B := quarticScale lam gamma with hB_def
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hB_pos : 0 < B := by
    rw [hB_def]
    unfold quarticScale
    positivity
  have hu4 : |u| ^ 4 = u ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hu12 : |u| ^ 12 = u ^ 12 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, pow_mul, sq_abs]
  have hA4 : |A| ^ 4 = A ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  set x := |A| * |u| ^ 3 / Real.sqrt t with hx_def
  set y := B * u ^ 4 / t with hy_def
  have habs : |rescaledPerturbation lam alpha gamma t u| ≤ x + y := by
    unfold rescaledPerturbation
    rw [hx_def, hy_def, ← hA_def, ← hB_def]
    calc |A * u ^ 3 / Real.sqrt t + B * u ^ 4 / t|
        ≤ |A * u ^ 3 / Real.sqrt t| + |B * u ^ 4 / t| := abs_add_le _ _
      _ = |A| * |u| ^ 3 / Real.sqrt t + B * u ^ 4 / t := by
          rw [abs_div, abs_div, abs_mul, abs_mul, abs_pow, abs_pow,
            abs_of_pos hst, abs_of_pos ht0, abs_of_pos hB_pos, hu4]
  have hx4 : x ^ 4 = A ^ 4 * u ^ 12 / t ^ 2 := by
    have h1 : (|u| ^ 3) ^ 4 = u ^ 12 := by
      rw [← pow_mul]
      exact hu12
    have h2 : Real.sqrt t ^ 4 = t ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ht0.le]
    rw [hx_def, div_pow, mul_pow, h1, h2, hA4]
  have hu16nn : (0 : ℝ) ≤ u ^ 16 := by
    rw [show (16 : ℕ) = 2 * 8 from rfl, pow_mul]
    positivity
  have hu12nn : (0 : ℝ) ≤ u ^ 12 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul]
    positivity
  have hy4 : y ^ 4 ≤ B ^ 4 * u ^ 16 / t ^ 2 := by
    have hyeq : y ^ 4 = B ^ 4 * u ^ 16 / t ^ 4 := by
      rw [hy_def, div_pow, mul_pow, ← pow_mul]
    rw [hyeq]
    have hnum : (0 : ℝ) ≤ B ^ 4 * u ^ 16 := mul_nonneg (by positivity) hu16nn
    have hden : t ^ 2 ≤ t ^ 4 := pow_le_pow_right₀ ht (by norm_num)
    gcongr
  have hA4nn : (0 : ℝ) ≤ A ^ 4 := by
    rw [← hA4]
    positivity
  have hB4nn : (0 : ℝ) ≤ B ^ 4 := by positivity
  calc |rescaledPerturbation lam alpha gamma t u| ^ 4
      ≤ (x + y) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) habs 4
    _ ≤ 8 * (x ^ 4 + y ^ 4) := add_pow_four_le_eight_mul x y
    _ ≤ 8 * (A ^ 4 * u ^ 12 / t ^ 2 + B ^ 4 * u ^ 16 / t ^ 2) := by
        rw [← hx4]
        gcongr
    _ = 8 * (A ^ 4 * u ^ 12 + B ^ 4 * u ^ 16) / t ^ 2 := by ring
    _ ≤ 8 * (A ^ 4 + B ^ 4) * (u ^ 12 + u ^ 16) / t ^ 2 := by
        rw [show (8 : ℝ) * (A ^ 4 + B ^ 4) * (u ^ 12 + u ^ 16) / t ^ 2 =
            8 * ((A ^ 4 + B ^ 4) * (u ^ 12 + u ^ 16)) / t ^ 2 by ring]
        gcongr
        nlinarith [mul_nonneg hA4nn hu16nn, mul_nonneg hB4nn hu12nn]

/-- **Combined pointwise quartic-order bound**: constants `C₀, c₀` with
`|uⁿ e^(-u²/2) (e^(-s_t) - (1 - s_t + s_t²/2 - s_t³/6))| ≤ (C₀/t²) |u|ⁿ (u¹² + u¹⁶) e^(-c₀u²)`
for `t ≥ 1`. -/
theorem perturbation_remainder4_combined {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ C₀ c₀ : ℝ, 0 ≤ C₀ ∧ 0 < c₀ ∧ ∀ {t : ℝ}, 1 ≤ t → ∀ (n : ℕ) (u : ℝ),
      |u ^ n * Real.exp (-(u ^ 2) / 2) *
        (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
         (1 - rescaledPerturbation lam alpha gamma t u +
           rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
           rescaledPerturbation lam alpha gamma t u ^ 3 / 6))| ≤
      (C₀ / t ^ 2) * |u| ^ n * (u ^ 12 + u ^ 16) * Real.exp (-(c₀ * u ^ 2)) := by
  obtain ⟨c₀, hc₀_pos, hdecay⟩ := rescaled_max_decay hlam hgamma hdisc
  refine ⟨8 * (cubicScale lam alpha ^ 4 + quarticScale lam gamma ^ 4) / 24, c₀,
    by positivity, hc₀_pos, ?_⟩
  intro t ht n u
  have ht0 : (0 : ℝ) < t := by linarith
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  set s := rescaledPerturbation lam alpha gamma t u with hs_def
  have h1 := perturbation_remainder4_pointwise n u s
  have h2 : Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s)) ≤ Real.exp (-(c₀ * u ^ 2)) :=
    hdecay ht0 u
  have h3 := rescaled_fourth_bound (alpha := alpha) hlam hgamma ht u
  rw [← hs_def] at h3
  have hpows : (0 : ℝ) ≤ u ^ 12 + u ^ 16 := by
    have h12 : (0 : ℝ) ≤ u ^ 12 := by
      rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul]
      positivity
    have h16 : (0 : ℝ) ≤ u ^ 16 := by
      rw [show (16 : ℕ) = 2 * 8 from rfl, pow_mul]
      positivity
    linarith
  calc |u ^ n * Real.exp (-(u ^ 2) / 2) * (Real.exp (-s) - (1 - s + s ^ 2 / 2 - s ^ 3 / 6))|
      ≤ (|s| ^ 4 / 24) * |u| ^ n * Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s)) := h1
    _ = (|s| ^ 4 / 24) * |u| ^ n * (Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s))) := by ring
    _ ≤ (|s| ^ 4 / 24) * |u| ^ n * Real.exp (-(c₀ * u ^ 2)) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
    _ ≤ ((8 * (cubicScale lam alpha ^ 4 + quarticScale lam gamma ^ 4) * (u ^ 12 + u ^ 16) /
          t ^ 2) / 24) * |u| ^ n * Real.exp (-(c₀ * u ^ 2)) := by
        gcongr ?_ / 24 * |u| ^ n * Real.exp (-(c₀ * u ^ 2))
    _ = (8 * (cubicScale lam alpha ^ 4 + quarticScale lam gamma ^ 4) / 24 / t ^ 2) *
          |u| ^ n * (u ^ 12 + u ^ 16) * Real.exp (-(c₀ * u ^ 2)) := by
        field_simp

/-- Integrability of `|u|ⁿ (u¹² + u¹⁶) e^(-cu²)`. -/
theorem integrable_pow_add2_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Integrable (fun u : ℝ ↦ |u| ^ n * (u ^ 12 + u ^ 16) * Real.exp (-(c * u ^ 2))) := by
  have hterm : ∀ k : ℕ, Integrable (fun u : ℝ ↦
      |u| ^ n * u ^ (2 * k) * Real.exp (-(c * u ^ 2))) := by
    intro k
    have h_eq : (fun u : ℝ ↦ |u| ^ n * u ^ (2 * k) * Real.exp (-(c * u ^ 2))) =
        fun u : ℝ ↦ |u| ^ (n + 2 * k) * Real.exp (-(c * u ^ 2)) := by
      ext u
      rw [pow_add, show |u| ^ (2 * k) = u ^ (2 * k) from by rw [pow_mul, pow_mul, sq_abs]]
    rw [h_eq]
    exact integrable_abs_pow_mul_exp_neg_mul_sq hc (n + 2 * k)
  have h_split : (fun u : ℝ ↦ |u| ^ n * (u ^ 12 + u ^ 16) * Real.exp (-(c * u ^ 2))) =
      (fun u : ℝ ↦ |u| ^ n * u ^ (2 * 6) * Real.exp (-(c * u ^ 2)))
      + fun u : ℝ ↦ |u| ^ n * u ^ (2 * 8) * Real.exp (-(c * u ^ 2)) := by
    ext u
    simp only [Pi.add_apply]
    norm_num
    ring
  rw [h_split]
  exact (hterm 6).add (hterm 8)

/-- The quartic-order remainder integrand is integrable for `t ≥ 1`. -/
theorem integrable_remainder4 {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (n : ℕ) {t : ℝ}
    (ht : 1 ≤ t) :
    Integrable (fun u : ℝ ↦ u ^ n * Real.exp (-(u ^ 2) / 2) *
      (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
       (1 - rescaledPerturbation lam alpha gamma t u +
         rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
         rescaledPerturbation lam alpha gamma t u ^ 3 / 6))) := by
  obtain ⟨C₀, c₀, hC₀_nn, hc₀_pos, hpointwise⟩ := perturbation_remainder4_combined hlam hgamma hdisc
  have ht0 : (0 : ℝ) < t := by linarith
  have hint_g : Integrable (fun u : ℝ ↦ (C₀ / t ^ 2) * |u| ^ n * (u ^ 12 + u ^ 16) *
      Real.exp (-(c₀ * u ^ 2))) := by
    have hgs : (fun u : ℝ ↦ (C₀ / t ^ 2) * |u| ^ n * (u ^ 12 + u ^ 16) *
        Real.exp (-(c₀ * u ^ 2))) = (C₀ / t ^ 2) • (fun u : ℝ ↦
        |u| ^ n * (u ^ 12 + u ^ 16) * Real.exp (-(c₀ * u ^ 2))) := by
      ext u
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hgs]
    exact (integrable_pow_add2_mul_exp_neg_mul_sq hc₀_pos n).smul _
  apply Integrable.mono' hint_g
  · apply Continuous.aestronglyMeasurable
    unfold rescaledPerturbation cubicScale quarticScale
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    fun_prop
  · exact Filter.Eventually.of_forall fun u ↦ (Real.norm_eq_abs _).symm ▸ hpointwise ht n u

/-- **Global `O(1/t²)` remainder bound**: the integral of the quartic-order perturbative remainder
against `uⁿ e^(-u²/2)` is bounded by `K/t²`. -/
theorem perturbation_remainder4_integral_bound {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
           (1 - rescaledPerturbation lam alpha gamma t u +
             rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
             rescaledPerturbation lam alpha gamma t u ^ 3 / 6))| ≤ K / t ^ 2 := by
  obtain ⟨C₀, c₀, hC₀_nn, hc₀_pos, hpointwise⟩ := perturbation_remainder4_combined hlam hgamma hdisc
  have hint_bound : Integrable (fun u : ℝ ↦ |u| ^ n * (u ^ 12 + u ^ 16) *
      Real.exp (-(c₀ * u ^ 2))) := integrable_pow_add2_mul_exp_neg_mul_sq hc₀_pos n
  set M := ∫ u : ℝ, |u| ^ n * (u ^ 12 + u ^ 16) * Real.exp (-(c₀ * u ^ 2)) with hM_def
  have hM_nn : 0 ≤ M := by
    apply integral_nonneg
    intro u
    have h12 : (0 : ℝ) ≤ u ^ 12 := by
      rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul]
      positivity
    have h16 : (0 : ℝ) ≤ u ^ 16 := by
      rw [show (16 : ℕ) = 2 * 8 from rfl, pow_mul]
      positivity
    have hsum : (0 : ℝ) ≤ u ^ 12 + u ^ 16 := by linarith
    positivity
  refine ⟨C₀ * M, mul_nonneg hC₀_nn hM_nn, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  set f := fun u : ℝ ↦ u ^ n * Real.exp (-(u ^ 2) / 2) *
    (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
     (1 - rescaledPerturbation lam alpha gamma t u +
       rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
       rescaledPerturbation lam alpha gamma t u ^ 3 / 6)) with hf_def
  set g := fun u : ℝ ↦ (C₀ / t ^ 2) * |u| ^ n * (u ^ 12 + u ^ 16) *
    Real.exp (-(c₀ * u ^ 2)) with hg_def
  have hint_g : Integrable g := by
    have hgs : g = (C₀ / t ^ 2) • (fun u : ℝ ↦
        |u| ^ n * (u ^ 12 + u ^ 16) * Real.exp (-(c₀ * u ^ 2))) := by
      ext u
      simp only [hg_def, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hgs]
    exact hint_bound.smul _
  have hfg : ∀ u, |f u| ≤ g u := fun u ↦ hpointwise ht n u
  have hint_f : Integrable f := integrable_remainder4 hlam hgamma hdisc n ht
  calc |∫ u : ℝ, f u|
      ≤ ∫ u : ℝ, |f u| := abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, g u := integral_mono hint_f.abs hint_g fun u ↦ hfg u
    _ = (C₀ / t ^ 2) * M := by
        rw [hg_def, hM_def]
        simp only
        rw [← integral_const_mul]
        congr 1
        funext u
        ring
    _ = C₀ * M / t ^ 2 := by ring

end Laplace.OneD
