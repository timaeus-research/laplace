/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.IntegralRemainder
import Laplace.OneD.ExpRemainderSigned

/-!
# Second-order integral remainder (gamma-rung programme, stage 2a)

The cubic-order analogue of the first-order remainder layer in
`Laplace.OneD.IntegralRemainder`: replacing the linearisation
`e^(-s) ≈ 1 - s` by the quadratisation `e^(-s) ≈ 1 - s + s²/2` improves
the integrated remainder from `O(1/t)` to `O(1/(t·√t))`
(`perturbation_remainder3_integral_bound`). The pointwise input is the
signed exponential Taylor bound at order three
(`abs_expRemainder_le_max`); the two-branch Gaussian decay
(`rescaled_max_decay`) and the proof architecture are reused from the
first-order layer, with the cube of the rescaled perturbation absorbed
into even powers via `|u|⁹ ≤ u⁸ + u¹⁰`.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- Pointwise cubic-order remainder bound with the Gaussian weight. -/
theorem perturbation_remainder3_pointwise (n : ℕ) (u s : ℝ) :
    |u ^ n * Real.exp (-(u ^ 2) / 2) *
        (Real.exp (-s) - (1 - s + s ^ 2 / 2))| ≤
      (|s| ^ 3 / 6) * |u| ^ n * Real.exp (-(u ^ 2) / 2) *
        max 1 (Real.exp (-s)) := by
  have hexp_pos : 0 < Real.exp (-(u ^ 2) / 2) := Real.exp_pos _
  have hE3 : Real.exp (-s) - (1 - s + s ^ 2 / 2) = expRemainder 3 s := by
    simp [expRemainder, Finset.sum_range_succ, Nat.factorial]
    ring
  have hbound : |Real.exp (-s) - (1 - s + s ^ 2 / 2)| ≤
      |s| ^ 3 / 6 * max 1 (Real.exp (-s)) := by
    rw [hE3]
    have h := abs_expRemainder_le_max 3 s
    norm_num [Nat.factorial] at h
    exact h
  rw [abs_mul, abs_mul, abs_pow, abs_of_pos hexp_pos]
  rw [show (|s| ^ 3 / 6 * |u| ^ n * Real.exp (-(u ^ 2) / 2) *
        max 1 (Real.exp (-s)) : ℝ) =
      |u| ^ n * Real.exp (-(u ^ 2) / 2) *
        (|s| ^ 3 / 6 * max 1 (Real.exp (-s))) by ring]
  apply mul_le_mul_of_nonneg_left hbound
  positivity

/-- Even-power absorption of the odd absolute power:
`|u|⁹ ≤ u⁸ + u¹⁰`. -/
lemma abs_pow_nine_le (u : ℝ) : |u| ^ 9 ≤ u ^ 8 + u ^ 10 := by
  have h8 : u ^ 8 = |u| ^ 8 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, pow_mul, sq_abs]
  have h10 : u ^ 10 = |u| ^ 10 := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h8, h10]
  nlinarith [sq_nonneg (|u| ^ 4 * (|u| - 1)), abs_nonneg u,
    pow_nonneg (abs_nonneg u) 8, pow_nonneg (abs_nonneg u) 4,
    sq_nonneg (|u| ^ 4), sq_nonneg (|u| ^ 5 - |u| ^ 4)]

/-- The cube of the rescaled perturbation at scale `1/(t·√t)`: for
`t ≥ 1`,
`|s_t(u)|³ ≤ 4(|A|³ + B³)(u⁸ + u¹⁰ + u¹²)/(t·√t)`. -/
theorem rescaled_cube_bound {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) {t : ℝ} (ht : 1 ≤ t) (u : ℝ) :
    |rescaledPerturbation lam alpha gamma t u| ^ 3 ≤
      4 * (|cubicScale lam alpha| ^ 3 + quarticScale lam gamma ^ 3) *
        (u ^ 8 + u ^ 10 + u ^ 12) / (t * Real.sqrt t) := by
  set A := cubicScale lam alpha with hA_def
  set B := quarticScale lam gamma with hB_def
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst1 : 1 ≤ Real.sqrt t := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt ht
  have hts : (0 : ℝ) < t * Real.sqrt t := by positivity
  have hB_pos : 0 < B := by
    rw [hB_def]
    unfold quarticScale
    positivity
  have hu4 : |u| ^ 4 = u ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hu12 : |u| ^ 12 = u ^ 12 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, pow_mul, sq_abs]
  set x := |A| * |u| ^ 3 / Real.sqrt t with hx_def
  set y := B * u ^ 4 / t with hy_def
  have hx_nn : 0 ≤ x := by rw [hx_def]; positivity
  have hy_nn : 0 ≤ y := by
    rw [hy_def, ← hu4]
    positivity
  have habs : |rescaledPerturbation lam alpha gamma t u| ≤ x + y := by
    unfold rescaledPerturbation
    rw [hx_def, hy_def, ← hA_def, ← hB_def]
    calc |A * u ^ 3 / Real.sqrt t + B * u ^ 4 / t|
        ≤ |A * u ^ 3 / Real.sqrt t| + |B * u ^ 4 / t| := abs_add_le _ _
      _ = |A| * |u| ^ 3 / Real.sqrt t + B * u ^ 4 / t := by
          rw [abs_div, abs_div, abs_mul, abs_mul, abs_pow, abs_pow,
            abs_of_pos hst, abs_of_pos ht0, abs_of_pos hB_pos, hu4]
  have hx3 : x ^ 3 = |A| ^ 3 * |u| ^ 9 / (t * Real.sqrt t) := by
    rw [hx_def, div_pow, mul_pow, ← pow_mul]
    congr 1
    rw [show Real.sqrt t ^ 3 = Real.sqrt t ^ 2 * Real.sqrt t by ring,
      Real.sq_sqrt ht0.le]
  have hu12nn : (0 : ℝ) ≤ u ^ 12 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul]
    positivity
  have hst_le : Real.sqrt t ≤ t := by
    nlinarith [Real.mul_self_sqrt ht0.le, hst1, hst.le]
  have hy3 : y ^ 3 ≤ B ^ 3 * u ^ 12 / (t * Real.sqrt t) := by
    have hyeq : y ^ 3 = B ^ 3 * u ^ 12 / t ^ 3 := by
      rw [hy_def, div_pow, mul_pow, ← pow_mul]
    rw [hyeq]
    have hnum : (0 : ℝ) ≤ B ^ 3 * u ^ 12 :=
      mul_nonneg (by positivity) hu12nn
    have hden : t * Real.sqrt t ≤ t ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hst_le ht0.le,
        mul_nonneg (mul_nonneg ht0.le ht0.le) (sub_nonneg.mpr ht)]
    gcongr
  have h8 : (0 : ℝ) ≤ u ^ 8 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul]
    positivity
  have h10 : (0 : ℝ) ≤ u ^ 10 := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul]
    positivity
  have h12 : (0 : ℝ) ≤ u ^ 12 := hu12nn
  have hA3 : (0 : ℝ) ≤ |A| ^ 3 := by positivity
  have hB3 : (0 : ℝ) ≤ B ^ 3 := by positivity
  have hnum_le : |A| ^ 3 * |u| ^ 9 + B ^ 3 * u ^ 12 ≤
      (|A| ^ 3 + B ^ 3) * (u ^ 8 + u ^ 10 + u ^ 12) := by
    have h9 := abs_pow_nine_le u
    nlinarith [mul_le_mul_of_nonneg_left h9 hA3,
      mul_nonneg hA3 h12, mul_nonneg hB3 h8, mul_nonneg hB3 h10]
  calc |rescaledPerturbation lam alpha gamma t u| ^ 3
      ≤ (x + y) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) habs 3
    _ ≤ 4 * (x ^ 3 + y ^ 3) := by
        nlinarith [sq_nonneg (x - y), mul_nonneg hx_nn hy_nn,
          mul_nonneg (mul_nonneg hx_nn hy_nn) (add_nonneg hx_nn hy_nn)]
    _ ≤ 4 * (|A| ^ 3 * |u| ^ 9 / (t * Real.sqrt t) +
          B ^ 3 * u ^ 12 / (t * Real.sqrt t)) := by
        rw [← hx3]
        gcongr
    _ = 4 * (|A| ^ 3 * |u| ^ 9 + B ^ 3 * u ^ 12) / (t * Real.sqrt t) := by
        ring
    _ ≤ 4 * (|A| ^ 3 + B ^ 3) * (u ^ 8 + u ^ 10 + u ^ 12) /
          (t * Real.sqrt t) := by
        rw [show (4 : ℝ) * (|A| ^ 3 + B ^ 3) * (u ^ 8 + u ^ 10 + u ^ 12) /
            (t * Real.sqrt t) =
            4 * ((|A| ^ 3 + B ^ 3) * (u ^ 8 + u ^ 10 + u ^ 12)) /
            (t * Real.sqrt t) by ring]
        gcongr

/-- **Combined pointwise cubic-order bound**: constants `C₀, c₀` with
`|u^n·e^(-u²/2)·(e^(-s_t) - (1 - s_t + s_t²/2))| ≤
  (C₀/(t·√t))·|u|^n·(u⁸+u¹⁰+u¹²)·e^(-c₀u²)` for `t ≥ 1`. -/
theorem perturbation_remainder3_combined {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ C₀ c₀ : ℝ, 0 ≤ C₀ ∧ 0 < c₀ ∧ ∀ {t : ℝ}, 1 ≤ t → ∀ (n : ℕ) (u : ℝ),
      |u ^ n * Real.exp (-(u ^ 2) / 2) *
        (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
         (1 - rescaledPerturbation lam alpha gamma t u +
           rescaledPerturbation lam alpha gamma t u ^ 2 / 2))| ≤
      (C₀ / (t * Real.sqrt t)) * |u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) *
        Real.exp (-(c₀ * u ^ 2)) := by
  obtain ⟨c₀, hc₀_pos, hdecay⟩ := rescaled_max_decay hlam hgamma hdisc
  have hB_pos : 0 < quarticScale lam gamma := by
    unfold quarticScale
    positivity
  refine ⟨4 * (|cubicScale lam alpha| ^ 3 + quarticScale lam gamma ^ 3) / 6,
    c₀, by positivity, hc₀_pos, ?_⟩
  intro t ht n u
  have ht0 : (0 : ℝ) < t := by linarith
  have hts : (0 : ℝ) < t * Real.sqrt t := by positivity
  set s := rescaledPerturbation lam alpha gamma t u with hs_def
  have h1 := perturbation_remainder3_pointwise n u s
  have h2 : Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s)) ≤
      Real.exp (-(c₀ * u ^ 2)) := hdecay ht0 u
  have h3 := rescaled_cube_bound (alpha := alpha) hlam hgamma ht u
  rw [← hs_def] at h3
  have hpows : (0 : ℝ) ≤ u ^ 8 + u ^ 10 + u ^ 12 := by
    have h8 : (0 : ℝ) ≤ u ^ 8 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul]; positivity
    have h10 : (0 : ℝ) ≤ u ^ 10 := by
      rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul]; positivity
    have h12 : (0 : ℝ) ≤ u ^ 12 := by
      rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul]; positivity
    linarith
  calc |u ^ n * Real.exp (-(u ^ 2) / 2) *
      (Real.exp (-s) - (1 - s + s ^ 2 / 2))|
      ≤ (|s| ^ 3 / 6) * |u| ^ n * Real.exp (-(u ^ 2) / 2) *
        max 1 (Real.exp (-s)) := h1
    _ = (|s| ^ 3 / 6) * |u| ^ n *
        (Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s))) := by ring
    _ ≤ (|s| ^ 3 / 6) * |u| ^ n * Real.exp (-(c₀ * u ^ 2)) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
    _ ≤ ((4 * (|cubicScale lam alpha| ^ 3 + quarticScale lam gamma ^ 3) *
          (u ^ 8 + u ^ 10 + u ^ 12) / (t * Real.sqrt t)) / 6) *
        |u| ^ n * Real.exp (-(c₀ * u ^ 2)) := by
        gcongr ?_ / 6 * |u| ^ n * Real.exp (-(c₀ * u ^ 2))
    _ = (4 * (|cubicScale lam alpha| ^ 3 + quarticScale lam gamma ^ 3) / 6 /
          (t * Real.sqrt t)) * |u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) *
        Real.exp (-(c₀ * u ^ 2)) := by
        field_simp

/-- Integrability of `|u|^n·(u⁸+u¹⁰+u¹²)·e^(-cu²)`. -/
theorem integrable_pow_add3_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c)
    (n : ℕ) :
    Integrable (fun u : ℝ ↦
      |u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) * Real.exp (-(c * u ^ 2))) := by
  have hterm : ∀ k : ℕ, Integrable (fun u : ℝ ↦
      |u| ^ n * u ^ (2 * k) * Real.exp (-(c * u ^ 2))) := by
    intro k
    have h_eq : (fun u : ℝ ↦ |u| ^ n * u ^ (2 * k) *
        Real.exp (-(c * u ^ 2))) =
        fun u : ℝ ↦ |u| ^ (n + 2 * k) * Real.exp (-(c * u ^ 2)) := by
      ext u
      rw [pow_add, show |u| ^ (2 * k) = u ^ (2 * k) from by
        rw [pow_mul, pow_mul, sq_abs]]
    rw [h_eq]
    exact integrable_abs_pow_mul_exp_neg_mul_sq hc (n + 2 * k)
  have h_split : (fun u : ℝ ↦
      |u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) * Real.exp (-(c * u ^ 2))) =
      (fun u : ℝ ↦ |u| ^ n * u ^ (2 * 4) * Real.exp (-(c * u ^ 2)))
      + ((fun u : ℝ ↦ |u| ^ n * u ^ (2 * 5) * Real.exp (-(c * u ^ 2)))
        + fun u : ℝ ↦ |u| ^ n * u ^ (2 * 6) * Real.exp (-(c * u ^ 2))) := by
    ext u
    simp only [Pi.add_apply]
    norm_num
    ring
  rw [h_split]
  exact (hterm 4).add ((hterm 5).add (hterm 6))

/-- **Global `O(1/(t·√t))` remainder bound**: the integral of the
cubic-order perturbative remainder against `u^n·e^(-u²/2)` is bounded by
`K/(t·√t)`. -/
theorem perturbation_remainder3_integral_bound {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
           (1 - rescaledPerturbation lam alpha gamma t u +
             rescaledPerturbation lam alpha gamma t u ^ 2 / 2))| ≤
      K / (t * Real.sqrt t) := by
  obtain ⟨C₀, c₀, hC₀_nn, hc₀_pos, hpointwise⟩ :=
    perturbation_remainder3_combined hlam hgamma hdisc
  have hint_bound : Integrable (fun u : ℝ ↦
      |u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) * Real.exp (-(c₀ * u ^ 2))) :=
    integrable_pow_add3_mul_exp_neg_mul_sq hc₀_pos n
  set M := ∫ u : ℝ, |u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) *
    Real.exp (-(c₀ * u ^ 2)) with hM_def
  have hM_nn : 0 ≤ M := by
    apply integral_nonneg
    intro u
    have h8 : (0 : ℝ) ≤ u ^ 8 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul]; positivity
    have h10 : (0 : ℝ) ≤ u ^ 10 := by
      rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul]; positivity
    have h12 : (0 : ℝ) ≤ u ^ 12 := by
      rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul]; positivity
    have habs : (0 : ℝ) ≤ |u| ^ n := pow_nonneg (abs_nonneg u) n
    have hexp : (0 : ℝ) ≤ Real.exp (-(c₀ * u ^ 2)) := (Real.exp_pos _).le
    have hsum : (0 : ℝ) ≤ u ^ 8 + u ^ 10 + u ^ 12 := by linarith
    positivity
  refine ⟨C₀ * M, mul_nonneg hC₀_nn hM_nn, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hts : (0 : ℝ) < t * Real.sqrt t := by positivity
  set f := fun u : ℝ ↦ u ^ n * Real.exp (-(u ^ 2) / 2) *
    (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
     (1 - rescaledPerturbation lam alpha gamma t u +
       rescaledPerturbation lam alpha gamma t u ^ 2 / 2)) with hf_def
  set g := fun u : ℝ ↦ (C₀ / (t * Real.sqrt t)) * |u| ^ n *
    (u ^ 8 + u ^ 10 + u ^ 12) * Real.exp (-(c₀ * u ^ 2)) with hg_def
  have hint_g : Integrable g := by
    have hgs : g = (C₀ / (t * Real.sqrt t)) • (fun u : ℝ ↦
        |u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) *
          Real.exp (-(c₀ * u ^ 2))) := by
      ext u
      simp only [hg_def, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hgs]
    exact hint_bound.smul _
  have hfg : ∀ u, |f u| ≤ g u := fun u ↦ hpointwise ht n u
  have hint_f : Integrable f := by
    apply Integrable.mono' hint_g
    · apply Continuous.aestronglyMeasurable
      simp only [hf_def]
      unfold rescaledPerturbation cubicScale quarticScale
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      fun_prop
    · exact Filter.Eventually.of_forall fun u ↦
        (Real.norm_eq_abs (f u)).symm ▸ hfg u
  calc |∫ u : ℝ, f u|
      ≤ ∫ u : ℝ, |f u| := abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, g u :=
        integral_mono hint_f.abs hint_g fun u ↦ hfg u
    _ = (C₀ / (t * Real.sqrt t)) * M := by
        rw [show g = fun u : ℝ ↦ (C₀ / (t * Real.sqrt t)) *
            (|u| ^ n * (u ^ 8 + u ^ 10 + u ^ 12) *
              Real.exp (-(c₀ * u ^ 2))) from by
          ext u; simp only [hg_def]; ring]
        rw [integral_const_mul]
    _ = C₀ * M / (t * Real.sqrt t) := by ring

end Laplace.OneD
