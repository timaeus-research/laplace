/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.MomentSecondOrder
import Laplace.OneD.IntegralRemainder

/-!
# The fourth-cumulant limit (gamma-rung programme, stages 4-5)

The analytic heart of the gamma rung: for the anharmonic potential
`λ/2·x² + α/6·x³ + γ/24·x⁴`, the fourth cumulant of the Gibbs measure
(written as its explicit moment combination) satisfies
`t³·κ₄ → 3α²/λ⁵ - γ/λ⁴` (`kappa4_anharmonic_asymptotic`). The proof
converts the stage-3 second-order moment rates into limits by the
squeeze pattern, splits `t³κ₄` by an exact `ring` identity into five
rate-convertible pieces, and evaluates the constants by the
radical-atom substitution. The `t⁻²` Gaussian contributions cancel in
the combination `μ₄ - 3μ₂²`; what survives at `t⁻³` is exactly the
second-order payload `108A² - 24B` (over `λ²`) of stages 2-3.
-/

open Real MeasureTheory Filter

namespace Laplace.OneD

/-- Squeeze: a rate bound `|f t - L - C/t| ≤ K/(t·√t)` eventually gives
`t·(f t - L) → C`. -/
private lemma tendsto_of_order2_rate {f : ℝ → ℝ} {L C K T : ℝ}
    (hT : 1 ≤ T)
    (h : ∀ {t : ℝ}, T ≤ t → |f t - L - C / t| ≤ K / (t * Real.sqrt t)) :
    Tendsto (fun t : ℝ ↦ t * (f t - L)) atTop (nhds C) := by
  have hzero : Tendsto (fun t : ℝ ↦ t * (f t - L) - C) atTop (nhds 0) := by
    have hbound : ∀ᶠ t : ℝ in atTop,
        ‖t * (f t - L) - C‖ ≤ K / Real.sqrt t := by
      filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (1 : ℝ)]
        with t htT ht1
      have ht0 : (0 : ℝ) < t := by linarith
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      have hb := h htT
      have heq : t * (f t - L) - C = t * (f t - L - C / t) := by
        field_simp
      rw [Real.norm_eq_abs, heq, abs_mul, abs_of_pos ht0]
      calc t * |f t - L - C / t| ≤ t * (K / (t * Real.sqrt t)) := by
            gcongr
        _ = K / Real.sqrt t := by
            field_simp
    have hCt : Tendsto (fun t : ℝ ↦ K / Real.sqrt t) atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ ↦ Real.sqrt t) atTop atTop :=
        Real.tendsto_sqrt_atTop
      simpa using h1.inv_tendsto_atTop.const_mul K
    exact squeeze_zero_norm' hbound hCt
  have := hzero.add_const C
  simpa using this

/-- Squeeze: a rate bound `|f t - L| ≤ K/√t` eventually gives
`f → L`. -/
private lemma tendsto_of_sqrt_rate {f : ℝ → ℝ} {L K T : ℝ}
    (hT : 1 ≤ T)
    (h : ∀ {t : ℝ}, T ≤ t → |f t - L| ≤ K / Real.sqrt t) :
    Tendsto f atTop (nhds L) := by
  have hzero : Tendsto (fun t : ℝ ↦ f t - L) atTop (nhds 0) := by
    have hbound : ∀ᶠ t : ℝ in atTop, ‖f t - L‖ ≤ K / Real.sqrt t := by
      filter_upwards [eventually_ge_atTop T] with t htT
      rw [Real.norm_eq_abs]
      exact h htT
    have hCt : Tendsto (fun t : ℝ ↦ K / Real.sqrt t) atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ ↦ Real.sqrt t) atTop atTop :=
        Real.tendsto_sqrt_atTop
      simpa using h1.inv_tendsto_atTop.const_mul K
    exact squeeze_zero_norm' hbound hCt
  have := hzero.add_const L
  simpa using this

/-- **The fourth-cumulant limit** (gamma-rung stages 4-5): writing
`μ_r` for the Gibbs expectation of `x^r` under the anharmonic potential,
`t³·(μ₄ - 4μ₃μ₁ - 3μ₂² + 12μ₂μ₁² - 6μ₁⁴) → 3α²/λ⁵ - γ/λ⁴`. -/
theorem kappa4_anharmonic_asymptotic {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Tendsto (fun t : ℝ ↦ t ^ 3 *
      (Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x ↦ x ^ 4)
        - 4 * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 3) *
          Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x ↦ x)
        - 3 * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 2) ^ 2
        + 12 * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 2) *
          Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x ↦ x) ^ 2
        - 6 * Laplace.gibbsExpectation
            (anharmonicPotential lam alpha gamma) t (fun x ↦ x) ^ 4))
      atTop
      (nhds (3 * alpha ^ 2 / lam ^ 5 - gamma / lam ^ 4)) := by
  set μ₁ : ℝ → ℝ := fun t ↦ Laplace.gibbsExpectation
    (anharmonicPotential lam alpha gamma) t (fun x ↦ x) with hμ₁
  set μ₂ : ℝ → ℝ := fun t ↦ Laplace.gibbsExpectation
    (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 2) with hμ₂
  set μ₃ : ℝ → ℝ := fun t ↦ Laplace.gibbsExpectation
    (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 3) with hμ₃
  set μ₄ : ℝ → ℝ := fun t ↦ Laplace.gibbsExpectation
    (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 4) with hμ₄
  set A := cubicScale lam alpha with hA_def
  set B := quarticScale lam gamma with hB_def
  set C₂ : ℝ := (45 * A ^ 2 - 12 * B) / lam with hC₂_def
  set C₄ : ℝ := (450 * A ^ 2 - 96 * B) / lam ^ 2 with hC₄_def
  -- The five limits.
  obtain ⟨K₂, T₂, hK₂, hT₂, hr₂⟩ :=
    secondMoment_anharmonic_order2_rate hlam hgamma hdisc
  obtain ⟨K₄, T₄, hK₄, hT₄, hr₄⟩ :=
    fourthMoment_anharmonic_order2_rate hlam hgamma hdisc
  obtain ⟨K₃, T₃, hK₃, hT₃, hr₃⟩ :=
    thirdMoment_anharmonic_rate hlam hgamma hdisc
  have hL2a : Tendsto (fun t : ℝ ↦ t * (t * μ₂ t - 1 / lam)) atTop
      (nhds C₂) := by
    apply tendsto_of_order2_rate (T := T₂) hT₂
    intro t ht
    have := hr₂ ht
    rw [hC₂_def]
    calc |t * μ₂ t - 1 / lam - (45 * A ^ 2 - 12 * B) / lam / t|
        = |t * μ₂ t - 1 / lam - (45 * A ^ 2 - 12 * B) / (lam * t)| := by
          rw [div_div]
      _ ≤ K₂ / (t * Real.sqrt t) := this
  have hL4a : Tendsto (fun t : ℝ ↦ t * (t ^ 2 * μ₄ t - 3 / lam ^ 2))
      atTop (nhds C₄) := by
    apply tendsto_of_order2_rate (T := T₄) hT₄
    intro t ht
    have := hr₄ ht
    rw [hC₄_def]
    calc |t ^ 2 * μ₄ t - 3 / lam ^ 2 -
          (450 * A ^ 2 - 96 * B) / lam ^ 2 / t|
        = |t ^ 2 * μ₄ t - 3 / lam ^ 2 -
            (450 * A ^ 2 - 96 * B) / (lam ^ 2 * t)| := by
          rw [div_div]
      _ ≤ K₄ / (t * Real.sqrt t) := this
  have hL3 : Tendsto (fun t : ℝ ↦ t ^ 2 * μ₃ t) atTop
      (nhds (-(15 * A / Real.sqrt lam ^ 3))) := by
    apply tendsto_of_sqrt_rate (T := T₃) hT₃
    intro t ht
    have := hr₃ ht
    calc |t ^ 2 * μ₃ t - -(15 * A / Real.sqrt lam ^ 3)|
        = |t ^ 2 * μ₃ t + 15 * A / Real.sqrt lam ^ 3| := by
          rw [sub_neg_eq_add]
      _ ≤ K₃ / Real.sqrt t := this
  have hL1 : Tendsto (fun t : ℝ ↦ t * μ₁ t) atTop
      (nhds (-alpha / (2 * lam ^ 2))) :=
    mean_anharmonic_asymptotic hlam hgamma hdisc
  have hL2 : Tendsto (fun t : ℝ ↦ t * μ₂ t) atTop (nhds (1 / lam)) := by
    have hdiv : Tendsto (fun t : ℝ ↦ (1 : ℝ) / t) atTop (nhds 0) := by
      simpa using tendsto_inv_atTop_zero
    have h := hL2a.mul hdiv
    rw [mul_zero] at h
    apply Tendsto.add_const (1 / lam) at h
    have heq : ∀ᶠ t : ℝ in atTop,
        t * (t * μ₂ t - 1 / lam) * (1 / t) + 1 / lam = t * μ₂ t := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have ht_ne : t ≠ 0 := ht.ne'
      field_simp
      ring
    rw [show (0 : ℝ) + 1 / lam = 1 / lam by ring] at h
    exact h.congr' heq
  -- Piece limits.
  have hP1 : Tendsto (fun t : ℝ ↦
      t * ((t * μ₂ t) ^ 2 - (1 / lam) ^ 2)) atTop
      (nhds (C₂ * (2 / lam))) := by
    have hconst : Tendsto (fun _ : ℝ ↦ (1 : ℝ) / lam) atTop
        (nhds (1 / lam)) := tendsto_const_nhds
    have hprod := hL2a.mul (hL2.add hconst)
    have heq : ∀ᶠ t : ℝ in atTop,
        t * (t * μ₂ t - 1 / lam) * (t * μ₂ t + 1 / lam) =
        t * ((t * μ₂ t) ^ 2 - (1 / lam) ^ 2) := by
      filter_upwards with t
      ring
    have : (1 : ℝ) / lam + 1 / lam = 2 / lam := by ring
    rw [this] at hprod
    exact hprod.congr' heq
  have hP2 : Tendsto (fun t : ℝ ↦ (t ^ 2 * μ₃ t) * (t * μ₁ t)) atTop
      (nhds (-(15 * A / Real.sqrt lam ^ 3) * (-alpha / (2 * lam ^ 2)))) :=
    hL3.mul hL1
  have hP3 : Tendsto (fun t : ℝ ↦ (t * μ₂ t) * (t * μ₁ t) ^ 2) atTop
      (nhds ((1 / lam) * (-alpha / (2 * lam ^ 2)) ^ 2)) :=
    hL2.mul (hL1.pow 2)
  have hP4 : Tendsto (fun t : ℝ ↦ (t * μ₁ t) ^ 4 * (1 / t)) atTop
      (nhds 0) := by
    have hdiv : Tendsto (fun t : ℝ ↦ (1 : ℝ) / t) atTop (nhds 0) := by
      simpa using tendsto_inv_atTop_zero
    have h := (hL1.pow 4).mul hdiv
    rwa [mul_zero] at h
  -- Assemble.
  have hcomb := ((hL4a.sub (hP1.const_mul 3)).sub (hP2.const_mul 4)).add
    ((hP3.const_mul 12).sub (hP4.const_mul 6))
  have heq : ∀ᶠ t : ℝ in atTop,
      t * (t ^ 2 * μ₄ t - 3 / lam ^ 2) -
        3 * (t * ((t * μ₂ t) ^ 2 - (1 / lam) ^ 2)) -
        4 * ((t ^ 2 * μ₃ t) * (t * μ₁ t)) +
        (12 * ((t * μ₂ t) * (t * μ₁ t) ^ 2) -
          6 * ((t * μ₁ t) ^ 4 * (1 / t))) =
      t ^ 3 * (μ₄ t - 4 * μ₃ t * μ₁ t - 3 * μ₂ t ^ 2 +
        12 * μ₂ t * μ₁ t ^ 2 - 6 * μ₁ t ^ 4) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
    ring
  have hfinal := hcomb.congr' heq
  -- Evaluate the constant.
  have hconst : C₄ - 3 * (C₂ * (2 / lam)) -
      4 * (-(15 * A / Real.sqrt lam ^ 3) * (-alpha / (2 * lam ^ 2))) +
      (12 * ((1 / lam) * (-alpha / (2 * lam ^ 2)) ^ 2) - 6 * 0) =
      3 * alpha ^ 2 / lam ^ 5 - gamma / lam ^ 4 := by
    rw [hC₂_def, hC₄_def, hA_def, hB_def]
    unfold cubicScale quarticScale
    set sl : ℝ := Real.sqrt lam with hsl_def
    have hsl_pos : 0 < sl := Real.sqrt_pos.mpr hlam
    have hsl_ne : sl ≠ 0 := hsl_pos.ne'
    have hlam_ne : lam ≠ 0 := hlam.ne'
    rw [show lam = sl * sl from (Real.mul_self_sqrt hlam.le).symm]
    field_simp
    ring
  rw [hconst] at hfinal
  exact hfinal

end Laplace.OneD
