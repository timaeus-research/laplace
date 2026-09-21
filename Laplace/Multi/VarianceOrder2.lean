/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GibbsRotation
import Laplace.OneD.MomentSecondOrder

/-!
# E7: the remainder after the one-loop term, with an explicit rate

E7 of the note finds that adding the one-loop term to the Laplace covariance takes the relative
remainder from `O(t⁻¹)` to `O(t⁻²)`. From the seabed's explicit moment rates
(`secondMoment_anharmonic_order2_rate`, `mean_anharmonic_O2_rate`) we certify the exact variance
of the anharmonic oscillator to second order with a `t^{-3/2}` remainder:

* `var_order2_coeff`: `(45A² − 12B)/λ − (α/(2λ²))² = α²/λ⁴ − γ/(2λ³)`, the one-loop coefficient;
* `var_anharmonic_order2_rate`: `|t Var_t[x] − 1/λ − (α²/λ⁴ − γ/(2λ³))/t| ≤ K/(t√t)` for `t ≥ T`;
* `var_relative_rate_order2`, `var_relative_rate_order2_note`:
  `|t(λ t Var − 1) − (α²/λ³ − γ/(2λ²))| ≤ K/√t`, and `→ a² − 1/2` with an explicit `K/√t`
  remainder in the note's parametrisation;
* `separableAnharmonic_var_order2_rate_note`, `rotatedAnharmonic_var_order2_rate_note`: the same
  along every coordinate of E2's oscillator and every column of the note's `Q`;
* `mean_anharmonic_rate_div` (`|⟨x⟩ + α/(2λ²t)| ≤ K/t²`), `energy_order1_coeff`,
  `energy_anharmonic_order1_rate` (`|t⟨ℓ⟩ − ½ − c/t| ≤ K/(t√t)`, `c = 5α²/(24λ³) − γ/(8λ²)`) and the
  E2 forms `separableAnharmonic_energy_order1_rate_note`,
  `rotatedAnharmonic_energy_order1_rate_note`
  (`t⟨L⟩ = d/2 + d(5a²/24 − 1/8)/t + O(t^{-3/2})`: E2's "at `t = 3` the exact LLC is 4.76, not 5"
  is this first-order term, `5 − 10·0.073/3 = 4.757`).

The true remainder is `O(t⁻¹)` in `t(λtVar − 1) − (a² − ½)` (numerically `≈ 0.27/t`); the seabed's
rates give `O(t^{-1/2})`, i.e. the one-loop prediction is exact to relative order `t^{-3/2}`.
-/

open MeasureTheory Filter Topology Matrix Laplace.OneD

namespace Laplace.Multi

section OneDim

variable {lam alpha gamma : ℝ}

/-- The second-order coefficient of the variance is the one-loop coefficient:
`(45A² − 12B)/λ − m₀² = α²/λ⁴ − γ/(2λ³)` with `A = α/(6λ√λ)`, `B = γ/(24λ²)`, `m₀ = −α/(2λ²)`. -/
theorem var_order2_coeff (hlam : 0 < lam) :
    (45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma) / lam -
        (-alpha / (2 * lam ^ 2)) ^ 2 =
      alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3) := by
  unfold cubicScale quarticScale
  have hs0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hs : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
  set s := Real.sqrt lam with hsdef
  clear_value s
  subst hs
  have hne : s ≠ 0 := hs0.ne'
  field_simp
  ring

/-- **The exact anharmonic variance at second order, with a rate**:
`|t Var_t[x] − 1/λ − (α²/λ⁴ − γ/(2λ³))/t| ≤ K/(t√t)` for all `t ≥ T`. -/
theorem var_anharmonic_order2_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x) (fun x => x)
        - 1 / lam - (alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3)) / t| ≤ K / (t * Real.sqrt t) := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := secondMoment_anharmonic_order2_rate hlam hgamma hdisc
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := mean_anharmonic_O2_rate hlam hgamma hdisc
  set m₀ : ℝ := -alpha / (2 * lam ^ 2) with hm₀
  set C₂ : ℝ := (45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma) / lam with hC₂
  refine ⟨K₂ + K₁ * (2 * |m₀| + K₁), max T₁ T₂, by positivity, le_max_of_le_left hT₁,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT₁.trans ((le_max_left _ _).trans ht)
  have htpos : 0 < t := by linarith
  have hsqrt : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1
  have e2 := h₂ ((le_max_right _ _).trans ht)
  have e1 := h₁ ((le_max_left _ _).trans ht)
  set M := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x)
    with hM
  set M2 := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2)
    with hM2
  have hcov : _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x)
      (fun x => x) = M2 - M * M := by
    simp only [_root_.Laplace.gibbsCov, hM2, hM, sq]
  have hC : alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3) = C₂ - m₀ ^ 2 := by
    rw [← var_order2_coeff hlam]
  have hC2t : C₂ / t = (45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma) / (lam * t) :=
    div_div _ _ _
  rw [hcov, hC]
  have key : t * (M2 - M * M) - 1 / lam - (C₂ - m₀ ^ 2) / t =
      (t * M2 - 1 / lam - C₂ / t) - (t * M - m₀) * (t * M + m₀) / t := by
    field_simp
    ring
  rw [key]
  have hsum : |t * M + m₀| ≤ 2 * |m₀| + K₁ := by
    have h1 : |t * M + m₀| ≤ |t * M - m₀| + 2 * |m₀| := by
      calc |t * M + m₀| = |(t * M - m₀) + 2 * m₀| := by ring_nf
        _ ≤ |t * M - m₀| + |2 * m₀| := abs_add_le _ _
        _ = |t * M - m₀| + 2 * |m₀| := by rw [abs_mul, abs_two]
    have h2 : K₁ / t ≤ K₁ := div_le_self hK₁ ht1
    linarith
  have hY : |(t * M - m₀) * (t * M + m₀) / t| ≤ K₁ * (2 * |m₀| + K₁) / (t * Real.sqrt t) := by
    rw [abs_div, abs_mul, abs_of_pos htpos]
    have h1 : |t * M - m₀| * |t * M + m₀| ≤ K₁ / t * (2 * |m₀| + K₁) :=
      mul_le_mul e1 hsum (abs_nonneg _) (by positivity)
    have hst : Real.sqrt t ≤ t := by
      calc Real.sqrt t ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = t := Real.sqrt_sq htpos.le
    calc |t * M - m₀| * |t * M + m₀| / t ≤ K₁ / t * (2 * |m₀| + K₁) / t :=
          div_le_div_of_nonneg_right h1 htpos.le
      _ = K₁ * (2 * |m₀| + K₁) / (t * t) := by field_simp
      _ ≤ K₁ * (2 * |m₀| + K₁) / (t * Real.sqrt t) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hst htpos.le)
  rw [← hC2t] at e2
  calc |(t * M2 - 1 / lam - C₂ / t) - (t * M - m₀) * (t * M + m₀) / t|
      ≤ |t * M2 - 1 / lam - C₂ / t| + |(t * M - m₀) * (t * M + m₀) / t| := abs_sub _ _
    _ ≤ K₂ / (t * Real.sqrt t) + K₁ * (2 * |m₀| + K₁) / (t * Real.sqrt t) := add_le_add e2 hY
    _ = (K₂ + K₁ * (2 * |m₀| + K₁)) / (t * Real.sqrt t) := by ring

/-- **E7, relative form**: `|t(λ t Var − 1) − (α²/λ³ − γ/(2λ²))| ≤ K/√t` for `t ≥ T`: the exact
relative covariance error is the one-loop term `(α²/λ³ − γ/(2λ²))/t` up to `O(t^{-3/2})`. -/
theorem var_relative_rate_order2 (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * (lam * t * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x)
          (fun x => x) - 1) - (alpha ^ 2 / lam ^ 3 - gamma / (2 * lam ^ 2))| ≤ K / Real.sqrt t := by
  obtain ⟨K, T, hK, hT, h⟩ := var_anharmonic_order2_rate hlam hgamma hdisc
  refine ⟨lam * K, T, by positivity, hT, fun {t} ht => ?_⟩
  have htpos : 0 < t := by linarith
  have hne := hlam.ne'
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  set V := _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x) (fun x => x)
    with hV
  have key : t * (lam * t * V - 1) - (alpha ^ 2 / lam ^ 3 - gamma / (2 * lam ^ 2)) =
      lam * t * (t * V - 1 / lam - (alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3)) / t) := by
    field_simp
  rw [key, abs_mul, abs_of_pos (mul_pos hlam htpos)]
  calc lam * t * |t * V - 1 / lam - (alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3)) / t|
      ≤ lam * t * (K / (t * Real.sqrt t)) := mul_le_mul_of_nonneg_left (h ht) (by positivity)
    _ = lam * K / Real.sqrt t := by
        field_simp

/-- **E7 in the note's parametrisation** (`α² = a²λ³`, `γ = λ²`, `a² < 3`): the exact relative
covariance error is `(a² − ½)/t` up to an explicit `K/t^{3/2}`. -/
theorem var_relative_rate_order2_note {a : ℝ} (hlam : 0 < lam) (hgamma : gamma = lam ^ 2)
    (halpha : alpha ^ 2 = a ^ 2 * lam ^ 3) (ha : a ^ 2 < 3) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * (lam * t * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t (fun x => x)
          (fun x => x) - 1) - (a ^ 2 - 1 / 2)| ≤ K / Real.sqrt t := by
  have hg : 0 < gamma := by rw [hgamma]; exact pow_pos hlam 2
  have hd : alpha ^ 2 < 3 * lam * gamma := by
    rw [halpha, hgamma]
    nlinarith [pow_pos hlam 3]
  have hne := hlam.ne'
  have hlim : alpha ^ 2 / lam ^ 3 - gamma / (2 * lam ^ 2) = a ^ 2 - 1 / 2 := by
    rw [halpha, hgamma]
    field_simp
  obtain ⟨K, T, hK, hT, h⟩ := var_relative_rate_order2 hlam hg hd
  exact ⟨K, T, hK, hT, fun {t} ht => by rw [← hlim]; exact h ht⟩

end OneDim

/-! ### E2's oscillator, along the coordinates and along the columns of `Q` -/

section Separable

variable {ι : Type*} [Fintype ι] {lam alpha gamma : ι → ℝ}

/-- **E7 for the exact separable oscillator**: along every coordinate the relative covariance
error is `(a² − ½)/t` up to `K/t^{3/2}`. -/
theorem separableAnharmonic_var_order2_rate_note {a : ℝ} (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, gamma i = lam i ^ 2) (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3)
    (ha : a ^ 2 < 3) (i : ι) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * (lam i * t * gibbsCov (separableAnharmonic lam alpha gamma) t (fun w => w i)
          (fun w => w i) - 1) - (a ^ 2 - 1 / 2)| ≤ K / Real.sqrt t := by
  have hg : ∀ i, 0 < gamma i := fun i => by rw [hgamma i]; exact pow_pos (hlam i) 2
  have hd : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i := fun i => by
    rw [halpha i, hgamma i]
    nlinarith [pow_pos (hlam i) 3]
  obtain ⟨K, T, hK, hT, h⟩ := var_relative_rate_order2_note (hlam i) (hgamma i) (halpha i) ha
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have htpos : 0 < t := by linarith
  classical
  rw [gibbsCov_separableAnharmonic hlam hg hd htpos i i, if_pos rfl]
  exact h ht

/-- **E7 in the note's frame**: along every column of `Q` the relative covariance error of the
`anharm` potential is `(a² − ½)/t` up to `K/t^{3/2}`. -/
theorem rotatedAnharmonic_var_order2_rate_note [DecidableEq ι] {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1)
    (c : ι → ℝ)
    {a : ℝ} (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, gamma i = lam i ^ 2)
    (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3) (ha : a ^ 2 < 3) (i : ι) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * (lam i * t * gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
          (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w i) - 1) - (a ^ 2 - 1 / 2)| ≤
        K / Real.sqrt t := by
  obtain ⟨K, T, hK, hT, h⟩ := separableAnharmonic_var_order2_rate_note hlam hgamma halpha ha i
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  rw [gibbsCov_rotatedAnharmonic_eq hQ c t i i]
  exact h ht

end Separable

/-! ### The mean, restated, and the energy at first order -/

section Energy

variable {lam alpha gamma : ℝ}

/-- The mean rate in the form `|⟨x⟩ + α/(2λ² t)| ≤ K/t²`. -/
theorem mean_anharmonic_rate_div (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) -
        (-alpha / (2 * lam ^ 2)) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := mean_anharmonic_O2_rate hlam hgamma hdisc
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have htpos : 0 < t := by linarith
  have key : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) -
      (-alpha / (2 * lam ^ 2)) / t =
      (t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) -
        (-alpha / (2 * lam ^ 2))) / t := by
    field_simp
  rw [key, abs_div, abs_of_pos htpos]
  calc _ ≤ K / t / t := div_le_div_of_nonneg_right (h ht) htpos.le
    _ = K / t ^ 2 := by ring

/-- The first-order energy coefficient:
`(λ/2)C₂ − (α/6)(15A/√λ³) + (γ/24)(3/λ²) = 5α²/(24λ³) − γ/(8λ²)`. -/
theorem energy_order1_coeff (hlam : 0 < lam) :
    lam / 2 * ((45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma) / lam) +
        alpha / 6 * (-(15 * cubicScale lam alpha / Real.sqrt lam ^ 3)) +
        gamma / 24 * (3 / lam ^ 2) =
      5 * alpha ^ 2 / (24 * lam ^ 3) - gamma / (8 * lam ^ 2) := by
  unfold cubicScale quarticScale
  have hs0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hs : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
  set s := Real.sqrt lam with hsdef
  clear_value s
  subst hs
  have hne : s ≠ 0 := hs0.ne'
  field_simp
  ring

/-- **The exact anharmonic energy at first order, with a rate**:
`|t⟨ℓ⟩ − ½ − c/t| ≤ K/(t√t)` with `c = 5α²/(24λ³) − γ/(8λ²)`, from the second-, third- and
fourth-moment rates. -/
theorem energy_anharmonic_order1_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (anharmonicPotential lam alpha gamma) - 1 / 2 -
        (5 * alpha ^ 2 / (24 * lam ^ 3) - gamma / (8 * lam ^ 2)) / t| ≤ K / (t * Real.sqrt t) := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := secondMoment_anharmonic_order2_rate hlam hgamma hdisc
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := thirdMoment_anharmonic_rate hlam hgamma hdisc
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_anharmonic_order2_rate hlam hgamma hdisc
  set C₂ : ℝ := (45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma) / lam with hC₂
  set m₃ : ℝ := -(15 * cubicScale lam alpha / Real.sqrt lam ^ 3) with hm₃
  set C₄ : ℝ := (450 * cubicScale lam alpha ^ 2 - 96 * quarticScale lam gamma) / lam ^ 2 with hC₄
  refine ⟨lam / 2 * K₂ + |alpha| / 6 * K₃ + gamma / 24 * (|C₄| + K₄), max T₂ (max T₃ T₄),
    by positivity, le_max_of_le_left hT₂, fun {t} ht => ?_⟩
  have ht2 : T₂ ≤ t := (le_max_left _ _).trans ht
  have ht3 : T₃ ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
  have ht4 : T₄ ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht
  have ht1 : 1 ≤ t := hT₂.trans ht2
  have htpos : 0 < t := by linarith
  have hsqrt : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1
  have hsqpos : 0 < Real.sqrt t := by linarith
  have hne := hlam.ne'
  set M2 := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2)
    with hM2
  set M3 := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3)
    with hM3
  set M4 := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4)
    with hM4
  have e2 : |t * M2 - 1 / lam - C₂ / t| ≤ K₂ / (t * Real.sqrt t) := by
    rw [hC₂, div_div]
    exact h₂ ht2
  have e3 : |t ^ 2 * M3 - m₃| ≤ K₃ / Real.sqrt t := by
    rw [hm₃, sub_neg_eq_add]
    exact h₃ ht3
  have e4 : |t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t| ≤ K₄ / (t * Real.sqrt t) := by
    rw [hC₄, div_div]
    exact h₄ ht4
  rw [gibbsExpectation_anharmonic_energy hlam hgamma hdisc htpos, ← energy_order1_coeff hlam]
  have key : t * (lam / 2 * M2 + alpha / 6 * M3 + gamma / 24 * M4) - 1 / 2 -
      (lam / 2 * C₂ + alpha / 6 * m₃ + gamma / 24 * (3 / lam ^ 2)) / t =
      lam / 2 * (t * M2 - 1 / lam - C₂ / t) + alpha / 6 * ((t ^ 2 * M3 - m₃) / t) +
        gamma / 24 * ((t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t + C₄ / t ^ 2) := by
    field_simp
    ring
  rw [key]
  have b3 : |(t ^ 2 * M3 - m₃) / t| ≤ K₃ / (t * Real.sqrt t) := by
    rw [abs_div, abs_of_pos htpos]
    calc |t ^ 2 * M3 - m₃| / t ≤ K₃ / Real.sqrt t / t := div_le_div_of_nonneg_right e3 htpos.le
      _ = K₃ / (t * Real.sqrt t) := by rw [div_div, mul_comm]
  have b4 : |(t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t + C₄ / t ^ 2| ≤
      (|C₄| + K₄) / (t * Real.sqrt t) := by
    have b41 : |(t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t| ≤ K₄ / (t * Real.sqrt t) := by
      rw [abs_div, abs_of_pos htpos]
      calc |t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t| / t ≤ K₄ / (t * Real.sqrt t) / t :=
            div_le_div_of_nonneg_right e4 htpos.le
        _ ≤ K₄ / (t * Real.sqrt t) := div_le_self (by positivity) ht1
    have hst : Real.sqrt t ≤ t := by
      calc Real.sqrt t ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = t := Real.sqrt_sq htpos.le
    have b42 : |C₄ / t ^ 2| ≤ |C₄| / (t * Real.sqrt t) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
        (by rw [sq]; exact mul_le_mul_of_nonneg_left hst htpos.le)
    calc |(t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t + C₄ / t ^ 2|
        ≤ |(t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t| + |C₄ / t ^ 2| := abs_add_le _ _
      _ ≤ K₄ / (t * Real.sqrt t) + |C₄| / (t * Real.sqrt t) := add_le_add b41 b42
      _ = (|C₄| + K₄) / (t * Real.sqrt t) := by ring
  calc |lam / 2 * (t * M2 - 1 / lam - C₂ / t) + alpha / 6 * ((t ^ 2 * M3 - m₃) / t) +
        gamma / 24 * ((t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t + C₄ / t ^ 2)|
      ≤ |lam / 2 * (t * M2 - 1 / lam - C₂ / t)| + |alpha / 6 * ((t ^ 2 * M3 - m₃) / t)| +
        |gamma / 24 * ((t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t + C₄ / t ^ 2)| := abs_add_three _ _ _
    _ = lam / 2 * |t * M2 - 1 / lam - C₂ / t| + |alpha| / 6 * |(t ^ 2 * M3 - m₃) / t| +
        gamma / 24 * |(t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t + C₄ / t ^ 2| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam / 2),
          abs_of_pos (by positivity : (0 : ℝ) < gamma / 24), abs_div,
          abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    _ ≤ lam / 2 * (K₂ / (t * Real.sqrt t)) + |alpha| / 6 * (K₃ / (t * Real.sqrt t)) +
        gamma / 24 * ((|C₄| + K₄) / (t * Real.sqrt t)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left e2 (by positivity))
          (mul_le_mul_of_nonneg_left b3 (by positivity)))
          (mul_le_mul_of_nonneg_left b4 (by positivity))
    _ = (lam / 2 * K₂ + |alpha| / 6 * K₃ + gamma / 24 * (|C₄| + K₄)) / (t * Real.sqrt t) := by ring

/-- **E2's finite-`t` LLC in one dimension**: in the note's parametrisation
`t⟨ℓ⟩ = ½ + (5a²/24 − 1/8)/t + O(t^{-3/2})`. -/
theorem energy_anharmonic_order1_rate_note {a : ℝ} (hlam : 0 < lam) (hgamma : gamma = lam ^ 2)
    (halpha : alpha ^ 2 = a ^ 2 * lam ^ 3) (ha : a ^ 2 < 3) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (anharmonicPotential lam alpha gamma) - 1 / 2 - (5 * a ^ 2 / 24 - 1 / 8) / t| ≤
        K / (t * Real.sqrt t) := by
  have hg : 0 < gamma := by rw [hgamma]; exact pow_pos hlam 2
  have hd : alpha ^ 2 < 3 * lam * gamma := by
    rw [halpha, hgamma]
    nlinarith [pow_pos hlam 3]
  have hne := hlam.ne'
  have hc : 5 * alpha ^ 2 / (24 * lam ^ 3) - gamma / (8 * lam ^ 2) = 5 * a ^ 2 / 24 - 1 / 8 := by
    rw [halpha, hgamma]
    field_simp
  obtain ⟨K, T, hK, hT, h⟩ := energy_anharmonic_order1_rate hlam hg hd
  exact ⟨K, T, hK, hT, fun {t} ht => by rw [← hc]; exact h ht⟩

end Energy

section SeparableEnergy

variable {ι : Type*} [Fintype ι] {lam alpha gamma : ι → ℝ}

/-- **E2's finite-`t` LLC for the separable oscillator**:
`t⟨L⟩ = d/2 + d(5a²/24 − 1/8)/t + O(t^{-3/2})` (for `a = ½`, `d = 10`, `t = 3` this first-order
formula gives `4.757`; the note measures `4.76`). -/
theorem separableAnharmonic_energy_order1_rate_note {a : ℝ} (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, gamma i = lam i ^ 2) (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3)
    (ha : a ^ 2 < 3) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (separableAnharmonic lam alpha gamma) t
          (separableAnharmonic lam alpha gamma) - (Fintype.card ι : ℝ) / 2 -
        (Fintype.card ι : ℝ) * (5 * a ^ 2 / 24 - 1 / 8) / t| ≤ K / (t * Real.sqrt t) := by
  have hg : ∀ i, 0 < gamma i := fun i => by rw [hgamma i]; exact pow_pos (hlam i) 2
  have hd : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i := fun i => by
    rw [halpha i, hgamma i]
    nlinarith [pow_pos (hlam i) 3]
  choose K T hK hT h using fun i =>
    energy_anharmonic_order1_rate_note (hlam i) (hgamma i) (halpha i) ha
  refine ⟨∑ i, K i, 1 + ∑ i, T i, Finset.sum_nonneg fun i _ => hK i,
    le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (zero_le_one.trans (hT i))),
    fun {t} ht => ?_⟩
  have hsum : 0 ≤ ∑ i, T i := Finset.sum_nonneg fun i _ => zero_le_one.trans (hT i)
  have hTi : ∀ i, T i ≤ t := fun i => by
    have := Finset.single_le_sum (f := T) (fun j _ => zero_le_one.trans (hT j)) (Finset.mem_univ i)
    linarith
  have htpos : 0 < t := by linarith
  rw [gibbsExpectation_energy_separableAnharmonic hlam hg hd htpos, Finset.mul_sum]
  have hsplit : ∑ i, t * _root_.Laplace.gibbsExpectation
        (anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) - (Fintype.card ι : ℝ) / 2 -
      (Fintype.card ι : ℝ) * (5 * a ^ 2 / 24 - 1 / 8) / t =
      ∑ i, (t * _root_.Laplace.gibbsExpectation (anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 -
        (5 * a ^ 2 / 24 - 1 / 8) / t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [hsplit]
  calc |∑ i, (t * _root_.Laplace.gibbsExpectation
          (anharmonicPotential (lam i) (alpha i) (gamma i)) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 - (5 * a ^ 2 / 24 - 1 / 8) / t)|
      ≤ ∑ i, |t * _root_.Laplace.gibbsExpectation
          (anharmonicPotential (lam i) (alpha i) (gamma i)) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 -
          (5 * a ^ 2 / 24 - 1 / 8) / t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, K i / (t * Real.sqrt t) := Finset.sum_le_sum fun i _ => h i (hTi i)
    _ = (∑ i, K i) / (t * Real.sqrt t) := by rw [Finset.sum_div]

/-- **E2's finite-`t` LLC in the note's frame**. -/
theorem rotatedAnharmonic_energy_order1_rate_note [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : Qᵀ * Q = 1) (c : ι → ℝ) {a : ℝ} (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, gamma i = lam i ^ 2) (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3)
    (ha : a ^ 2 < 3) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t
          (rotatedAnharmonic Q c lam alpha gamma) - (Fintype.card ι : ℝ) / 2 -
        (Fintype.card ι : ℝ) * (5 * a ^ 2 / 24 - 1 / 8) / t| ≤ K / (t * Real.sqrt t) := by
  obtain ⟨K, T, hK, hT, h⟩ := separableAnharmonic_energy_order1_rate_note hlam hgamma halpha ha
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  rw [gibbsExpectation_rotatedAnharmonic_self hQ c t]
  exact h ht

end SeparableEnergy

end Laplace.Multi
