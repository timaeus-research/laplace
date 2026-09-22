/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedLLCCoeff

/-!
# eq:mean's and eq:cov's `O(S²)` coefficients on E2's exact localised measure

Tides 67 and 68 certified the `O(S²)` remainders of eq:mean and eq:cov on the exact localised
rotated anharmonic measure without their coefficients; tides 72 and 73 gave the one-dimensional
second-order mean and second moment. This file identifies the coefficients: the localised
variance to second order (`v' = c₂' − c²`), the residual of the mean against the displayed
`P_t` (`r = c' − c'_S`), their transport to E2, and the observation that with the anchor at the
minimiser both coefficients are the *unlocalised* second-order ones — using `S = (tH + gI)⁻¹`
absorbs all localiser-dependent contributions through order `t⁻²` (structurally: at `x₀ = 0` the
localiser is the substitution `λ ↦ λ + g/t`, whose effect on the second-order coefficients is
`O(t⁻³)`).
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

/-! ### Coefficients -/

section Coeffs

variable {lam alpha gamma g x₀ : ℝ}

/-- `v' = c₂' − c²`: the `1/t` coefficient of `t·Var_loc`. -/
noncomputable def varLocCoeff2 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  locSecondCoeff2 lam alpha gamma g x₀ - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) ^ 2

theorem varLocCoeff2_eq (hlam : 0 < lam) :
    varLocCoeff2 lam alpha gamma g x₀ =
      alpha ^ 2 / lam ^ 4 - g * x₀ * alpha / lam ^ 3 - g / lam ^ 2 - gamma / (2 * lam ^ 3) := by
  unfold varLocCoeff2 locSecondCoeff2 locN2 locD1 locP₃
  field_simp
  ring

/-- `v' + g/λ²`: the `t⁻²` coefficient of `Var_loc − 1/(tλ + g)`, eq:cov's `O(S²)` term. -/
noncomputable def covLocCoeff2 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  varLocCoeff2 lam alpha gamma g x₀ + g / lam ^ 2

/-- eq:cov's `O(S²)` term is the unlocalised second-order variance coefficient minus `aα/λ³`. -/
theorem covLocCoeff2_eq (hlam : 0 < lam) :
    covLocCoeff2 lam alpha gamma g x₀ =
      (alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3)) - g * x₀ * alpha / lam ^ 3 := by
  unfold covLocCoeff2
  rw [varLocCoeff2_eq hlam]
  ring

theorem covLocCoeff2_anchor_zero (hlam : 0 < lam) :
    covLocCoeff2 lam alpha gamma g 0 = alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3) := by
  rw [covLocCoeff2_eq hlam]
  ring

/-- `c'_S = αg/λ³ − ag/λ²`: the `t⁻²` coefficient of the displayed `P_t`. -/
noncomputable def locLeadingCoeff2 (lam alpha g x₀ : ℝ) : ℝ :=
  alpha * g / lam ^ 3 - g * x₀ * g / lam ^ 2

/-- `r = c' − c'_S`: the `t⁻²` coefficient of `⟨x⟩_loc − P_t`, eq:mean's `O(S²)` term. -/
noncomputable def meanLocResidual2 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  meanLocCoeff2 lam alpha gamma g x₀ - locLeadingCoeff2 lam alpha g x₀

/-- `r = B₁ + aα²/λ⁴ − aγ/(2λ³) − αa²/(2λ³)`. -/
theorem meanLocResidual2_eq (hlam : 0 < lam) :
    meanLocResidual2 lam alpha gamma g x₀ =
      meanCoeff2 lam alpha gamma + g * x₀ * alpha ^ 2 / lam ^ 4 - g * x₀ * gamma / (2 * lam ^ 3) -
        alpha * (g * x₀) ^ 2 / (2 * lam ^ 3) := by
  unfold meanLocResidual2 locLeadingCoeff2 meanLocCoeff2 locN1 locD1 locP₃ locP₄
  field_simp
  ring

theorem meanLocResidual2_anchor_zero (hlam : 0 < lam) :
    meanLocResidual2 lam alpha gamma g 0 = meanCoeff2 lam alpha gamma := by
  rw [meanLocResidual2_eq hlam]
  ring

/-- The displayed `P_t = −αt/(2(tλ + g)²) + a/(tλ + g)` to second order:
`|P_t − c/t − c'_S/t²| ≤ K₀/t³`. -/
theorem locLeading_order2_sub_le (hlam : 0 < lam) (hg : 0 ≤ g) {t : ℝ} (ht : 1 ≤ t) :
    |locLeading lam alpha g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) / t -
        locLeadingCoeff2 lam alpha g x₀ / t ^ 2| ≤
      (|alpha| / 2 * ((3 * lam * g ^ 2 + 2 * g ^ 3) / lam ^ 5) + |g * x₀| * (g ^ 2 / lam ^ 3)) /
        t ^ 3 := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < t * lam + g := by positivity
  have e : locLeading lam alpha g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) / t -
      locLeadingCoeff2 lam alpha g x₀ / t ^ 2 =
      alpha / 2 * (-(3 * t * lam * g ^ 2 + 2 * g ^ 3) / ((t * lam + g) ^ 2 * lam ^ 3 * t ^ 2)) +
        g * x₀ * (g ^ 2 / ((t * lam + g) * lam ^ 2 * t ^ 2)) := by
    unfold locLeading locLeadingCoeff2
    field_simp
    ring
  have hsq : t ^ 2 * lam ^ 2 ≤ (t * lam + g) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ht0.le hlam.le) hg, sq_nonneg g]
  have hA : (3 * t * lam * g ^ 2 + 2 * g ^ 3) / ((t * lam + g) ^ 2 * lam ^ 3 * t ^ 2) ≤
      (3 * lam * g ^ 2 + 2 * g ^ 3) / lam ^ 5 / t ^ 3 := by
    have hnum : 3 * t * lam * g ^ 2 + 2 * g ^ 3 ≤ t * (3 * lam * g ^ 2 + 2 * g ^ 3) := by
      nlinarith [mul_nonneg (pow_nonneg hg 3) (sub_nonneg.2 ht)]
    have hden : lam ^ 5 * t ^ 4 ≤ (t * lam + g) ^ 2 * lam ^ 3 * t ^ 2 := by
      calc lam ^ 5 * t ^ 4 = t ^ 2 * lam ^ 2 * (lam ^ 3 * t ^ 2) := by ring
        _ ≤ (t * lam + g) ^ 2 * (lam ^ 3 * t ^ 2) := mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = (t * lam + g) ^ 2 * lam ^ 3 * t ^ 2 := by ring
    calc (3 * t * lam * g ^ 2 + 2 * g ^ 3) / ((t * lam + g) ^ 2 * lam ^ 3 * t ^ 2)
        ≤ t * (3 * lam * g ^ 2 + 2 * g ^ 3) / (lam ^ 5 * t ^ 4) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = (3 * lam * g ^ 2 + 2 * g ^ 3) / lam ^ 5 / t ^ 3 := by
          field_simp
  have hB : g ^ 2 / ((t * lam + g) * lam ^ 2 * t ^ 2) ≤ g ^ 2 / lam ^ 3 / t ^ 3 := by
    have hden : lam ^ 3 * t ^ 3 ≤ (t * lam + g) * lam ^ 2 * t ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hg (pow_nonneg hlam.le 2)) (pow_nonneg ht0.le 2)]
    calc g ^ 2 / ((t * lam + g) * lam ^ 2 * t ^ 2) ≤ g ^ 2 / (lam ^ 3 * t ^ 3) :=
          div_le_div_of_nonneg_left (sq_nonneg g) (by positivity) hden
      _ = g ^ 2 / lam ^ 3 / t ^ 3 := by rw [div_div]
  have hA' : |alpha / 2 * (-(3 * t * lam * g ^ 2 + 2 * g ^ 3) /
      ((t * lam + g) ^ 2 * lam ^ 3 * t ^ 2))| ≤
      |alpha| / 2 * ((3 * lam * g ^ 2 + 2 * g ^ 3) / lam ^ 5 / t ^ 3) := by
    rw [abs_mul, abs_div alpha, abs_two, abs_div (-(3 * t * lam * g ^ 2 + 2 * g ^ 3)), abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * t * lam * g ^ 2 + 2 * g ^ 3),
      abs_of_pos (by positivity : (0 : ℝ) < (t * lam + g) ^ 2 * lam ^ 3 * t ^ 2)]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have hB' : |g * x₀ * (g ^ 2 / ((t * lam + g) * lam ^ 2 * t ^ 2))| ≤
      |g * x₀| * (g ^ 2 / lam ^ 3 / t ^ 3) := by
    rw [abs_mul (g * x₀), abs_div, abs_of_nonneg (sq_nonneg g),
      abs_of_pos (by positivity : (0 : ℝ) < (t * lam + g) * lam ^ 2 * t ^ 2)]
    exact mul_le_mul_of_nonneg_left hB (abs_nonneg _)
  rw [e]
  calc _ ≤ _ + _ := abs_add_le _ _
    _ ≤ |alpha| / 2 * ((3 * lam * g ^ 2 + 2 * g ^ 3) / lam ^ 5 / t ^ 3) +
        |g * x₀| * (g ^ 2 / lam ^ 3 / t ^ 3) := add_le_add hA' hB'
    _ = _ := by ring

/-- `1/(λt) − 1/(tλ + g) − (g/λ²)/t² = −g²/(λ²t²(tλ + g))`, bounded by `g²/(λ³t³)`. -/
theorem displayed_var_remainder (hlam : 0 < lam) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |1 / (lam * t) - 1 / (t * lam + g) - g / lam ^ 2 / t ^ 2| ≤ g ^ 2 / lam ^ 3 / t ^ 3 := by
  have hd : 0 < t * lam + g := by positivity
  have e : 1 / (lam * t) - 1 / (t * lam + g) - g / lam ^ 2 / t ^ 2 =
      -(g ^ 2 / (lam ^ 2 * t ^ 2 * (t * lam + g))) := by
    field_simp
    ring
  rw [e, abs_neg, abs_of_nonneg (by positivity), div_div]
  apply div_le_div_of_nonneg_left (sq_nonneg g) (by positivity)
  nlinarith [mul_nonneg (mul_nonneg hg (pow_nonneg hlam.le 2)) (pow_nonneg ht.le 2)]

/-- The variance's assembly (abstract reals): from the second moment and the mean to second
order, `|t(M₂ − M₁²) − ℓ₀ − (c₂' − c²)/t| ≤ K/t²`. -/
theorem var_assembly (t M₂ M₁ ℓ₀ c c₂' c' K₂ K₁ : ℝ) (ht1 : 1 ≤ t) (hK₁ : 0 ≤ K₁)
    (e₂ : |t * M₂ - ℓ₀ - c₂' / t| ≤ K₂ / t ^ 2)
    (e₁ : |t * M₁ - c - c' / t| ≤ K₁ / t ^ 2) :
    |t * (M₂ - M₁ ^ 2) - ℓ₀ - (c₂' - c ^ 2) / t| ≤
      (K₂ + (|c'| + K₁) * (2 * |c| + |c'| + K₁)) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have key : t * (M₂ - M₁ ^ 2) - ℓ₀ - (c₂' - c ^ 2) / t =
      (t * M₂ - ℓ₀ - c₂' / t) - ((t * M₁ - c) * (t * M₁ + c)) / t := by
    field_simp
    ring
  have h1 : |t * M₁ - c| ≤ (|c'| + K₁) / t := by
    calc |t * M₁ - c| = |(t * M₁ - c - c' / t) + c' / t| := by ring_nf
      _ ≤ |t * M₁ - c - c' / t| + |c' / t| := abs_add_le _ _
      _ ≤ K₁ / t ^ 2 + |c'| / t := by
          gcongr
          rw [abs_div, abs_of_pos ht0]
      _ ≤ K₁ / t + |c'| / t := by
          gcongr
          nlinarith
      _ = (|c'| + K₁) / t := by ring
  have h2 : |t * M₁ + c| ≤ 2 * |c| + |c'| + K₁ := by
    calc |t * M₁ + c| = |(t * M₁ - c) + 2 * c| := by ring_nf
      _ ≤ |t * M₁ - c| + |2 * c| := abs_add_le _ _
      _ ≤ (|c'| + K₁) / t + 2 * |c| := by
          rw [abs_mul, abs_two]
          exact add_le_add h1 le_rfl
      _ ≤ (|c'| + K₁) + 2 * |c| := by
          gcongr
          exact div_le_self (by positivity) ht1
      _ = 2 * |c| + |c'| + K₁ := by ring
  have h3 : |((t * M₁ - c) * (t * M₁ + c)) / t| ≤
      (|c'| + K₁) * (2 * |c| + |c'| + K₁) / t ^ 2 := by
    rw [abs_div, abs_of_pos ht0, abs_mul]
    calc |t * M₁ - c| * |t * M₁ + c| / t
        ≤ ((|c'| + K₁) / t) * (2 * |c| + |c'| + K₁) / t := by gcongr
      _ = (|c'| + K₁) * (2 * |c| + |c'| + K₁) / t ^ 2 := by ring
  rw [key]
  calc _ ≤ _ + _ := abs_sub _ _
    _ ≤ K₂ / t ^ 2 + (|c'| + K₁) * (2 * |c| + |c'| + K₁) / t ^ 2 := add_le_add e₂ h3
    _ = _ := by ring

end Coeffs

/-! ### One-dimensional rates -/

section Rates

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- **The localised variance to second order (A)**: `|t·Var_loc − 1/λ − v'/t| ≤ K/t²`. -/
theorem localisedVar_order2_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * localisedVar lam alpha gamma g x₀ t - 1 / lam -
        varLocCoeff2 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locSecondMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := localisedMean_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K₂ + (|meanLocCoeff2 lam alpha gamma g x₀| + K₁) *
      (2 * |-alpha / (2 * lam ^ 2) + g * x₀ / lam| + |meanLocCoeff2 lam alpha gamma g x₀| + K₁),
    T₂ + T₁, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hV : localisedVar lam alpha gamma g x₀ t =
      _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2) -
        localisedMean lam alpha gamma g x₀ t ^ 2 := by
    rw [locSecondMoment_eq ht0]
    ring
  rw [hV]
  unfold varLocCoeff2
  exact var_assembly t _ _ (1 / lam) (-alpha / (2 * lam ^ 2) + g * x₀ / lam)
    (locSecondCoeff2 lam alpha gamma g x₀) (meanLocCoeff2 lam alpha gamma g x₀) K₂ K₁ ht1 hK₁
    (h₂ (t := t) (by linarith)) (h₁ (t := t) (by linarith))

/-- **eq:cov's `O(S²)` coefficient in one dimension**:
`|Var_loc − 1/(tλ + g) − (v' + g/λ²)/t²| ≤ K/t³`. -/
theorem localisedVar_sub_displayed_order2_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |localisedVar lam alpha gamma g x₀ t - 1 / (t * lam + g) -
        covLocCoeff2 lam alpha gamma g x₀ / t ^ 2| ≤ K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedVar_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K + g ^ 2 / lam ^ 3, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have e₁ := h ht
  have e₂ := displayed_var_remainder hlam hg ht0
  have key : localisedVar lam alpha gamma g x₀ t - 1 / (t * lam + g) -
      covLocCoeff2 lam alpha gamma g x₀ / t ^ 2 =
      (t * localisedVar lam alpha gamma g x₀ t - 1 / lam - varLocCoeff2 lam alpha gamma g x₀ / t) /
        t + (1 / (lam * t) - 1 / (t * lam + g) - g / lam ^ 2 / t ^ 2) := by
    unfold covLocCoeff2
    field_simp
    ring
  have h1 : |(t * localisedVar lam alpha gamma g x₀ t - 1 / lam -
      varLocCoeff2 lam alpha gamma g x₀ / t) / t| ≤ K / t ^ 3 := by
    rw [abs_div, abs_of_pos ht0]
    calc _ ≤ K / t ^ 2 / t := div_le_div_of_nonneg_right e₁ ht0.le
      _ = K / t ^ 3 := by ring
  rw [key]
  calc _ ≤ _ + _ := abs_add_le _ _
    _ ≤ K / t ^ 3 + g ^ 2 / lam ^ 3 / t ^ 3 := add_le_add h1 e₂
    _ = _ := by ring

/-- **eq:mean's `O(S²)` coefficient in one dimension (B)**: `|⟨x⟩_loc − P_t − r/t²| ≤ K/t³`. -/
theorem localisedMean_sub_locLeading_order2_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |localisedMean lam alpha gamma g x₀ t - locLeading lam alpha g x₀ t -
        meanLocResidual2 lam alpha gamma g x₀ / t ^ 2| ≤ K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedMean_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K + (|alpha| / 2 * ((3 * lam * g ^ 2 + 2 * g ^ 3) / lam ^ 5) +
    |g * x₀| * (g ^ 2 / lam ^ 3)), T, by positivity, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have e₁ := h ht
  have e₂ := locLeading_order2_sub_le (x₀ := x₀) hlam hg ht1 (alpha := alpha)
  have key : localisedMean lam alpha gamma g x₀ t - locLeading lam alpha g x₀ t -
      meanLocResidual2 lam alpha gamma g x₀ / t ^ 2 =
      (t * localisedMean lam alpha gamma g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) -
        meanLocCoeff2 lam alpha gamma g x₀ / t) / t -
      (locLeading lam alpha g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) / t -
        locLeadingCoeff2 lam alpha g x₀ / t ^ 2) := by
    unfold meanLocResidual2
    field_simp
    ring
  have h1 : |(t * localisedMean lam alpha gamma g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) -
      meanLocCoeff2 lam alpha gamma g x₀ / t) / t| ≤ K / t ^ 3 := by
    rw [abs_div, abs_of_pos ht0]
    calc _ ≤ K / t ^ 2 / t := div_le_div_of_nonneg_right e₁ ht0.le
      _ = K / t ^ 3 := by ring
  rw [key]
  calc _ ≤ _ + _ := abs_sub _ _
    _ ≤ K / t ^ 3 + (|alpha| / 2 * ((3 * lam * g ^ 2 + 2 * g ^ 3) / lam ^ 5) +
        |g * x₀| * (g ^ 2 / lam ^ 3)) / t ^ 3 := add_le_add h1 e₂
    _ = _ := by ring

end Rates

/-! ### E2: the rotated separable oscillator with the isotropic localiser -/

section Multi

open Matrix

/-- Finite sums of `K/t³` rates. -/
theorem sum_rate_div_cube {κ : Type*} [Fintype κ] (a : κ → ℝ) (e : κ → ℝ → ℝ)
    (h : ∀ i, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |e i t| ≤ K / t ^ 3) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |∑ i, a i * e i t| ≤ K / t ^ 3 := by
  choose K T hK hT h using h
  have hT0 : ∀ i, 0 ≤ T i := fun i => zero_le_one.trans (hT i)
  refine ⟨∑ i, |a i| * K i, 1 + ∑ i, T i,
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hK i),
    le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hT0 i), fun {t} ht => ?_⟩
  have hTi : ∀ i, T i ≤ t := fun i =>
    (Finset.single_le_sum (fun i _ => hT0 i) (Finset.mem_univ i)).trans
      ((le_add_of_nonneg_left zero_le_one).trans ht)
  calc |∑ i, a i * e i t| ≤ ∑ i, |a i * e i t| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |e i t| := by simp only [abs_mul]
    _ ≤ ∑ i, |a i| * (K i / t ^ 3) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i (hTi i)) (abs_nonneg _)
    _ = (∑ i, |a i| * K i) / t ^ 3 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- **eq:mean's `O(S²)` coefficient on E2's exact localised measure**: for every ambient `j`,
`|(⟨w⟩_loc − c − meanShiftLoc − g(tH + gI)⁻¹(w₀ − c))ⱼ − (∑ᵢ Qⱼᵢ rᵢ)/t²| ≤ K/t³`,
`rᵢ = meanLocResidual2` of the `i`-th frame oscillator with anchor `(Qᵀ(w₀ − c))ᵢ`. -/
theorem localisedRotatedAnharmonic_displayed_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j) -
        c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j -
        (∑ i, Q j i * meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) /
          t ^ 2| ≤ K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_cube (fun i => Q j i)
    (fun i t => localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) t -
      meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t ^ 2)
    (fun i => localisedMean_sub_locLeading_order2_rate (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => w j) - c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j -
        (∑ i, Q j i * meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) /
          t ^ 2 =
      ∑ i, Q j i * (localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
        locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) t -
        meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t ^ 2) := by
    rw [localisedRotatedAnharmonic_ambient_coord hQ c w₀ hlam hgamma hdisc hg ht0 j,
      displayed_mean_rot hQ hlam hg ht0 alpha c w₀, Finset.sum_div]
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, mul_div_assoc]
    ring
  rw [key]
  exact h ht

/-- **eq:cov's `O(S²)` coefficient on E2's exact localised measure**: for all ambient `j, k`,
`|Cov_loc[wⱼ, wₖ] − ((tH + gI)⁻¹)ⱼₖ − (∑ᵢ QⱼᵢQₖᵢ (v'ᵢ + g/λᵢ²))/t²| ≤ K/t³`. -/
theorem localisedRotatedAnharmonic_cov_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (j k : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
          (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k -
        (∑ i, Q j i * Q k i * covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) /
          t ^ 2| ≤ K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_cube (fun i => Q j i * Q k i)
    (fun i t => localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      1 / (t * lam i + g) -
      covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t ^ 2)
    (fun i => localisedVar_sub_displayed_order2_rate (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
        (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k -
        (∑ i, Q j i * Q k i * covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) /
          t ^ 2 =
      ∑ i, Q j i * Q k i * (localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
        1 / (t * lam i + g) -
        covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t ^ 2) := by
    rw [localisedRotatedAnharmonic_cov_coord hQ c w₀ hlam hgamma hdisc hg ht0 j k,
      locS_rot_apply hQ hlam hg ht0 j k, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  exact h ht

/-- The frame coordinates of the centre vanish. -/
theorem affineFrame_self (Q : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) (i : Fin d) :
    affineFrame Q c c i = 0 := by
  simp [affineFrame]

/-- **The anchor at the minimiser (D, mean)**: with `w₀ = c`, eq:mean's `O(S²)` coefficient is the
unlocalised one, `∑ᵢ Qⱼᵢ B₁,ᵢ`, independent of `g`. -/
theorem localisedRotatedAnharmonic_displayed_order2_rate_anchor (hQ : Qᵀ * Q = 1)
    (c : Fin d → ℝ) (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g c t) t (fun w => w j) -
        c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (c - c))) j -
        (∑ i, Q j i * meanCoeff2 (lam i) (alpha i) (gamma i)) / t ^ 2| ≤ K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ :=
    localisedRotatedAnharmonic_displayed_order2_rate hQ c c hlam hgamma hdisc hg j
  have e : ∀ i, meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c c i) =
      meanCoeff2 (lam i) (alpha i) (gamma i) := fun i => by
    rw [affineFrame_self, meanLocResidual2_anchor_zero (hlam i)]
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have := h ht
  simp only [e] at this
  exact this

/-- **The anchor at the minimiser (D, covariance)**: with `w₀ = c`, eq:cov's `O(S²)` coefficient is
the unlocalised one, `∑ᵢ QⱼᵢQₖᵢ (αᵢ²/λᵢ⁴ − γᵢ/(2λᵢ³))`, independent of `g`. -/
theorem localisedRotatedAnharmonic_cov_order2_rate_anchor (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (j k : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g c t) t (fun w => w j)
          (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k -
        (∑ i, Q j i * Q k i * (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3))) / t ^ 2| ≤
        K / t ^ 3 := by
  obtain ⟨K, T, hK, hT, h⟩ :=
    localisedRotatedAnharmonic_cov_order2_rate hQ c c hlam hgamma hdisc hg j k
  have e : ∀ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c c i) =
      alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3) := fun i => by
    rw [affineFrame_self, covLocCoeff2_anchor_zero (hlam i)]
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have := h ht
  simp only [e] at this
  exact this

end Multi

end Laplace.Multi
