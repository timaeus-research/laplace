/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedMeanEuclid

/-!
# The localised energy: the invariant anchor correction and the LLC as a fluctuation coefficient

On E2's exact localised measure (`S = (tH + gI)⁻¹`, `δ = w₀ − c` the anchor displacement,
`m₁ = Q(−αᵢ/(2λᵢ²))` the unlocalised first-order mean shift, `E₁ = ∑ᵢ energyCoeff1ᵢ`):

* the discrepancy of the scaled energy `t⟨L∘A⟩_loc` from the Gaussian trace prediction
  `½tr(tHS)` has the invariant `1/t` coefficient `E₁ + (g²/2)⟨δ, H⁻¹δ⟩ + g⟨δ, m₁⟩` — the unlocalised
  anharmonic correction, the anchored Gaussian's squared-mean energy (omitted by the trace-only
  predictor) and the anchor/mean-shift coupling; at the matched anchor it is `E₁`;
* exactly `∂ₜ⟨L∘A⟩_loc = −Var_loc(L∘A)`, and `t² Var_loc(L∘A) = d/2 + O(1/t)`: the same LLC `d/2`
  governs the leading energy fluctuation and the temperature response,
  `−∂ₜ⟨L∘A⟩_loc = Var_loc(L∘A) = d/(2t²) + O(t⁻³)`;
* the squared discrepancy `t⁴(⟨L∘A⟩_loc − ½tr(HS))² → (∑ᵢ (e₁ᵢ + g/(2λᵢ)))²`.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section OneD

variable {lam alpha gamma g x₀ : ℝ} (hlam : 0 < lam) (hgamma : 0 < gamma)
  (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `|t³ ⟨x⁸ φ⟩| ≤ K` eventually (weighted eighth moment). -/
theorem locEighth_bound (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 8 * locWeight g x₀ x)| ≤ K := by
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  simp only [show (2 * 4 : ℕ) = 8 from rfl] at h₈
  refine ⟨Real.exp (g * x₀ ^ 2 / 2) * C₈, T₈, by positivity, hT₈, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT₈.trans ht
  have ht0 : 0 < t := by linarith
  have hZ := partition_pos' hlam hgamma hdisc ht0
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht0
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht0 (x₀ := x₀) 8
  have hG : Integrable (fun x => (Real.exp (g * x₀ ^ 2 / 2) * x ^ 8) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    ((hp 8).const_mul _).congr (Eventually.of_forall fun x => by dsimp only; ring)
  have hmono : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => |x ^ 8 * locWeight g x₀ x|) ≤
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => Real.exp (g * x₀ ^ 2 / 2) * x ^ 8) := by
    refine gibbsExpectation_mono' hZ (integrable_abs_weighted hf) hG fun x => ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 8),
      abs_of_pos (locWeight_pos x), mul_comm]
    exact mul_le_mul_of_nonneg_right (locWeight_le hg x) (by positivity)
  rw [gibbsExpectation_const_mul₁] at hmono
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 3)]
  calc t ^ 3 * |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 8 * locWeight g x₀ x)|
      ≤ t ^ 3 * (Real.exp (g * x₀ ^ 2 / 2) *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ 8)) :=
        mul_le_mul_of_nonneg_left ((abs_gibbsExpectation_le' hZ _).trans hmono) (by positivity)
    _ ≤ t ^ 3 * (Real.exp (g * x₀ ^ 2 / 2) * (C₈ / t ^ 4)) := by
        gcongr
        exact h₈ (t := t) ht
    _ = Real.exp (g * x₀ ^ 2 / 2) * C₈ / t := by
        field_simp
    _ ≤ Real.exp (g * x₀ ^ 2 / 2) * C₈ := div_le_self (by positivity) ht1

/-- `|t³ ⟨x⁷ φ⟩| ≤ K` eventually, via `|x|⁷ ≤ (x⁶ + x⁸)/2`. -/
theorem locSeventh_bound (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 7 * locWeight g x₀ x)| ≤ K := by
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  simp only [show (2 * 3 : ℕ) = 6 from rfl] at h₆
  simp only [show (2 * 4 : ℕ) = 8 from rfl] at h₈
  refine ⟨Real.exp (g * x₀ ^ 2 / 2) * ((C₆ + C₈) / 2), T₆ + T₈, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hZ := partition_pos' hlam hgamma hdisc ht0
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht0
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht0 (x₀ := x₀) 7
  have hG : Integrable (fun x => (Real.exp (g * x₀ ^ 2 / 2) * ((x ^ 6 + x ^ 8) / 2)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    (((hp 6).add (hp 8)).const_mul (Real.exp (g * x₀ ^ 2 / 2) / 2)).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h7 : ∀ x : ℝ, |x| ^ 7 ≤ (x ^ 6 + x ^ 8) / 2 := fun x => by
    have h6 : |x| ^ 6 = x ^ 6 := Even.pow_abs (by decide) x
    have h8 : |x| ^ 8 = x ^ 8 := Even.pow_abs (by decide) x
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg x) 6) (sq_nonneg (|x| - 1))]
  have hmono : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => |x ^ 7 * locWeight g x₀ x|) ≤
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => Real.exp (g * x₀ ^ 2 / 2) * ((x ^ 6 + x ^ 8) / 2)) := by
    refine gibbsExpectation_mono' hZ (integrable_abs_weighted hf) hG fun x => ?_
    rw [abs_mul, abs_of_pos (locWeight_pos x), abs_pow, mul_comm]
    exact mul_le_mul (locWeight_le hg x) (h7 x) (by positivity) (by positivity)
  rw [gibbsExpectation_const_mul₁] at hmono
  have hsplit : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => (x ^ 6 + x ^ 8) / 2) =
      1 / 2 * (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 6) +
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 8)) := by
    rw [← _root_.Laplace.gibbsExpectation_add _ _ _ _ (hp 6) (hp 8),
      ← _root_.Laplace.gibbsExpectation_smul]
    congr 1
    funext x
    ring
  rw [hsplit] at hmono
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 3)]
  calc t ^ 3 * |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 7 * locWeight g x₀ x)|
      ≤ t ^ 3 * (Real.exp (g * x₀ ^ 2 / 2) * (1 / 2 *
          (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ 6) +
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ 8)))) :=
        mul_le_mul_of_nonneg_left ((abs_gibbsExpectation_le' hZ _).trans hmono) (by positivity)
    _ ≤ t ^ 3 * (Real.exp (g * x₀ ^ 2 / 2) * (1 / 2 * (C₆ / t ^ 3 + C₈ / t ^ 4))) := by
        gcongr
        · exact h₆ (t := t) (by linarith)
        · exact h₈ (t := t) (by linarith)
    _ = Real.exp (g * x₀ ^ 2 / 2) * ((C₆ + C₈ / t) / 2) := by
        field_simp
    _ ≤ Real.exp (g * x₀ ^ 2 / 2) * ((C₆ + C₈) / 2) := by
        gcongr
        exact div_le_self hC₈ ht1

theorem locSeventh_loc_bound (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 7)| ≤ K :=
  loc_ratio_bounded hlam hgamma hdisc (fun x => x ^ 7) hg (locSeventh_bound hlam hgamma hdisc hg)

theorem locEighth_loc_bound (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 8)| ≤ K :=
  loc_ratio_bounded hlam hgamma hdisc (fun x => x ^ 8) hg (locEighth_bound hlam hgamma hdisc hg)

/-- `⟨ℓ²⟩_loc` as a combination of the localised moments of degrees `4` to `8`. -/
theorem locEnergySq_eq (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) =
      lam ^ 2 / 4 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 4) +
        (lam * alpha / 6 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 5) +
        ((lam * gamma / 24 + alpha ^ 2 / 36) *
          _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
            (fun x => x ^ 6) +
        (alpha * gamma / 72 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t)
          t (fun x => x ^ 7) +
        gamma ^ 2 / 576 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 8)))) := by
  have hp : ∀ m, Integrable (fun x : ℝ => x ^ m *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    integrable_pow_locPotential1 hlam hgamma hdisc hg ht
  have hc : ∀ (a : ℝ) (m : ℕ), Integrable (fun x : ℝ => a * x ^ m *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := fun a m =>
    ((hp m).const_mul a).congr (Eventually.of_forall fun x => by ring)
  have h78 : Integrable (fun x : ℝ => (alpha * gamma / 72 * x ^ 7 + gamma ^ 2 / 576 * x ^ 8) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (alpha * gamma / 72) 7).add (hc (gamma ^ 2 / 576) 8)).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h678 : Integrable (fun x : ℝ => ((lam * gamma / 24 + alpha ^ 2 / 36) * x ^ 6 +
      (alpha * gamma / 72 * x ^ 7 + gamma ^ 2 / 576 * x ^ 8)) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (lam * gamma / 24 + alpha ^ 2 / 36) 6).add h78).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h5678 : Integrable (fun x : ℝ => (lam * alpha / 6 * x ^ 5 +
      ((lam * gamma / 24 + alpha ^ 2 / 36) * x ^ 6 +
      (alpha * gamma / 72 * x ^ 7 + gamma ^ 2 / 576 * x ^ 8))) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (lam * alpha / 6) 5).add h678).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have e : (fun x =>
      anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) =
      fun x => lam ^ 2 / 4 * x ^ 4 + (lam * alpha / 6 * x ^ 5 +
        ((lam * gamma / 24 + alpha ^ 2 / 36) * x ^ 6 +
        (alpha * gamma / 72 * x ^ 7 + gamma ^ 2 / 576 * x ^ 8))) := by
    funext x
    simp only [anharmonicPotential]
    ring
  rw [e, _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam ^ 2 / 4) 4) h5678,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam * alpha / 6) 5) h678,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam * gamma / 24 + alpha ^ 2 / 36) 6) h78,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (alpha * gamma / 72) 7)
      (hc (gamma ^ 2 / 576) 8),
    _root_.Laplace.gibbsExpectation_smul, _root_.Laplace.gibbsExpectation_smul,
    _root_.Laplace.gibbsExpectation_smul, _root_.Laplace.gibbsExpectation_smul,
    _root_.Laplace.gibbsExpectation_smul]

omit hlam hgamma hdisc in
/-- Assembly: `|t²⟨ℓ²⟩_loc − 3/4| ≤ K/t` from the moment rates. -/
theorem energySq_assembly (lam alpha gamma t M₄ M₅ M₆ M₇ M₈ K₄ K₅ K₆ K₇ K₈ : ℝ)
    (hlam : 0 < lam) (ht1 : 1 ≤ t) (e₄ : |t ^ 2 * M₄ - 3 / lam ^ 2| ≤ K₄ / t)
    (e₅ : |t ^ 3 * M₅| ≤ K₅)
    (e₆ : |t ^ 3 * M₆| ≤ K₆) (e₇ : |t ^ 3 * M₇| ≤ K₇) (e₈ : |t ^ 3 * M₈| ≤ K₈) :
    |t ^ 2 * (lam ^ 2 / 4 * M₄ + (lam * alpha / 6 * M₅ +
        ((lam * gamma / 24 + alpha ^ 2 / 36) * M₆ +
        (alpha * gamma / 72 * M₇ + gamma ^ 2 / 576 * M₈)))) - 3 / 4| ≤
      (lam ^ 2 / 4 * K₄ + (|lam * alpha / 6| * K₅ + (|lam * gamma / 24 + alpha ^ 2 / 36| * K₆ +
        (|alpha * gamma / 72| * K₇ + |gamma ^ 2 / 576| * K₈)))) / t := by
  have ht0 : 0 < t := by linarith
  have hl : lam ≠ 0 := hlam.ne'
  have key : t ^ 2 * (lam ^ 2 / 4 * M₄ + (lam * alpha / 6 * M₅ +
      ((lam * gamma / 24 + alpha ^ 2 / 36) * M₆ +
      (alpha * gamma / 72 * M₇ + gamma ^ 2 / 576 * M₈)))) - 3 / 4 =
      lam ^ 2 / 4 * (t ^ 2 * M₄ - 3 / lam ^ 2) + (lam * alpha / 6 * (t ^ 3 * M₅) +
        ((lam * gamma / 24 + alpha ^ 2 / 36) * (t ^ 3 * M₆) +
        (alpha * gamma / 72 * (t ^ 3 * M₇) + gamma ^ 2 / 576 * (t ^ 3 * M₈)))) / t := by
    field_simp
    ring
  rw [key]
  have h4 : |lam ^ 2 / 4 * (t ^ 2 * M₄ - 3 / lam ^ 2)| ≤ lam ^ 2 / 4 * (K₄ / t) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam ^ 2 / 4)]
    exact mul_le_mul_of_nonneg_left e₄ (by positivity)
  have h5 : |lam * alpha / 6 * (t ^ 3 * M₅)| ≤ |lam * alpha / 6| * K₅ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e₅ (abs_nonneg _)
  have h6 : |(lam * gamma / 24 + alpha ^ 2 / 36) * (t ^ 3 * M₆)| ≤
      |lam * gamma / 24 + alpha ^ 2 / 36| * K₆ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e₆ (abs_nonneg _)
  have h7 : |alpha * gamma / 72 * (t ^ 3 * M₇)| ≤ |alpha * gamma / 72| * K₇ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e₇ (abs_nonneg _)
  have h8 : |gamma ^ 2 / 576 * (t ^ 3 * M₈)| ≤ |gamma ^ 2 / 576| * K₈ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e₈ (abs_nonneg _)
  have hrest : |lam * alpha / 6 * (t ^ 3 * M₅) +
      ((lam * gamma / 24 + alpha ^ 2 / 36) * (t ^ 3 * M₆) +
      (alpha * gamma / 72 * (t ^ 3 * M₇) + gamma ^ 2 / 576 * (t ^ 3 * M₈)))| ≤
      |lam * alpha / 6| * K₅ + (|lam * gamma / 24 + alpha ^ 2 / 36| * K₆ +
        (|alpha * gamma / 72| * K₇ + |gamma ^ 2 / 576| * K₈)) :=
    (abs_add_le _ _).trans (add_le_add h5 ((abs_add_le _ _).trans (add_le_add h6
      ((abs_add_le _ _).trans (add_le_add h7 h8)))))
  calc |lam ^ 2 / 4 * (t ^ 2 * M₄ - 3 / lam ^ 2) + (lam * alpha / 6 * (t ^ 3 * M₅) +
        ((lam * gamma / 24 + alpha ^ 2 / 36) * (t ^ 3 * M₆) +
        (alpha * gamma / 72 * (t ^ 3 * M₇) + gamma ^ 2 / 576 * (t ^ 3 * M₈)))) / t|
      ≤ |lam ^ 2 / 4 * (t ^ 2 * M₄ - 3 / lam ^ 2)| + |lam * alpha / 6 * (t ^ 3 * M₅) +
        ((lam * gamma / 24 + alpha ^ 2 / 36) * (t ^ 3 * M₆) +
        (alpha * gamma / 72 * (t ^ 3 * M₇) + gamma ^ 2 / 576 * (t ^ 3 * M₈)))| / t := by
        rw [← abs_of_pos ht0, ← abs_div, abs_of_pos ht0]
        exact abs_add_le _ _
    _ ≤ lam ^ 2 / 4 * (K₄ / t) + (|lam * alpha / 6| * K₅ +
        (|lam * gamma / 24 + alpha ^ 2 / 36| * K₆ +
        (|alpha * gamma / 72| * K₇ + |gamma ^ 2 / 576| * K₈))) / t := by gcongr
    _ = _ := by ring

/-- **The leading localised energy second moment**: `|t²⟨ℓ²⟩_loc − 3/4| ≤ K/t`. -/
theorem locEnergySq_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) -
        3 / 4| ≤ K / t := by
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := locFifth_loc_bound hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := locSixth_loc_bound hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₇, T₇, hK₇, hT₇, h₇⟩ := locSeventh_loc_bound hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₈, T₈, hK₈, hT₈, h₈⟩ := locEighth_loc_bound hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨lam ^ 2 / 4 * K₄ + (|lam * alpha / 6| * K₅ + (|lam * gamma / 24 + alpha ^ 2 / 36| * K₆ +
    (|alpha * gamma / 72| * K₇ + |gamma ^ 2 / 576| * K₈))), T₄ + T₅ + T₆ + T₇ + T₈, by positivity,
    by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [locEnergySq_eq hlam hgamma hdisc hg ht0]
  exact energySq_assembly lam alpha gamma t _ _ _ _ _ K₄ K₅ K₆ K₇ K₈ hlam ht1
    (h₄ (t := t) (by linarith)) (h₅ (t := t) (by linarith)) (h₆ (t := t) (by linarith))
    (h₇ (t := t) (by linarith)) (h₈ (t := t) (by linarith))

/-- **The leading localised energy variance**: `|t² Var_loc(ℓ) − ½| ≤ K/t`. -/
theorem locEnergyVar_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (anharmonicPotential lam alpha gamma) - 1 / 2| ≤
        K / t := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locEnergySq_leading hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := localisedEnergy_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K₂ + (2 * |(1 : ℝ) / 2| * (|energyLocCoeff1 lam alpha gamma g x₀| + K₁) +
    (|energyLocCoeff1 lam alpha gamma g x₀| + K₁) ^ 2), T₂ + T₁, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hE : |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
      (anharmonicPotential lam alpha gamma) - 1 / 2| ≤
      (|energyLocCoeff1 lam alpha gamma g x₀| + K₁) / t := by
    have h := h₁ (t := t) (by linarith)
    have e : t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) - 1 / 2 =
        (t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) - 1 / 2 -
          energyLocCoeff1 lam alpha gamma g x₀ / t) +
        energyLocCoeff1 lam alpha gamma g x₀ / t := by ring
    have hK : K₁ / t ^ 2 ≤ K₁ / t :=
      div_le_div_of_nonneg_left hK₁ ht0 (by nlinarith)
    rw [e]
    calc _ ≤ |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) - 1 / 2 -
          energyLocCoeff1 lam alpha gamma g x₀ / t| +
          |energyLocCoeff1 lam alpha gamma g x₀ / t| := abs_add_le _ _
      _ ≤ K₁ / t + |energyLocCoeff1 lam alpha gamma g x₀| / t := by
          rw [abs_div, abs_of_pos ht0]
          exact add_le_add (h.trans hK) le_rfl
      _ = (|energyLocCoeff1 lam alpha gamma g x₀| + K₁) / t := by ring
  have hsq := sq_rate ht1 (by positivity) hE
  unfold _root_.Laplace.gibbsCov
  have key : t ^ 2 * (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
      (fun x => anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) -
      _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) *
      _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma)) - 1 / 2 =
      (t ^ 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) -
        3 / 4) -
      ((t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma)) ^ 2 - (1 / 2) ^ 2) := by ring
  rw [key, add_div]
  exact (abs_sub _ _).trans (add_le_add (h₂ (t := t) (by linarith)) hsq)

end OneD

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- `∑ᵢ aᵢ²/(2λᵢ) = (g²/2)⟨w₀ − c, H⁻¹(w₀ − c)⟩`, `aᵢ = g u₀ᵢ`. -/
theorem sum_anchor_sq_div_eq (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (c w₀ : Fin d → ℝ) :
    ∑ i, (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i) =
      g ^ 2 / 2 * ((w₀ - c) ⬝ᵥ ((Q * diagonal (fun i => 1 / lam i) * Qᵀ) *ᵥ (w₀ - c))) := by
  rw [sub_eq_mulVec_affineFrame hQ c w₀, conj_mulVec_mulVec hQ, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hQ, Matrix.vecMul_one]
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (hlam i).ne'
  field_simp

/-- `−∑ᵢ aᵢαᵢ/(2λᵢ²) = g⟨w₀ − c, m₁⟩`, `m₁ = Q(−α/(2λ²))` the unlocalised first-order mean shift. -/
theorem sum_anchor_alpha_eq (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) :
    -∑ i, g * affineFrame Q c w₀ i * alpha i / (2 * lam i ^ 2) =
      g * ((w₀ - c) ⬝ᵥ (Q *ᵥ fun i => -alpha i / (2 * lam i ^ 2))) := by
  rw [sub_eq_mulVec_affineFrame hQ c w₀, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, hQ, Matrix.vecMul_one]
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `|t·x − C/t| ≤ K/t² ⟹ |t²x − C| ≤ K/t`. -/
theorem scaled_sq_from_rate {t x C K : ℝ} (ht : 0 < t) (h : |t * x - C / t| ≤ K / t ^ 2) :
    |t ^ 2 * x - C| ≤ K / t := by
  have ht' : t ≠ 0 := ht.ne'
  have e : t ^ 2 * x - C = t * (t * x - C / t) := by
    field_simp
  rw [e, abs_mul, abs_of_pos ht]
  calc t * |t * x - C / t| ≤ t * (K / t ^ 2) := by gcongr
    _ = K / t := by field_simp

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-! ### A. The invariant anchor correction -/

/-- **The energy's discrepancy from the Gaussian trace prediction, invariantly**:
`|t⟨L∘A⟩_loc − ½tr(tHS) − (E₁ + (g²/2)⟨w₀ − c, H⁻¹(w₀ − c)⟩ + g⟨w₀ − c, m₁⟩)/t| ≤ K/t²`. -/
theorem localisedRotatedAnharmonic_llc_sub_trace_invariant (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) -
        1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace -
        (∑ i, energyCoeff1 (lam i) (alpha i) (gamma i) +
          g ^ 2 / 2 * ((w₀ - c) ⬝ᵥ ((Q * diagonal (fun i => 1 / lam i) * Qᵀ) *ᵥ (w₀ - c))) +
          g * ((w₀ - c) ⬝ᵥ (Q *ᵥ fun i => -alpha i / (2 * lam i ^ 2)))) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ :=
    localisedRotatedAnharmonic_llc_sub_trace_rate hQ c w₀ hlam hgamma hdisc hg
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have e : ∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
      g / (2 * lam i)) =
      ∑ i, energyCoeff1 (lam i) (alpha i) (gamma i) +
        g ^ 2 / 2 * ((w₀ - c) ⬝ᵥ ((Q * diagonal (fun i => 1 / lam i) * Qᵀ) *ᵥ (w₀ - c))) +
        g * ((w₀ - c) ⬝ᵥ (Q *ᵥ fun i => -alpha i / (2 * lam i ^ 2))) := by
    rw [← sum_anchor_sq_div_eq hQ hlam c w₀, ← sum_anchor_alpha_eq hQ c w₀,
      ← Finset.sum_add_distrib, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => energyLocCoeff1_add_eq _ _ _ _ _ (hlam i)
  rw [← e]
  exact h ht

/-- **Matched anchor** `w₀ = c`: the coefficient reduces to the unlocalised `E₁`. -/
theorem localisedRotatedAnharmonic_llc_sub_trace_matched (hQ : Qᵀ * Q = 1) (c : Fin d → ℝ)
    (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g c t) t
          (rotatedAnharmonic Q c lam alpha gamma) -
        1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace -
        (∑ i, energyCoeff1 (lam i) (alpha i) (gamma i)) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ :=
    localisedRotatedAnharmonic_llc_sub_trace_invariant hlam hgamma hdisc hQ c c hg
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have := h ht
  rwa [sub_self, zero_dotProduct, zero_dotProduct, mul_zero, mul_zero, add_zero, add_zero] at this

/-! ### C. The squared discrepancy -/

/-- `|t⁴ (⟨L∘A⟩_loc − ½tr(HS))² − (∑ᵢ (e₁ᵢ + g/(2λᵢ)))²| ≤ K/t`. -/
theorem localisedRotatedAnharmonic_llc_sub_trace_sq_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) -
          1 / 2 * ((Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace) ^ 2 -
        (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
          g / (2 * lam i))) ^ 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ :=
    localisedRotatedAnharmonic_llc_sub_trace_rate hQ c w₀ hlam hgamma hdisc hg
  refine ⟨2 * |∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
    g / (2 * lam i))| * K + K ^ 2, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have htr : 1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace =
      t * (1 / 2 * ((Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace) := by
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    ring
  have h1 := h ht
  rw [htr] at h1
  have h2 : |t * (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) -
      1 / 2 * ((Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace) -
      (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
        g / (2 * lam i))) / t| ≤ K / t ^ 2 := by
    convert h1 using 2
    ring
  have h3 := scaled_sq_from_rate ht0 h2
  have e : t ^ 4 * (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) -
      1 / 2 * ((Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace) ^ 2 =
      (t ^ 2 * (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) -
      1 / 2 * ((Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace)) ^ 2 := by ring
  rw [e]
  exact sq_rate ht1 hK h3

/-! ### B. The LLC as the leading fluctuation coefficient -/

/-- `Var_loc(L∘A) = ∑ᵢ Var_loc,ᵢ(ℓᵢ)`: the frame family is a product measure. -/
theorem localisedVar_energy_eq_sum (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) =
      ∑ i, _root_.Laplace.gibbsCov
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i))
        (anharmonicPotential (lam i) (alpha i) (gamma i)) := by
  have e : gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) =
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (rotated Q c (separableAnharmonic lam alpha gamma)) := rfl
  rw [e, localisedRotated_gibbsCov_eq hQ c w₀ t (continuous_separableAnharmonic lam alpha gamma)]
  have hℓ : ∀ k, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) := integrable_energy_locFamily hlam hgamma hdisc hg (affineFrame Q c w₀) ht
  have hℓℓ : ∀ k l, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      anharmonicPotential (lam l) (alpha l) (gamma l) (u l) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) := fun k l => by
    have h2 := integrable_energy_pow_locFamily hlam hgamma hdisc hg (affineFrame Q c w₀) ht k l 2
    have h3 := integrable_energy_pow_locFamily hlam hgamma hdisc hg (affineFrame Q c w₀) ht k l 3
    have h4 := integrable_energy_pow_locFamily hlam hgamma hdisc hg (affineFrame Q c w₀) ht k l 4
    refine (((h2.const_mul (lam l / 2)).add (h3.const_mul (alpha l / 6))).add
      (h4.const_mul (gamma l / 24))).congr (Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply, anharmonicPotential]
    ring
  have hℓE : ∀ k, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      (∑ l, anharmonicPotential (lam l) (alpha l) (gamma l) (u l)) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) := fun k => by
    refine (integrable_finsetSum Finset.univ fun l _ => hℓℓ k l).congr
      (Eventually.of_forall fun u => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul]
  have hZ : ∀ m, _root_.Laplace.partitionFunction
      (locFamily lam alpha gamma g (affineFrame Q c w₀) t m) t ≠ 0 :=
    partitionFunction_locFamily_ne hlam hgamma hdisc hg (affineFrame Q c w₀) ht
  rw [separableAnharmonic_eq_sum,
    gibbsCov_finsetSum_left _ t Finset.univ _ _ (fun k _ => hℓ k) (fun k _ => hℓE k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gibbsCov_comm, gibbsCov_finsetSum_left _ t Finset.univ _ _ (fun l _ => hℓ l)
    (fun l _ => hℓℓ l k)]
  simp only [gibbsCov_coord_fun_separable (locFamily lam alpha gamma g (affineFrame Q c w₀) t) t hZ,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- **The leading localised energy variance**: `|t² Var_loc(L∘A) − d/2| ≤ K/t`. -/
theorem localisedVar_energy_leading (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) -
        (d : ℝ) / 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div (fun _ : Fin d => (1 : ℝ))
    (fun i t => t ^ 2 * _root_.Laplace.gibbsCov
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
      (anharmonicPotential (lam i) (alpha i) (gamma i))
      (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2)
    (fun i => locEnergyVar_leading (hlam i) (hgamma i) (hdisc i) hg (x₀ := affineFrame Q c w₀ i))
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedVar_energy_eq_sum hlam hgamma hdisc hQ c w₀ hg ht0]
  have key : t ^ 2 * ∑ i, _root_.Laplace.gibbsCov
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
      (anharmonicPotential (lam i) (alpha i) (gamma i))
      (anharmonicPotential (lam i) (alpha i) (gamma i)) - (d : ℝ) / 2 =
      ∑ i, (1 : ℝ) * (t ^ 2 * _root_.Laplace.gibbsCov
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i))
        (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2) := by
    simp only [one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [key]
  exact h ht

/-- **The energy's exact derivative**: `d/ds ⟨L∘A⟩_loc(s) = −Var_loc,t(L∘A)` at `s = t`. -/
theorem hasDerivAt_localised_energy (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (rotatedAnharmonic Q c lam alpha gamma))
      (-gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma)) t := by
  have ht2 := half_pos ht
  have hexp : ∀ s, gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
      (rotatedAnharmonic Q c lam alpha gamma) =
      gibbsExpectation (localisedPotential (separableAnharmonic lam alpha gamma) g
        (affineFrame Q c w₀) s) s (separableAnharmonic lam alpha gamma) := fun s => by
    have e : gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (rotatedAnharmonic Q c lam alpha gamma) =
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (rotated Q c (separableAnharmonic lam alpha gamma)) := rfl
    rw [e, localisedRotated_gibbsExpectation_eq hQ c w₀ s
      (continuous_separableAnharmonic lam alpha gamma), separablePotential_locFamily]
  have hcov : gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) =
      gibbsCov (localisedPotential (separableAnharmonic lam alpha gamma) g (affineFrame Q c w₀) t) t
        (separableAnharmonic lam alpha gamma) (separableAnharmonic lam alpha gamma) := by
    have e : gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) =
        gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma)
          (rotated Q c (separableAnharmonic lam alpha gamma)) := rfl
    rw [e, localisedRotated_gibbsCov_eq hQ c w₀ t (continuous_separableAnharmonic lam alpha gamma),
      separablePotential_locFamily]
  simp only [hexp, hcov]
  have hkl : ∀ k l, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      anharmonicPotential (lam l) (alpha l) (gamma l) (u l) *
      Real.exp (-(t / 2 * separableAnharmonic lam alpha gamma u))) := fun k l => by
    have h2 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht2 k l 2
    have h3 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht2 k l 3
    have h4 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht2 k l 4
    refine (((h2.const_mul (lam l / 2)).add (h3.const_mul (alpha l / 6))).add
      (h4.const_mul (gamma l / 24))).congr (Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply, anharmonicPotential]
    ring
  refine hasDerivAt_localised_separable hlam hgamma hdisc hg (affineFrame Q c w₀) ht
    (continuous_separableAnharmonic lam alpha gamma) ?_
    (integrable_energy_separableAnharmonic hlam hgamma hdisc ht2)
  refine integrable_energy_mul_separableAnharmonic (separableAnharmonic lam alpha gamma) fun k => ?_
  refine (integrable_finsetSum Finset.univ fun l _ => hkl k l).congr
    (Eventually.of_forall fun u => ?_)
  simp only [separableAnharmonic_eq_sum, Finset.mul_sum, Finset.sum_mul]

/-- `−∂ₜ⟨L∘A⟩_loc = Var_loc(L∘A)`: the fluctuation–response identity for the energy. -/
theorem localisedEnergy_neg_deriv_eq_var (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) :
    -deriv (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (rotatedAnharmonic Q c lam alpha gamma)) t =
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) := by
  rw [(hasDerivAt_localised_energy hlam hgamma hdisc hQ c w₀ hg ht).deriv, neg_neg]

/-- **The LLC as the leading coefficient of the temperature response**:
`|t²(−∂ₜ⟨L∘A⟩_loc) − d/2| ≤ K/t`, i.e. `−∂ₜ⟨L∘A⟩_loc = Var_loc(L∘A) = d/(2t²) + O(t⁻³)`. -/
theorem localisedEnergy_neg_deriv_leading (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * (-deriv (fun s =>
          gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
            (rotatedAnharmonic Q c lam alpha gamma)) t) - (d : ℝ) / 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedVar_energy_leading hlam hgamma hdisc hQ c w₀ hg
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedEnergy_neg_deriv_eq_var hlam hgamma hdisc hQ c w₀ hg ht0]
  exact h ht

end Multi

end Laplace.Multi
