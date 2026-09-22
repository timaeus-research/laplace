/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedEnergyInvariant

/-!
# The third cumulant of the localised energy: the LLC governs the second temperature derivative

On E2's exact localised measure, per frame coordinate: the *signed* seventh localised moment is
`O(t⁻⁴)` (from the localised Stein recursion at `k = 4`, whose `O(t)` terms cancel exactly),
`t³⟨ℓ³⟩_loc → 15/8` and the third cumulant `κ₃(ℓ) = ⟨ℓ³⟩ − 3⟨ℓ²⟩⟨ℓ⟩ + 2⟨ℓ⟩³` has `t³κ₃ → 1`. On E2,
exactly `∂ₜ² ⟨L∘A⟩_loc = −∂ₜ Var_loc(L∘A) = ∑ᵢ κ₃,ᵢ`, and `|t³ ∂ₜ²⟨L∘A⟩_loc − d| ≤ K/t`.

With `LocalisedEnergyInvariant`: the LLC `d/2` governs the localised mean energy and its first two
temperature derivatives, `t⟨L⟩ → d/2`, `−t²∂ₜ⟨L⟩ → d/2`, `t³∂ₜ²⟨L⟩ → d` — the first three cumulants
of a Gamma law with shape `d/2` and rate `t`.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section OneD

variable {lam alpha gamma g x₀ : ℝ} (hlam : 0 < lam) (hgamma : 0 < gamma)
  (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- Dividing a bounded `t⁴`-weighted quantity by the denominator. -/
theorem loc_ratio_bounded4 (f : ℝ → ℝ) (hg : 0 ≤ g)
    (hN : ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => f x * locWeight g x₀ x)| ≤ K) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t f| ≤ K := by
  obtain ⟨KN, TN, hKN, hTN, hN⟩ := hN
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨2 * KN, TN + TD + 2 * KD, by positivity, by linarith, fun {t} ht => ?_⟩
  have hTNt : TN ≤ t := by linarith
  have hTDt : TD ≤ t := by linarith
  have h2K : 2 * KD ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [gibbsExpectation_locPotential1 hlam hgamma hdisc ht0]
  have eN := hN hTNt
  have eD := hD hTDt
  have hDhalf : 1 / 2 ≤ _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (locWeight g x₀) := by
    have h1 : KD / t ≤ 1 / 2 := by rw [div_le_iff₀ ht0]; linarith
    have h2 := (abs_le.mp (eD.trans h1)).1
    linarith
  have hD0 : 0 < _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (locWeight g x₀) := by linarith
  rw [← mul_div_assoc, abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  calc |t ^ 4 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => f x * locWeight g x₀ x)| ≤ KN := eN
    _ = 2 * KN * (1 / 2) := by ring
    _ ≤ 2 * KN * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (locWeight g x₀) := by gcongr

/-- Even weighted moments of degree `2k ≥ 8`: `|t⁴ ⟨x^{2k} φ⟩| ≤ K`. -/
theorem locEven_weighted_bound4 (hg : 0 ≤ g) (k : ℕ) (hk : 4 ≤ k) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (2 * k) * locWeight g x₀ x)| ≤ K := by
  obtain ⟨C, T, hC, hT, h⟩ := evenMoment_bound hlam hgamma hdisc k
  refine ⟨Real.exp (g * x₀ ^ 2 / 2) * C, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have hZ := partition_pos' hlam hgamma hdisc ht0
  have hp : ∀ m, Integrable (fun x : ℝ => x ^ m *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht0
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht0 (x₀ := x₀) (2 * k)
  have hG : Integrable (fun x => (Real.exp (g * x₀ ^ 2 / 2) * x ^ (2 * k)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    ((hp (2 * k)).const_mul _).congr (Eventually.of_forall fun x => by dsimp only; ring)
  have hmono : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => |x ^ (2 * k) * locWeight g x₀ x|) ≤
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => Real.exp (g * x₀ ^ 2 / 2) * x ^ (2 * k)) := by
    refine gibbsExpectation_mono' hZ (integrable_abs_weighted hf) hG fun x => ?_
    rw [abs_mul, abs_of_nonneg ((even_two_mul k).pow_nonneg x),
      abs_of_pos (locWeight_pos x), mul_comm]
    exact mul_le_mul_of_nonneg_right (locWeight_le hg x) ((even_two_mul k).pow_nonneg x)
  rw [gibbsExpectation_const_mul₁] at hmono
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 4)]
  calc t ^ 4 * |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (2 * k) * locWeight g x₀ x)|
      ≤ t ^ 4 * (Real.exp (g * x₀ ^ 2 / 2) *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ (2 * k))) :=
        mul_le_mul_of_nonneg_left ((abs_gibbsExpectation_le' hZ _).trans hmono) (by positivity)
    _ ≤ t ^ 4 * (Real.exp (g * x₀ ^ 2 / 2) * (C / t ^ k)) := by
        gcongr
        exact h (t := t) ht
    _ = Real.exp (g * x₀ ^ 2 / 2) * C * (t ^ 4 / t ^ k) := by ring
    _ ≤ Real.exp (g * x₀ ^ 2 / 2) * C * 1 := by
        gcongr
        exact div_le_one_of_le₀ (pow_le_pow_right₀ ht1 hk) (by positivity)
    _ = Real.exp (g * x₀ ^ 2 / 2) * C := mul_one _

/-- Odd weighted moments of degree `2k + 1 ≥ 9`: `|t⁴ ⟨x^{2k+1} φ⟩| ≤ K`, via
`|x|^{2k+1} ≤ (x^{2k} + x^{2(k+1)})/2`. -/
theorem locOdd_weighted_bound4 (hg : 0 ≤ g) (k : ℕ) (hk : 4 ≤ k) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (2 * k + 1) * locWeight g x₀ x)| ≤ K := by
  obtain ⟨C₁, T₁, hC₁, hT₁, h₁⟩ := evenMoment_bound hlam hgamma hdisc k
  obtain ⟨C₂, T₂, hC₂, hT₂, h₂⟩ := evenMoment_bound hlam hgamma hdisc (k + 1)
  refine ⟨Real.exp (g * x₀ ^ 2 / 2) * ((C₁ + C₂) / 2), T₁ + T₂, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hZ := partition_pos' hlam hgamma hdisc ht0
  have hp : ∀ m, Integrable (fun x : ℝ => x ^ m *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht0
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht0 (x₀ := x₀) (2 * k + 1)
  have hG : Integrable (fun x =>
      (Real.exp (g * x₀ ^ 2 / 2) * ((x ^ (2 * k) + x ^ (2 * (k + 1))) / 2)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    (((hp (2 * k)).add (hp (2 * (k + 1)))).const_mul (Real.exp (g * x₀ ^ 2 / 2) / 2)).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have hodd : ∀ x : ℝ, |x| ^ (2 * k + 1) ≤ (x ^ (2 * k) + x ^ (2 * (k + 1))) / 2 := fun x => by
    have he : |x| ^ (2 * k) = x ^ (2 * k) := Even.pow_abs (even_two_mul k) x
    have he' : |x| ^ (2 * (k + 1)) = x ^ (2 * (k + 1)) := Even.pow_abs (even_two_mul (k + 1)) x
    have h := mul_nonneg (pow_nonneg (abs_nonneg x) (2 * k)) (sq_nonneg (|x| - 1))
    have e : |x| ^ (2 * k) * (|x| - 1) ^ 2 =
        |x| ^ (2 * (k + 1)) - 2 * |x| ^ (2 * k + 1) + |x| ^ (2 * k) := by ring
    rw [e] at h
    linarith
  have hmono : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => |x ^ (2 * k + 1) * locWeight g x₀ x|) ≤
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => Real.exp (g * x₀ ^ 2 / 2) * ((x ^ (2 * k) + x ^ (2 * (k + 1))) / 2)) := by
    refine gibbsExpectation_mono' hZ (integrable_abs_weighted hf) hG fun x => ?_
    rw [abs_mul, abs_of_pos (locWeight_pos x), abs_pow, mul_comm]
    exact mul_le_mul (locWeight_le hg x) (hodd x) (by positivity) (by positivity)
  rw [gibbsExpectation_const_mul₁] at hmono
  have hsplit : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => (x ^ (2 * k) + x ^ (2 * (k + 1))) / 2) =
      1 / 2 * (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (2 * k)) +
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (2 * (k + 1)))) := by
    rw [← _root_.Laplace.gibbsExpectation_add _ _ _ _ (hp _) (hp _),
      ← _root_.Laplace.gibbsExpectation_smul]
    congr 1
    funext x
    ring
  rw [hsplit] at hmono
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 4)]
  have hk1 : t ^ 4 ≤ t ^ k := pow_le_pow_right₀ ht1 hk
  have hk2 : t ^ 4 ≤ t ^ (k + 1) := pow_le_pow_right₀ ht1 (by omega)
  calc t ^ 4 * |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (2 * k + 1) * locWeight g x₀ x)|
      ≤ t ^ 4 * (Real.exp (g * x₀ ^ 2 / 2) * (1 / 2 *
          (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ (2 * k)) +
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ (2 * (k + 1)))))) :=
        mul_le_mul_of_nonneg_left ((abs_gibbsExpectation_le' hZ _).trans hmono) (by positivity)
    _ ≤ t ^ 4 * (Real.exp (g * x₀ ^ 2 / 2) * (1 / 2 * (C₁ / t ^ k + C₂ / t ^ (k + 1)))) := by
        gcongr
        · exact h₁ (t := t) (by linarith)
        · exact h₂ (t := t) (by linarith)
    _ = Real.exp (g * x₀ ^ 2 / 2) * ((C₁ * (t ^ 4 / t ^ k) + C₂ * (t ^ 4 / t ^ (k + 1))) / 2) := by
        ring
    _ ≤ Real.exp (g * x₀ ^ 2 / 2) * ((C₁ * 1 + C₂ * 1) / 2) := by
        gcongr
        · exact div_le_one_of_le₀ hk1 (by positivity)
        · exact div_le_one_of_le₀ hk2 (by positivity)
    _ = Real.exp (g * x₀ ^ 2 / 2) * ((C₁ + C₂) / 2) := by ring

theorem locEven_loc_bound4 (hg : 0 ≤ g) (k : ℕ) (hk : 4 ≤ k) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ (2 * k))| ≤ K :=
  loc_ratio_bounded4 hlam hgamma hdisc (fun x => x ^ (2 * k)) hg
    (locEven_weighted_bound4 hlam hgamma hdisc hg k hk)

theorem locOdd_loc_bound4 (hg : 0 ≤ g) (k : ℕ) (hk : 4 ≤ k) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ (2 * k + 1))| ≤ K :=
  loc_ratio_bounded4 hlam hgamma hdisc (fun x => x ^ (2 * k + 1)) hg
    (locOdd_weighted_bound4 hlam hgamma hdisc hg k hk)

omit hgamma hdisc in
/-- The leading Stein consistency: `4c₃ + 3a/λ² − λc₅ − (α/2)(15/λ³) = 0`. -/
theorem stein_leading_consistency :
    4 * locThirdCoeff lam alpha g x₀ + 3 * (g * x₀) / lam ^ 2 - lam * locFifthCoeff lam alpha g x₀ -
      alpha / 2 * (15 / lam ^ 3) = 0 := by
  have hl : lam ≠ 0 := hlam.ne'
  unfold locThirdCoeff locFifthCoeff
  field_simp
  ring

/-- **The signed localised seventh moment is `O(t⁻⁴)`**: `|t⁴ ⟨x⁷⟩_loc| ≤ K` eventually, from the
Stein recursion at `k = 4` whose `O(t)` terms cancel by `stein_leading_consistency`. -/
theorem locSeventhMoment_loc_bound4 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 7)| ≤ K := by
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locThirdMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := locFifthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := locSixthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨6 / gamma * (4 * K₃ + |g * x₀| * K₄ + lam * K₅ + g * |locFifthCoeff lam alpha g x₀| +
    g * K₅ + |alpha| / 2 * K₆), T₃ + T₄ + T₅ + T₆, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hγ : gamma ≠ 0 := hgamma.ne'
  have hrec := stein_loc_recursion hlam hgamma hdisc hg ht0 (x₀ := x₀) 4
  norm_num at hrec
  set m₃ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 3) with hm₃
  set m₄ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 4) with hm₄
  set m₅ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 5) with hm₅
  set m₆ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 6) with hm₆
  set m₇ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 7) with hm₇
  have e₃ := h₃ (t := t) (by linarith)
  have e₄ := h₄ (t := t) (by linarith)
  have e₅ := h₅ (t := t) (by linarith)
  have e₆ := h₆ (t := t) (by linarith)
  have hm7 : m₇ = (4 * m₃ + g * x₀ * m₄ - (t * lam + g) * m₅ - t * alpha / 2 * m₆) /
      (t * gamma / 6) := by
    rw [eq_div_iff (by positivity)]
    linear_combination hrec
  have hrec3 : gamma / 6 * (t ^ 4 * m₇) = 4 * (t * (t ^ 2 * m₃)) + g * x₀ * (t * (t ^ 2 * m₄)) -
      lam * (t * (t ^ 3 * m₅)) - g * (t ^ 3 * m₅) - alpha / 2 * (t * (t ^ 3 * m₆)) := by
    linear_combination t ^ 3 * hrec
  have key : t ^ 4 * m₇ = 6 / gamma * (4 * (t * (t ^ 2 * m₃ - locThirdCoeff lam alpha g x₀)) +
      g * x₀ * (t * (t ^ 2 * m₄ - 3 / lam ^ 2)) -
      lam * (t * (t ^ 3 * m₅ - locFifthCoeff lam alpha g x₀)) - g * (t ^ 3 * m₅) -
      alpha / 2 * (t * (t ^ 3 * m₆ - 15 / lam ^ 3))) := by
    have hc := stein_leading_consistency hlam (alpha := alpha) (g := g) (x₀ := x₀)
    calc t ^ 4 * m₇ = 6 / gamma * (gamma / 6 * (t ^ 4 * m₇)) := by field_simp
      _ = _ := by
        rw [hrec3]
        congr 1
        linear_combination t * hc
  rw [key]
  have b₃ : |4 * (t * (t ^ 2 * m₃ - locThirdCoeff lam alpha g x₀))| ≤ 4 * K₃ := by
    rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have := mul_le_mul_of_nonneg_left e₃ ht0.le
    rw [mul_div_cancel₀ _ ht0.ne'] at this
    linarith
  have b₄ : |g * x₀ * (t * (t ^ 2 * m₄ - 3 / lam ^ 2))| ≤ |g * x₀| * K₄ := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_mul, abs_of_pos ht0]
    have := mul_le_mul_of_nonneg_left e₄ ht0.le
    rw [mul_div_cancel₀ _ ht0.ne'] at this
    exact this
  have b₅ : |lam * (t * (t ^ 3 * m₅ - locFifthCoeff lam alpha g x₀))| ≤ lam * K₅ := by
    rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_pos hlam]
    have := mul_le_mul_of_nonneg_left e₅ ht0.le
    rw [mul_div_cancel₀ _ ht0.ne'] at this
    exact mul_le_mul_of_nonneg_left this hlam.le
  have b₅' : |g * (t ^ 3 * m₅)| ≤ g * |locFifthCoeff lam alpha g x₀| + g * K₅ := by
    rw [abs_mul, abs_of_nonneg hg, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hg
    have h1 : |t ^ 3 * m₅| ≤ |locFifthCoeff lam alpha g x₀| + K₅ / t := by
      have := abs_sub_abs_le_abs_sub (t ^ 3 * m₅) (locFifthCoeff lam alpha g x₀)
      linarith
    have h2 : K₅ / t ≤ K₅ := div_le_self hK₅ ht1
    linarith
  have b₆ : |alpha / 2 * (t * (t ^ 3 * m₆ - 15 / lam ^ 3))| ≤ |alpha| / 2 * K₆ := by
    rw [abs_mul, abs_mul, abs_of_pos ht0, abs_div, abs_two]
    have := mul_le_mul_of_nonneg_left e₆ ht0.le
    rw [mul_div_cancel₀ _ ht0.ne'] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 6 / gamma)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |4 * (t * (t ^ 2 * m₃ - locThirdCoeff lam alpha g x₀)) +
        g * x₀ * (t * (t ^ 2 * m₄ - 3 / lam ^ 2)) -
        lam * (t * (t ^ 3 * m₅ - locFifthCoeff lam alpha g x₀)) - g * (t ^ 3 * m₅) -
        alpha / 2 * (t * (t ^ 3 * m₆ - 15 / lam ^ 3))|
      ≤ |4 * (t * (t ^ 2 * m₃ - locThirdCoeff lam alpha g x₀))| +
        |g * x₀ * (t * (t ^ 2 * m₄ - 3 / lam ^ 2))| +
        |lam * (t * (t ^ 3 * m₅ - locFifthCoeff lam alpha g x₀))| + |g * (t ^ 3 * m₅)| +
        |alpha / 2 * (t * (t ^ 3 * m₆ - 15 / lam ^ 3))| := by
        have a1 := abs_add_le (4 * (t * (t ^ 2 * m₃ - locThirdCoeff lam alpha g x₀)))
          (g * x₀ * (t * (t ^ 2 * m₄ - 3 / lam ^ 2)))
        have a2 := abs_sub (4 * (t * (t ^ 2 * m₃ - locThirdCoeff lam alpha g x₀)) +
          g * x₀ * (t * (t ^ 2 * m₄ - 3 / lam ^ 2)))
          (lam * (t * (t ^ 3 * m₅ - locFifthCoeff lam alpha g x₀)))
        have a3 := abs_sub (4 * (t * (t ^ 2 * m₃ - locThirdCoeff lam alpha g x₀)) +
          g * x₀ * (t * (t ^ 2 * m₄ - 3 / lam ^ 2)) -
          lam * (t * (t ^ 3 * m₅ - locFifthCoeff lam alpha g x₀))) (g * (t ^ 3 * m₅))
        have a4 := abs_sub (4 * (t * (t ^ 2 * m₃ - locThirdCoeff lam alpha g x₀)) +
          g * x₀ * (t * (t ^ 2 * m₄ - 3 / lam ^ 2)) -
          lam * (t * (t ^ 3 * m₅ - locFifthCoeff lam alpha g x₀)) - g * (t ^ 3 * m₅))
          (alpha / 2 * (t * (t ^ 3 * m₆ - 15 / lam ^ 3)))
        linarith
    _ ≤ 4 * K₃ + |g * x₀| * K₄ + lam * K₅ + (g * |locFifthCoeff lam alpha g x₀| + g * K₅) +
        |alpha| / 2 * K₆ := by linarith [b₃, b₄, b₅, b₅', b₆]
    _ = _ := by ring

/-- `⟨ℓ³⟩_loc` as a combination of the localised moments of degrees `6` to `12`. -/
theorem locEnergyCube_eq (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => anharmonicPotential lam alpha gamma x *
          (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x)) =
      lam ^ 3 / 8 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 6) +
        (lam ^ 2 * alpha / 8 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀
            t)
          t (fun x => x ^ 7) +
        ((lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) *
          _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
            (fun x => x ^ 8) +
        ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) *
          _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
            (fun x => x ^ 9) +
        ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) *
          _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
            (fun x => x ^ 10) +
        (alpha * gamma ^ 2 / 1152 *
          _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
            (fun x => x ^ 11) +
        gamma ^ 3 / 13824 *
          _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
            (fun x => x ^ 12)))))) := by
  have hp : ∀ m, Integrable (fun x : ℝ => x ^ m *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    integrable_pow_locPotential1 hlam hgamma hdisc hg ht
  have hc : ∀ (a : ℝ) (m : ℕ), Integrable (fun x : ℝ => a * x ^ m *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := fun a m =>
    ((hp m).const_mul a).congr (Eventually.of_forall fun x => by ring)
  have h12 := hc (gamma ^ 3 / 13824) 12
  have h11 : Integrable (fun x : ℝ =>
      (alpha * gamma ^ 2 / 1152 * x ^ 11 + gamma ^ 3 / 13824 * x ^ 12) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (alpha * gamma ^ 2 / 1152) 11).add h12).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h10 : Integrable (fun x : ℝ => ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * x ^ 10 +
      (alpha * gamma ^ 2 / 1152 * x ^ 11 + gamma ^ 3 / 13824 * x ^ 12)) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) 10).add h11).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h9 : Integrable (fun x : ℝ => ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) * x ^ 9 +
      ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * x ^ 10 +
      (alpha * gamma ^ 2 / 1152 * x ^ 11 + gamma ^ 3 / 13824 * x ^ 12))) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (lam * alpha * gamma / 48 + alpha ^ 3 / 216) 9).add h10).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h8 : Integrable (fun x : ℝ => ((lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) * x ^ 8 +
      ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) * x ^ 9 +
      ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * x ^ 10 +
      (alpha * gamma ^ 2 / 1152 * x ^ 11 + gamma ^ 3 / 13824 * x ^ 12)))) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) 8).add h9).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h7 : Integrable (fun x : ℝ => (lam ^ 2 * alpha / 8 * x ^ 7 +
      ((lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) * x ^ 8 +
      ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) * x ^ 9 +
      ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * x ^ 10 +
      (alpha * gamma ^ 2 / 1152 * x ^ 11 + gamma ^ 3 / 13824 * x ^ 12))))) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (lam ^ 2 * alpha / 8) 7).add h8).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have e : (fun x => anharmonicPotential lam alpha gamma x *
      (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x)) =
      fun x => lam ^ 3 / 8 * x ^ 6 + (lam ^ 2 * alpha / 8 * x ^ 7 +
      ((lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) * x ^ 8 +
      ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) * x ^ 9 +
      ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * x ^ 10 +
      (alpha * gamma ^ 2 / 1152 * x ^ 11 + gamma ^ 3 / 13824 * x ^ 12))))) := by
    funext x
    simp only [anharmonicPotential]
    ring
  rw [e, _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam ^ 3 / 8) 6) h7,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam ^ 2 * alpha / 8) 7) h8,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) 8)
      h9,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam * alpha * gamma / 48 + alpha ^ 3 / 216) 9)
      h10,
    _root_.Laplace.gibbsExpectation_add _ _ _ _
      (hc (lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) 10) h11,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (alpha * gamma ^ 2 / 1152) 11) h12,
    _root_.Laplace.gibbsExpectation_smul, _root_.Laplace.gibbsExpectation_smul,
    _root_.Laplace.gibbsExpectation_smul, _root_.Laplace.gibbsExpectation_smul,
    _root_.Laplace.gibbsExpectation_smul, _root_.Laplace.gibbsExpectation_smul,
    _root_.Laplace.gibbsExpectation_smul]

omit hlam hgamma hdisc in
/-- Assembly: `|t³⟨ℓ³⟩_loc − 15/8| ≤ K/t` from the moment rates and `t⁴`-scaled bounds. -/
theorem energyCube_assembly (lam alpha gamma t M₆ M₇ M₈ M₉ M₁₀ M₁₁ M₁₂ : ℝ)
    (K₆ K₇ K₈ K₉ K₁₀ K₁₁ K₁₂ : ℝ) (hlam : 0 < lam) (ht1 : 1 ≤ t) (e₆ : |t ^ 3 * M₆ - 15 / lam ^ 3|
        ≤ K₆ / t)
    (e₇ : |t ^ 4 * M₇| ≤ K₇) (e₈ : |t ^ 4 * M₈| ≤ K₈) (e₉ : |t ^ 4 * M₉| ≤ K₉)
    (e₁₀ : |t ^ 4 * M₁₀| ≤ K₁₀) (e₁₁ : |t ^ 4 * M₁₁| ≤ K₁₁) (e₁₂ : |t ^ 4 * M₁₂| ≤ K₁₂) :
    |t ^ 3 * (lam ^ 3 / 8 * M₆ + (lam ^ 2 * alpha / 8 * M₇ +
        ((lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) * M₈ +
        ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) * M₉ +
        ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * M₁₀ +
        (alpha * gamma ^ 2 / 1152 * M₁₁ + gamma ^ 3 / 13824 * M₁₂)))))) - 15 / 8| ≤
      (lam ^ 3 / 8 * K₆ + (|lam ^ 2 * alpha / 8| * K₇ +
        (|lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24| * K₈ + (|lam * alpha * gamma / 48 + alpha ^
            3 / 216| * K₉ +
        (|lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288| * K₁₀ +
        (|alpha * gamma ^ 2 / 1152| * K₁₁ + |gamma ^ 3 / 13824| * K₁₂)))))) / t := by
  have ht0 : 0 < t := by linarith
  have hl : lam ≠ 0 := hlam.ne'
  have key : t ^ 3 * (lam ^ 3 / 8 * M₆ + (lam ^ 2 * alpha / 8 * M₇ +
      ((lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) * M₈ +
      ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) * M₉ +
      ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * M₁₀ +
      (alpha * gamma ^ 2 / 1152 * M₁₁ + gamma ^ 3 / 13824 * M₁₂)))))) - 15 / 8 =
      lam ^ 3 / 8 * (t ^ 3 * M₆ - 15 / lam ^ 3) + (lam ^ 2 * alpha / 8 * (t ^ 4 * M₇) +
      ((lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) * (t ^ 4 * M₈) +
      ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) * (t ^ 4 * M₉) +
      ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * (t ^ 4 * M₁₀) +
      (alpha * gamma ^ 2 / 1152 * (t ^ 4 * M₁₁) + gamma ^ 3 / 13824 * (t ^ 4 * M₁₂)))))) / t := by
    field_simp
    ring
  rw [key]
  have h6 : |lam ^ 3 / 8 * (t ^ 3 * M₆ - 15 / lam ^ 3)| ≤ lam ^ 3 / 8 * (K₆ / t) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam ^ 3 / 8)]
    exact mul_le_mul_of_nonneg_left e₆ (by positivity)
  have hb : ∀ (c X K : ℝ), |t ^ 4 * X| ≤ K → |c * (t ^ 4 * X)| ≤ |c| * K := fun c X K h => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hrest : |lam ^ 2 * alpha / 8 * (t ^ 4 * M₇) +
      ((lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) * (t ^ 4 * M₈) +
      ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) * (t ^ 4 * M₉) +
      ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * (t ^ 4 * M₁₀) +
      (alpha * gamma ^ 2 / 1152 * (t ^ 4 * M₁₁) + gamma ^ 3 / 13824 * (t ^ 4 * M₁₂)))))| ≤
      |lam ^ 2 * alpha / 8| * K₇ + (|lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24| * K₈ +
      (|lam * alpha * gamma / 48 + alpha ^ 3 / 216| * K₉ +
      (|lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288| * K₁₀ +
      (|alpha * gamma ^ 2 / 1152| * K₁₁ + |gamma ^ 3 / 13824| * K₁₂)))) :=
    (abs_add_le _ _).trans (add_le_add (hb _ _ _ e₇) ((abs_add_le _ _).trans (add_le_add
      (hb _ _ _ e₈) ((abs_add_le _ _).trans (add_le_add (hb _ _ _ e₉) ((abs_add_le _ _).trans
      (add_le_add (hb _ _ _ e₁₀) ((abs_add_le _ _).trans (add_le_add (hb _ _ _ e₁₁)
      (hb _ _ _ e₁₂))))))))))
  calc _ ≤ |lam ^ 3 / 8 * (t ^ 3 * M₆ - 15 / lam ^ 3)| + |lam ^ 2 * alpha / 8 * (t ^ 4 * M₇) +
        ((lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24) * (t ^ 4 * M₈) +
        ((lam * alpha * gamma / 48 + alpha ^ 3 / 216) * (t ^ 4 * M₉) +
        ((lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288) * (t ^ 4 * M₁₀) +
        (alpha * gamma ^ 2 / 1152 * (t ^ 4 * M₁₁) + gamma ^ 3 / 13824 * (t ^ 4 * M₁₂)))))| / t := by
        rw [← abs_of_pos ht0, ← abs_div, abs_of_pos ht0]
        exact abs_add_le _ _
    _ ≤ lam ^ 3 / 8 * (K₆ / t) + (|lam ^ 2 * alpha / 8| * K₇ +
        (|lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24| * K₈ +
        (|lam * alpha * gamma / 48 + alpha ^ 3 / 216| * K₉ +
        (|lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288| * K₁₀ +
        (|alpha * gamma ^ 2 / 1152| * K₁₁ + |gamma ^ 3 / 13824| * K₁₂))))) / t := by gcongr
    _ = _ := by ring

/-- **The leading localised energy third moment**: `|t³⟨ℓ³⟩_loc − 15/8| ≤ K/t`. -/
theorem locEnergyCube_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => anharmonicPotential lam alpha gamma x *
          (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x)) -
        15 / 8| ≤ K / t := by
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := locSixthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₇, T₇, hK₇, hT₇, h₇⟩ := locSeventhMoment_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₈, T₈, hK₈, hT₈, h₈⟩ := locEven_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀) 4 le_rfl
  obtain ⟨K₉, T₉, hK₉, hT₉, h₉⟩ := locOdd_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀) 4 le_rfl
  obtain ⟨K₁₀, T₁₀, hK₁₀, hT₁₀, h₁₀⟩ := locEven_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀) 5
    (by norm_num)
  obtain ⟨K₁₁, T₁₁, hK₁₁, hT₁₁, h₁₁⟩ := locOdd_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀) 5
    (by norm_num)
  obtain ⟨K₁₂, T₁₂, hK₁₂, hT₁₂, h₁₂⟩ := locEven_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀) 6
    (by norm_num)
  refine ⟨lam ^ 3 / 8 * K₆ + (|lam ^ 2 * alpha / 8| * K₇ +
    (|lam ^ 2 * gamma / 32 + lam * alpha ^ 2 / 24| * K₈ +
    (|lam * alpha * gamma / 48 + alpha ^ 3 / 216| * K₉ +
    (|lam * gamma ^ 2 / 384 + alpha ^ 2 * gamma / 288| * K₁₀ +
    (|alpha * gamma ^ 2 / 1152| * K₁₁ + |gamma ^ 3 / 13824| * K₁₂))))),
    T₆ + T₇ + T₈ + T₉ + T₁₀ + T₁₁ + T₁₂, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [locEnergyCube_eq hlam hgamma hdisc hg ht0]
  exact energyCube_assembly lam alpha gamma t _ _ _ _ _ _ _ K₆ K₇ K₈ K₉ K₁₀ K₁₁ K₁₂ hlam ht1
    (h₆ (t := t) (by linarith)) (h₇ (t := t) (by linarith)) (h₈ (t := t) (by linarith))
    (h₉ (t := t) (by linarith)) (h₁₀ (t := t) (by linarith)) (h₁₁ (t := t) (by linarith))
    (h₁₂ (t := t) (by linarith))

/-- `|t⟨ℓ⟩_loc − ½| ≤ K/t`. -/
theorem locEnergy_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) - 1 / 2| ≤ K / t := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := localisedEnergy_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨|energyLocCoeff1 lam alpha gamma g x₀| + K₁, T₁, by positivity, hT₁, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT₁.trans ht
  have ht0 : 0 < t := by linarith
  have h := h₁ ht
  have e : t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
      (anharmonicPotential lam alpha gamma) - 1 / 2 =
      (t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) - 1 / 2 -
        energyLocCoeff1 lam alpha gamma g x₀ / t) + energyLocCoeff1 lam alpha gamma g x₀ / t := by
    ring
  have hK : K₁ / t ^ 2 ≤ K₁ / t := div_le_div_of_nonneg_left hK₁ ht0 (by nlinarith)
  rw [e]
  calc _ ≤ |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) - 1 / 2 - energyLocCoeff1 lam alpha gamma g x₀ / t| +
        |energyLocCoeff1 lam alpha gamma g x₀ / t| := abs_add_le _ _
    _ ≤ K₁ / t + |energyLocCoeff1 lam alpha gamma g x₀| / t := by
        rw [abs_div, abs_of_pos ht0]
        exact add_le_add (h.trans hK) le_rfl
    _ = (|energyLocCoeff1 lam alpha gamma g x₀| + K₁) / t := by ring

/-- **The third cumulant of the localised energy at leading order**:
`|t³ (⟨ℓ³⟩ − 3⟨ℓ²⟩⟨ℓ⟩ + 2⟨ℓ⟩³) − 1| ≤ K/t` — the third cumulant of a `Gamma(½, t)` law. -/
theorem locEnergyCum3_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => anharmonicPotential lam alpha gamma x *
            (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x)) -
        3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) *
          _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
            (anharmonicPotential lam alpha gamma) +
        2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) ^ 3) - 1| ≤ K / t := by
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locEnergyCube_leading hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locEnergySq_leading hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := locEnergy_leading hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K₃ + 3 * (K₂ * (|(1 : ℝ) / 2| + K₁) + |(3 : ℝ) / 4| * K₁) +
    2 * ((2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2) * (|(1 : ℝ) / 2| + K₁) + |((1 : ℝ) / 2) ^ 2| * K₁),
    T₃ + T₂ + T₁, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have e₃ := h₃ (t := t) (by linarith)
  have e₂ := h₂ (t := t) (by linarith)
  have e₁ := h₁ (t := t) (by linarith)
  have p₂₁ := prod_rate t _ _ (3 / 4) (1 / 2) K₂ K₁ ht1 hK₂ hK₁ e₂ e₁
  have hsq := sq_rate ht1 hK₁ e₁
  have p₁₁₁ := prod_rate t _ _ ((1 / 2) ^ 2) (1 / 2) (2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2) K₁ ht1
    (by positivity) hK₁ hsq e₁
  set X₃ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => anharmonicPotential lam alpha gamma x *
      (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x)) with hX₃
  set X₂ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) with
        hX₂
  set X₁ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (anharmonicPotential lam alpha gamma) with hX₁
  have key : t ^ 3 * (X₃ - 3 * X₂ * X₁ + 2 * X₁ ^ 3) - 1 =
      (t ^ 3 * X₃ - 15 / 8) - 3 * ((t ^ 2 * X₂) * (t * X₁) - 3 / 4 * (1 / 2)) +
        2 * ((t * X₁) ^ 2 * (t * X₁) - (1 / 2) ^ 2 * (1 / 2)) := by ring
  rw [key]
  calc _ ≤ |t ^ 3 * X₃ - 15 / 8| + |3 * ((t ^ 2 * X₂) * (t * X₁) - 3 / 4 * (1 / 2))| +
        |2 * ((t * X₁) ^ 2 * (t * X₁) - (1 / 2) ^ 2 * (1 / 2))| := by
        have := abs_sub (t ^ 3 * X₃ - 15 / 8) (3 * ((t ^ 2 * X₂) * (t * X₁) - 3 / 4 * (1 / 2)))
        have := abs_add_le (t ^ 3 * X₃ - 15 / 8 - 3 * ((t ^ 2 * X₂) * (t * X₁) - 3 / 4 * (1 / 2)))
          (2 * ((t * X₁) ^ 2 * (t * X₁) - (1 / 2) ^ 2 * (1 / 2)))
        linarith
    _ ≤ K₃ / t + 3 * ((K₂ * (|(1 : ℝ) / 2| + K₁) + |(3 : ℝ) / 4| * K₁) / t) +
        2 * (((2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2) * (|(1 : ℝ) / 2| + K₁) +
          |((1 : ℝ) / 2) ^ 2| * K₁) / t) := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
    _ = _ := by ring

end OneD

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- `⟨f(uᵢ)⟩_loc = ⟨f⟩_loc,ᵢ` for a continuous `f`. -/
theorem localised_frame_fun_expectation (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) (i : Fin d) (f : ℝ → ℝ) (hf : Continuous f) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => f (affineFrame Q c w i)) =
      _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t f := by
  have e : (fun w => f (affineFrame Q c w i)) = rotated Q c (fun u : Fin d → ℝ => f (u i)) := rfl
  rw [e, localisedRotated_gibbsExpectation_eq hQ c w₀ t (ψ := fun u : Fin d → ℝ => f (u i))
    (by exact hf.comp (continuous_apply i))]
  exact gibbsExpectation_coord_separable _ t
    (partitionFunction_locFamily_ne hlam hgamma hdisc hg _ ht) i f

/-- `Cov_loc[L∘A, f(uᵢ)] = Cov_loc,ᵢ[ℓᵢ, f]` given integrability of `ℓₖ(uₖ) f(uᵢ)` on the frame
family. -/
theorem localisedCovK_frame_fun (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (i : Fin d) (f : ℝ → ℝ) (hf : Continuous f)
    (hfk : ∀ k, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * f (u i) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u)))) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => f (affineFrame Q c w i)) =
      _root_.Laplace.gibbsCov
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) f := by
  have e : (fun w => f (affineFrame Q c w i)) = rotated Q c (fun u : Fin d → ℝ => f (u i)) := rfl
  rw [e, localisedRotated_gibbsCov_eq hQ c w₀ t (ψ := fun u : Fin d → ℝ => f (u i))
    (by exact hf.comp (continuous_apply i))]
  have hℓ : ∀ k, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g (affineFrame Q c w₀) t)
        u))) := integrable_energy_locFamily hlam hgamma hdisc hg (affineFrame Q c w₀) ht
  have hZ : ∀ m, _root_.Laplace.partitionFunction
      (locFamily lam alpha gamma g (affineFrame Q c w₀) t m) t ≠ 0 :=
    partitionFunction_locFamily_ne hlam hgamma hdisc hg (affineFrame Q c w₀) ht
  rw [separableAnharmonic_eq_sum,
    gibbsCov_finsetSum_left _ t Finset.univ _ _ (fun k _ => hℓ k) (fun k _ => hfk k)]
  simp only [gibbsCov_coord_fun_separable (locFamily lam alpha gamma g (affineFrame Q c w₀) t) t hZ,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- The derivative of `⟨f(uᵢ)⟩_loc(s)` for a continuous `f` with the two integrability
hypotheses at temperature `t/2`. -/
theorem hasDerivAt_localised_frame_fun (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (i : Fin d) (f : ℝ → ℝ) (hf : Continuous f)
    (h1 : ∀ k, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * f (u i) *
      Real.exp (-(t / 2 * separableAnharmonic lam alpha gamma u))))
    (h0 : Integrable (fun u : Fin d → ℝ => f (u i) *
      Real.exp (-(t / 2 * separableAnharmonic lam alpha gamma u)))) :
    HasDerivAt (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => f (affineFrame Q c w i)))
      (-gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => f (affineFrame Q c w i))) t := by
  have e : (fun w => f (affineFrame Q c w i)) = rotated Q c (fun u : Fin d → ℝ => f (u i)) := rfl
  have hc : Continuous fun u : Fin d → ℝ => f (u i) := hf.comp (continuous_apply i)
  have hexp : ∀ s, gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
      (fun w => f (affineFrame Q c w i)) =
      gibbsExpectation (localisedPotential (separableAnharmonic lam alpha gamma) g
        (affineFrame Q c w₀) s) s (fun u => f (u i)) := fun s => by
    rw [e, localisedRotated_gibbsExpectation_eq hQ c w₀ s hc, separablePotential_locFamily]
  have hcov : gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => f (affineFrame Q c w i)) =
      gibbsCov (localisedPotential (separableAnharmonic lam alpha gamma) g (affineFrame Q c w₀) t) t
        (separableAnharmonic lam alpha gamma) (fun u => f (u i)) := by
    rw [e, localisedRotated_gibbsCov_eq hQ c w₀ t hc, separablePotential_locFamily]
  simp only [hexp, hcov]
  exact hasDerivAt_localised_separable hlam hgamma hdisc hg (affineFrame Q c w₀) ht hc
    (integrable_energy_mul_separableAnharmonic (fun u => f (u i)) h1) h0

/-- Integrability of `ℓₖ(uₖ) ℓᵢ(uᵢ)` against the unlocalised separable measure at temperature
`s`. -/
theorem integrable_energy_energy_coord (k i : Fin d) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      anharmonicPotential (lam i) (alpha i) (gamma i) (u i) *
      Real.exp (-(s * separableAnharmonic lam alpha gamma u))) := by
  have h2 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 2
  have h3 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 3
  have h4 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 4
  refine (((h2.const_mul (lam i / 2)).add (h3.const_mul (alpha i / 6))).add
    (h4.const_mul (gamma i / 24))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

/-- Integrability of `ℓₖ(uₖ) ℓᵢ(uᵢ)²` against the unlocalised separable measure. -/
theorem integrable_energy_energySq_coord (k i : Fin d) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      (anharmonicPotential (lam i) (alpha i) (gamma i) (u i) *
        anharmonicPotential (lam i) (alpha i) (gamma i) (u i)) *
      Real.exp (-(s * separableAnharmonic lam alpha gamma u))) := by
  have h4 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 4
  have h5 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 5
  have h6 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 6
  have h7 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 7
  have h8 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 8
  refine (((((h4.const_mul (lam i ^ 2 / 4)).add (h5.const_mul (lam i * alpha i / 6))).add
    (h6.const_mul (lam i * gamma i / 24 + alpha i ^ 2 / 36))).add
    (h7.const_mul (alpha i * gamma i / 72))).add
    (h8.const_mul (gamma i ^ 2 / 576))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

/-- Integrability of `ℓᵢ(uᵢ)` against the unlocalised separable measure. -/
theorem integrable_energy_coord_alone (i : Fin d) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam i) (alpha i) (gamma i) (u i) *
      Real.exp (-(s * separableAnharmonic lam alpha gamma u))) := by
  have h2 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 2
  have h3 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 3
  have h4 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 4
  refine (((h2.const_mul (lam i / 2)).add (h3.const_mul (alpha i / 6))).add
    (h4.const_mul (gamma i / 24))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential, pow_zero, one_mul]
  ring

/-- Integrability of `ℓᵢ(uᵢ)²` against the unlocalised separable measure. -/
theorem integrable_energySq_coord_alone (i : Fin d) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u : Fin d → ℝ => (anharmonicPotential (lam i) (alpha i) (gamma i) (u i) *
      anharmonicPotential (lam i) (alpha i) (gamma i) (u i)) *
      Real.exp (-(s * separableAnharmonic lam alpha gamma u))) := by
  have h4 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 4
  have h5 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 5
  have h6 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 6
  have h7 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 7
  have h8 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 8
  refine (((((h4.const_mul (lam i ^ 2 / 4)).add (h5.const_mul (lam i * alpha i / 6))).add
    (h6.const_mul (lam i * gamma i / 24 + alpha i ^ 2 / 36))).add
    (h7.const_mul (alpha i * gamma i / 72))).add
    (h8.const_mul (gamma i ^ 2 / 576))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential, pow_zero, one_mul]
  ring

/-- Integrability of `ℓₖ(uₖ) ℓᵢ(uᵢ)` on the frame family. -/
theorem integrable_energy_energy_locFamily (hg : 0 ≤ g) (u₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (k i : Fin d) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      anharmonicPotential (lam i) (alpha i) (gamma i) (u i) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) := by
  have h2 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 2
  have h3 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 3
  have h4 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 4
  refine (((h2.const_mul (lam i / 2)).add (h3.const_mul (alpha i / 6))).add
    (h4.const_mul (gamma i / 24))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

/-- Integrability of `ℓₖ(uₖ) ℓᵢ(uᵢ)²` on the frame family. -/
theorem integrable_energy_energySq_locFamily (hg : 0 ≤ g) (u₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (k i : Fin d) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      (anharmonicPotential (lam i) (alpha i) (gamma i) (u i) *
        anharmonicPotential (lam i) (alpha i) (gamma i) (u i)) *
      Real.exp (-(t * separablePotential (locFamily lam alpha gamma g u₀ t) u))) := by
  have h4 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 4
  have h5 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 5
  have h6 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 6
  have h7 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 7
  have h8 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 8
  refine (((((h4.const_mul (lam i ^ 2 / 4)).add (h5.const_mul (lam i * alpha i / 6))).add
    (h6.const_mul (lam i * gamma i / 24 + alpha i ^ 2 / 36))).add
    (h7.const_mul (alpha i * gamma i / 72))).add
    (h8.const_mul (gamma i ^ 2 / 576))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

/-- **The derivative of the `i`-th coordinate energy variance**:
`d/ds Var_loc,ᵢ(ℓᵢ)(s) = −κ₃,loc,ᵢ(t)` with `κ₃ = ⟨ℓ³⟩ − 3⟨ℓ²⟩⟨ℓ⟩ + 2⟨ℓ⟩³`, through the frame
expectations `⟨ℓᵢ(uᵢ)²⟩_loc − ⟨ℓᵢ(uᵢ)⟩_loc²`. -/
theorem hasDerivAt_localised_frame_energyVar (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) (i : Fin d) :
    HasDerivAt (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) *
          anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) -
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) *
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)))
      (-(_root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
            (anharmonicPotential (lam i) (alpha i) (gamma i) x *
              anharmonicPotential (lam i) (alpha i) (gamma i) x)) -
        3 * _root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
            anharmonicPotential (lam i) (alpha i) (gamma i) x) *
          _root_.Laplace.gibbsExpectation
            (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
            (anharmonicPotential (lam i) (alpha i) (gamma i)) +
        2 * _root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 3)) t := by
  have ht2 := half_pos ht
  have hcont : Continuous (anharmonicPotential (lam i) (alpha i) (gamma i)) := by
    unfold anharmonicPotential; fun_prop
  have h2 := hasDerivAt_localised_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i
    (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
      anharmonicPotential (lam i) (alpha i) (gamma i) x) (hcont.mul hcont)
    (fun k => integrable_energy_energySq_coord hlam hgamma hdisc k i ht2)
    (integrable_energySq_coord_alone hlam hgamma hdisc i ht2)
  have h1 := hasDerivAt_localised_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i
    (anharmonicPotential (lam i) (alpha i) (gamma i)) hcont
    (fun k => integrable_energy_energy_coord hlam hgamma hdisc k i ht2)
    (integrable_energy_coord_alone hlam hgamma hdisc i ht2)
  refine (h2.sub (h1.mul h1)).congr_deriv ?_
  rw [localisedCovK_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i
      (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
        anharmonicPotential (lam i) (alpha i) (gamma i) x) (hcont.mul hcont)
      (fun k => integrable_energy_energySq_locFamily hlam hgamma hdisc hg _ ht k i),
    localisedCovK_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i
      (anharmonicPotential (lam i) (alpha i) (gamma i)) hcont
      (fun k => integrable_energy_energy_locFamily hlam hgamma hdisc hg _ ht k i),
    localised_frame_fun_expectation hlam hgamma hdisc hQ c w₀ hg ht i
      (anharmonicPotential (lam i) (alpha i) (gamma i)) hcont]
  unfold _root_.Laplace.gibbsCov
  ring

/-- `Var_loc(L∘A)(s) = ∑ᵢ (⟨ℓᵢ(uᵢ)²⟩_loc − ⟨ℓᵢ(uᵢ)⟩_loc²)` for `s > 0`. -/
theorem localisedVar_energy_eq_frame_sum (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {s : ℝ} (hs : 0 < s) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) =
      ∑ i, (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) *
          anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) -
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) *
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i))) := by
  rw [localisedVar_energy_eq_sum hlam hgamma hdisc hQ c w₀ hg hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcont : Continuous (anharmonicPotential (lam i) (alpha i) (gamma i)) := by
    unfold anharmonicPotential; fun_prop
  rw [localised_frame_fun_expectation hlam hgamma hdisc hQ c w₀ hg hs i
      (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
        anharmonicPotential (lam i) (alpha i) (gamma i) x) (hcont.mul hcont),
    localised_frame_fun_expectation hlam hgamma hdisc hQ c w₀ hg hs i
      (anharmonicPotential (lam i) (alpha i) (gamma i)) hcont]
  unfold _root_.Laplace.gibbsCov
  ring

/-- **The exact second temperature derivative**: `d/ds (−Var_loc(L∘A))(s) = ∑ᵢ κ₃,loc,ᵢ(t)` — i.e.
`∂ₜ² ⟨L∘A⟩_loc = −∂ₜ Var_loc(L∘A) = ∑ᵢ κ₃,ᵢ`. -/
theorem hasDerivAt_localised_energy_deriv (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g
        w₀ s)
        s (rotatedAnharmonic Q c lam alpha gamma))
      (∑ i, (_root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
            (anharmonicPotential (lam i) (alpha i) (gamma i) x *
              anharmonicPotential (lam i) (alpha i) (gamma i) x)) -
        3 * _root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
            anharmonicPotential (lam i) (alpha i) (gamma i) x) *
          _root_.Laplace.gibbsExpectation
            (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
            (anharmonicPotential (lam i) (alpha i) (gamma i)) +
        2 * _root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 3)) t := by
  have hderiv : (deriv fun s =>
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (rotatedAnharmonic Q c lam alpha gamma)) =ᶠ[𝓝 t]
      fun s => -∑ i, (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) *
          anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) -
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) *
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i))) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => by
      rw [(hasDerivAt_localised_energy hlam hgamma hdisc hQ c w₀ hg hs).deriv,
        localisedVar_energy_eq_frame_sum hlam hgamma hdisc hQ c w₀ hg hs]
  have h : HasDerivAt (fun s => ∑ i,
      (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) *
          anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) -
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) *
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i))))
      (∑ i, -(_root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
            (anharmonicPotential (lam i) (alpha i) (gamma i) x *
              anharmonicPotential (lam i) (alpha i) (gamma i) x)) -
        3 * _root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
            anharmonicPotential (lam i) (alpha i) (gamma i) x) *
          _root_.Laplace.gibbsExpectation
            (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
            (anharmonicPotential (lam i) (alpha i) (gamma i)) +
        2 * _root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 3)) t :=
    HasDerivAt.fun_sum fun i _ => hasDerivAt_localised_frame_energyVar hlam hgamma hdisc hQ c w₀ hg
        ht i
  refine (h.neg.congr_of_eventuallyEq hderiv).congr_deriv ?_
  rw [Finset.sum_neg_distrib, neg_neg]

/-- **The LLC governs the second temperature derivative**: `|t³ ∂ₜ²⟨L∘A⟩_loc − d| ≤ K/t`, i.e.
`∂ₜ²⟨L∘A⟩_loc = −∂ₜ Var_loc(L∘A) = d/t³ + O(t⁻⁴)` — the third cumulant `2·(d/2)/t³` of a
`Gamma(d/2, t)` law. -/
theorem localisedEnergy_deriv2_leading (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * deriv (deriv fun s =>
          gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
            (rotatedAnharmonic Q c lam alpha gamma)) t - (d : ℝ)| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div (fun _ : Fin d => (1 : ℝ))
    (fun i t => t ^ 3 * (_root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
          (anharmonicPotential (lam i) (alpha i) (gamma i) x *
            anharmonicPotential (lam i) (alpha i) (gamma i) x)) -
      3 * _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
          anharmonicPotential (lam i) (alpha i) (gamma i) x) *
        _root_.Laplace.gibbsExpectation
          (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) +
      2 * _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 3) - 1)
    (fun i => locEnergyCum3_leading (hlam i) (hgamma i) (hdisc i) hg (x₀ := affineFrame Q c w₀ i))
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [(hasDerivAt_localised_energy_deriv hlam hgamma hdisc hQ c w₀ hg ht0).deriv]
  have key : ∀ (F : Fin d → ℝ), t ^ 3 * ∑ i, F i - (d : ℝ) = ∑ i, (1 : ℝ) * (t ^ 3 * F i - 1) := by
    intro F
    simp only [one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [key]
  exact h ht

end Multi

end Laplace.Multi
