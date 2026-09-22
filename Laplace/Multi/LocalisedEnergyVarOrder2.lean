/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedEnergyCumulant3

/-!
# The second-order localised energy variance

Per frame coordinate of E2's exact localised measure, through the Stein–covariance reduction
(`LocalisedDerivative`) and the landed moment rates (with the signed seventh and eighth-moment
bounds of `LocalisedEnergyCumulant3`):

`t² Cov_loc[ℓ, x³] = C₃'/t + O(t⁻²)`, `t² Cov_loc[ℓ, x⁴] = 6/(λ²t) + O(t⁻²)`, and
`t² Var_loc(ℓ) = ½ + 2e₁/t + O(t⁻²)` — the variance's second-order coefficient is exactly twice
the energy's first correction `e₁` (`LocalisedLLCCoeff`).

On E2: `−∂ₜ⟨L∘A⟩_loc = Var_loc(L∘A) = d/(2t²) + 2(∑ᵢ e₁ᵢ)/t³ + O(t⁻⁴)`, the coefficientwise
derivative of `t⟨L∘A⟩_loc = d/2 + ∑e₁/t + O(t⁻²)` established from moments; and against the
Gaussian trace prediction `P(t) = ½tr(HS(t))`, `t³(Var_loc(L∘A) + P'(t)) → 2C₁`, twice the
invariant discrepancy coefficient of `LocalisedEnergyInvariant`.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section Rates

theorem bound_of_rate {X c K t : ℝ} (ht1 : 1 ≤ t) (hK : 0 ≤ K) (h : |X - c| ≤ K / t) :
    |X| ≤ |c| + K := by
  have h1 := abs_sub_abs_le_abs_sub X c
  have h2 : K / t ≤ K := div_le_self hK ht1
  linarith

theorem bound_of_rate2 {X c c' K t : ℝ} (ht1 : 1 ≤ t) (hK : 0 ≤ K)
    (h : |X - c - c' / t| ≤ K / t ^ 2) : |X| ≤ |c| + (|c'| + K) :=
  bound_of_rate ht1 (by positivity) (order2_to_order1 ht1 hK h)

theorem prod_div_sq_bound {t X Y BX BY : ℝ} (ht : 0 < t) (hX : |X| ≤ BX) (hY : |Y| ≤ BY) :
    |X * Y / t ^ 2| ≤ BX * BY / t ^ 2 := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), abs_mul]
  exact div_le_div_of_nonneg_right
    (mul_le_mul hX hY (abs_nonneg _) ((abs_nonneg _).trans hX)) (by positivity)

theorem scale_down_sq {t Z K : ℝ} (ht : 0 < t) (h : |t ^ 4 * Z| ≤ K) : |t ^ 2 * Z| ≤ K / t ^ 2 := by
  have e : t ^ 2 * Z = t ^ 4 * Z / t ^ 2 := by
    rw [eq_div_iff (by positivity)]
    ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem scale_down_one {t Z K : ℝ} (ht : 0 < t) (h : |t ^ 3 * Z| ≤ K) : |t * Z| ≤ K / t ^ 2 := by
  have e : t * Z = t ^ 3 * Z / t ^ 2 := by
    rw [eq_div_iff (by positivity)]
    ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem rate_shift_one {t Z c K : ℝ} (ht : 0 < t) (h : |t ^ 2 * Z - c| ≤ K / t) :
    |t * Z - c / t| ≤ K / t ^ 2 := by
  have ht' : t ≠ 0 := ht.ne'
  have e : t * Z - c / t = (t ^ 2 * Z - c) / t := by
    field_simp
  rw [e, abs_div, abs_of_pos ht]
  calc |t ^ 2 * Z - c| / t ≤ K / t / t := div_le_div_of_nonneg_right h ht.le
    _ = K / t ^ 2 := by ring

theorem rate_shift_two {t Z c K : ℝ} (ht : 0 < t) (h : |t ^ 3 * Z - c| ≤ K / t) :
    |t ^ 2 * Z - c / t| ≤ K / t ^ 2 := by
  have ht' : t ≠ 0 := ht.ne'
  have e : t ^ 2 * Z - c / t = (t ^ 3 * Z - c) / t := by
    field_simp
  rw [e, abs_div, abs_of_pos ht]
  calc |t ^ 3 * Z - c| / t ≤ K / t / t := div_le_div_of_nonneg_right h ht.le
    _ = K / t ^ 2 := by ring

end Rates

section OneD

variable {lam alpha gamma g x₀ : ℝ} (hlam : 0 < lam) (hgamma : 0 < gamma)
  (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `ℓ · xᵏ` is integrable against the localised measure. -/
theorem integrable_energy_pow_locPotential1 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (fun x : ℝ => anharmonicPotential lam alpha gamma x * x ^ k *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := by
  have hp : ∀ m, Integrable (fun x : ℝ => x ^ m *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    integrable_pow_locPotential1 hlam hgamma hdisc hg ht
  refine ((((hp (k + 2)).const_mul (lam / 2)).add ((hp (k + 3)).const_mul (alpha / 6))).add
    ((hp (k + 4)).const_mul (gamma / 24))).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

/-- `Var_loc(ℓ) = (λ/2)Cov[ℓ, x²] + (α/6)Cov[ℓ, x³] + (γ/24)Cov[ℓ, x⁴]`. -/
theorem locEnergyVar_split (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (anharmonicPotential lam alpha gamma) =
      lam / 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) +
        (alpha / 6 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x ^ 3) +
        gamma / 24 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x ^ 4)) := by
  have hp : ∀ m, Integrable (fun x : ℝ => x ^ m *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    integrable_pow_locPotential1 hlam hgamma hdisc hg ht
  have hc : ∀ (a : ℝ) (m : ℕ), Integrable (fun x : ℝ => a * x ^ m *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := fun a m =>
    ((hp m).const_mul a).congr (Eventually.of_forall fun x => by ring)
  have hℓc : ∀ (a : ℝ) (m : ℕ), Integrable (fun x : ℝ =>
      anharmonicPotential lam alpha gamma x * (a * x ^ m) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := fun a m =>
    ((integrable_energy_pow_locPotential1 hlam hgamma hdisc hg ht m).const_mul a).congr
      (Eventually.of_forall fun x => by ring)
  have h34 : Integrable (fun x : ℝ => (alpha / 6 * x ^ 3 + gamma / 24 * x ^ 4) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (alpha / 6) 3).add (hc (gamma / 24) 4)).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have hℓ34 : Integrable (fun x : ℝ => anharmonicPotential lam alpha gamma x *
      (alpha / 6 * x ^ 3 + gamma / 24 * x ^ 4) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hℓc (alpha / 6) 3).add (hℓc (gamma / 24) 4)).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have e : anharmonicPotential lam alpha gamma =
      fun x => lam / 2 * x ^ 2 + (alpha / 6 * x ^ 3 + gamma / 24 * x ^ 4) := by
    funext x
    simp only [anharmonicPotential]
    ring
  calc _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (anharmonicPotential lam alpha gamma) =
      _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma)
        (fun x => lam / 2 * x ^ 2 + (alpha / 6 * x ^ 3 + gamma / 24 * x ^ 4)) := by
        congr 1
    _ = _ := by
        rw [_root_.Laplace.gibbsCov_add_right _ _ _ _ _ (hc _ 2) h34 (hℓc _ 2) hℓ34,
          _root_.Laplace.gibbsCov_add_right _ _ _ _ _ (hc _ 3) (hc _ 4) (hℓc _ 3) (hℓc _ 4),
          _root_.Laplace.gibbsCov_smul_right, _root_.Laplace.gibbsCov_smul_right,
          _root_.Laplace.gibbsCov_smul_right]

/-- **`t²Cov_loc[ℓ, x³]` to second order**: `|t²Cov[ℓ, x³] − C₃'/t| ≤ K/t²`,
`C₃' = (3/2)c₃ − (α/12)(15/λ³) + (a/2)(3/λ²)`. -/
theorem locCovK_cubic_order2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x ^ 3) -
        (3 / 2 * locThirdCoeff lam alpha g x₀ - alpha / 12 * (15 / lam ^ 3) +
          g * x₀ / 2 * (3 / lam ^ 2)) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := locMean_loc_order2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locSecondMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locThirdMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := locFifthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := locSixthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₇, T₇, hK₇, hT₇, h₇⟩ := locSeventhMoment_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨3 / 2 * K₃ + |alpha| / 12 * (K₆ + (|locThirdCoeff lam alpha g x₀| + K₃) *
      (|locThirdCoeff lam alpha g x₀| + K₃)) +
    gamma / 24 * (K₇ + (|3 / lam ^ 2| + K₄) * (|locThirdCoeff lam alpha g x₀| + K₃)) +
    g / 2 * ((|locFifthCoeff lam alpha g x₀| + K₅) +
      (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) *
        (|locThirdCoeff lam alpha g x₀| + K₃)) +
    |g * x₀| / 2 * (K₄ + (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| +
      (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) * (|locThirdCoeff lam alpha g x₀| + K₃)),
    T₁ + T₂ + T₃ + T₄ + T₅ + T₆ + T₇, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have ht' : t ≠ 0 := ht0.ne'
  rw [stein_loc_cov_reduction hlam hgamma hdisc hg ht0 (x₀ := x₀) 3]
  have e33 : (fun x : ℝ => x ^ 3 * x ^ 3) = fun x => x ^ 6 := by funext x; ring
  have e43 : (fun x : ℝ => x ^ 4 * x ^ 3) = fun x => x ^ 7 := by funext x; ring
  have e23 : (fun x : ℝ => x ^ 2 * x ^ 3) = fun x => x ^ 5 := by funext x; ring
  have e13 : (fun x : ℝ => x * x ^ 3) = fun x => x ^ 4 := by funext x; ring
  simp only [_root_.Laplace.gibbsCov, e33, e43, e23, e13, Nat.cast_ofNat]
  set m₁ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x)
    with hm₁
  set m₂ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 2) with hm₂
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
  have hB₁ : |t * m₁| ≤ |-alpha / (2 * lam ^ 2) + g * x₀ / lam| +
      (|meanLocCoeff2 lam alpha gamma g x₀| + K₁) :=
    bound_of_rate2 ht1 hK₁ (h₁ (t := t) (by linarith))
  have hB₂ : |t * m₂| ≤ |1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂) :=
    bound_of_rate2 ht1 hK₂ (h₂ (t := t) (by linarith))
  have hB₃ : |t ^ 2 * m₃| ≤ |locThirdCoeff lam alpha g x₀| + K₃ :=
    bound_of_rate ht1 hK₃ (h₃ (t := t) (by linarith))
  have hB₄ : |t ^ 2 * m₄| ≤ |3 / lam ^ 2| + K₄ := bound_of_rate ht1 hK₄ (h₄ (t := t) (by linarith))
  have hB₅ : |t ^ 3 * m₅| ≤ |locFifthCoeff lam alpha g x₀| + K₅ :=
    bound_of_rate ht1 hK₅ (h₅ (t := t) (by linarith))
  have b1 : |t * m₃ - locThirdCoeff lam alpha g x₀ / t| ≤ K₃ / t ^ 2 :=
    rate_shift_one ht0 (h₃ (t := t) (by linarith))
  have b2 : |t ^ 2 * m₆ - 15 / lam ^ 3 / t| ≤ K₆ / t ^ 2 :=
    rate_shift_two ht0 (h₆ (t := t) (by linarith))
  have b3 := prod_div_sq_bound ht0 hB₃ hB₃
  have b4 : |t ^ 2 * m₇| ≤ K₇ / t ^ 2 := scale_down_sq ht0 (h₇ (t := t) (by linarith))
  have b5 := prod_div_sq_bound ht0 hB₄ hB₃
  have b6 : |t * m₅| ≤ (|locFifthCoeff lam alpha g x₀| + K₅) / t ^ 2 := scale_down_one ht0 hB₅
  have b7 := prod_div_sq_bound ht0 hB₂ hB₃
  have b8 : |t * m₄ - 3 / lam ^ 2 / t| ≤ K₄ / t ^ 2 := rate_shift_one ht0 (h₄ (t := t) (by
      linarith))
  have b9 := prod_div_sq_bound ht0 hB₁ hB₃
  have key : (3 : ℝ) / 2 * (t * m₃) - alpha / 12 * (t ^ 2 * (m₆ - m₃ * m₃)) -
      gamma / 24 * (t ^ 2 * (m₇ - m₄ * m₃)) - g / 2 * (t * (m₅ - m₂ * m₃)) +
      g * x₀ / 2 * (t * (m₄ - m₁ * m₃)) -
      (3 / 2 * locThirdCoeff lam alpha g x₀ - alpha / 12 * (15 / lam ^ 3) +
        g * x₀ / 2 * (3 / lam ^ 2)) / t =
      3 / 2 * (t * m₃ - locThirdCoeff lam alpha g x₀ / t) -
      alpha / 12 * ((t ^ 2 * m₆ - 15 / lam ^ 3 / t) - t ^ 2 * m₃ * (t ^ 2 * m₃) / t ^ 2) -
      gamma / 24 * (t ^ 2 * m₇ - t ^ 2 * m₄ * (t ^ 2 * m₃) / t ^ 2) -
      g / 2 * (t * m₅ - t * m₂ * (t ^ 2 * m₃) / t ^ 2) +
      g * x₀ / 2 * ((t * m₄ - 3 / lam ^ 2 / t) - t * m₁ * (t ^ 2 * m₃) / t ^ 2) := by
    field_simp
    ring
  rw [key]
  have hA : |3 / 2 * (t * m₃ - locThirdCoeff lam alpha g x₀ / t)| ≤ 3 / 2 * (K₃ / t ^ 2) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    exact mul_le_mul_of_nonneg_left b1 (by norm_num)
  have hB : |alpha / 12 * ((t ^ 2 * m₆ - 15 / lam ^ 3 / t) - t ^ 2 * m₃ * (t ^ 2 * m₃) / t ^ 2)| ≤
      |alpha| / 12 * ((K₆ + (|locThirdCoeff lam alpha g x₀| + K₃) *
        (|locThirdCoeff lam alpha g x₀| + K₃)) / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ |t ^ 2 * m₆ - 15 / lam ^ 3 / t| + |t ^ 2 * m₃ * (t ^ 2 * m₃) / t ^ 2| := abs_sub _ _
      _ ≤ K₆ / t ^ 2 + (|locThirdCoeff lam alpha g x₀| + K₃) *
          (|locThirdCoeff lam alpha g x₀| + K₃) / t ^ 2 := add_le_add b2 b3
      _ = _ := by ring
  have hC : |gamma / 24 * (t ^ 2 * m₇ - t ^ 2 * m₄ * (t ^ 2 * m₃) / t ^ 2)| ≤
      gamma / 24 * ((K₇ + (|3 / lam ^ 2| + K₄) * (|locThirdCoeff lam alpha g x₀| + K₃)) / t ^ 2) :=
          by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 24)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ |t ^ 2 * m₇| + |t ^ 2 * m₄ * (t ^ 2 * m₃) / t ^ 2| := abs_sub _ _
      _ ≤ K₇ / t ^ 2 + (|3 / lam ^ 2| + K₄) * (|locThirdCoeff lam alpha g x₀| + K₃) / t ^ 2 :=
          add_le_add b4 b5
      _ = _ := by ring
  have hD : |g / 2 * (t * m₅ - t * m₂ * (t ^ 2 * m₃) / t ^ 2)| ≤
      g / 2 * (((|locFifthCoeff lam alpha g x₀| + K₅) +
        (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) *
          (|locThirdCoeff lam alpha g x₀| + K₃)) / t ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ |t * m₅| + |t * m₂ * (t ^ 2 * m₃) / t ^ 2| := abs_sub _ _
      _ ≤ (|locFifthCoeff lam alpha g x₀| + K₅) / t ^ 2 +
          (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) *
            (|locThirdCoeff lam alpha g x₀| + K₃) / t ^ 2 := add_le_add b6 b7
      _ = _ := by ring
  have hE : |g * x₀ / 2 * ((t * m₄ - 3 / lam ^ 2 / t) - t * m₁ * (t ^ 2 * m₃) / t ^ 2)| ≤
      |g * x₀| / 2 * ((K₄ + (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| +
        (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) * (|locThirdCoeff lam alpha g x₀| + K₃)) /
        t ^ 2) := by
    rw [abs_mul, abs_div, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ |t * m₄ - 3 / lam ^ 2 / t| + |t * m₁ * (t ^ 2 * m₃) / t ^ 2| := abs_sub _ _
      _ ≤ K₄ / t ^ 2 + (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| +
          (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) *
            (|locThirdCoeff lam alpha g x₀| + K₃) / t ^ 2 := add_le_add b8 b9
      _ = _ := by ring
  have hsum := abs_add_le (3 / 2 * (t * m₃ - locThirdCoeff lam alpha g x₀ / t) -
    alpha / 12 * ((t ^ 2 * m₆ - 15 / lam ^ 3 / t) - t ^ 2 * m₃ * (t ^ 2 * m₃) / t ^ 2) -
    gamma / 24 * (t ^ 2 * m₇ - t ^ 2 * m₄ * (t ^ 2 * m₃) / t ^ 2) -
    g / 2 * (t * m₅ - t * m₂ * (t ^ 2 * m₃) / t ^ 2))
    (g * x₀ / 2 * ((t * m₄ - 3 / lam ^ 2 / t) - t * m₁ * (t ^ 2 * m₃) / t ^ 2))
  have hs1 := abs_sub (3 / 2 * (t * m₃ - locThirdCoeff lam alpha g x₀ / t) -
    alpha / 12 * ((t ^ 2 * m₆ - 15 / lam ^ 3 / t) - t ^ 2 * m₃ * (t ^ 2 * m₃) / t ^ 2) -
    gamma / 24 * (t ^ 2 * m₇ - t ^ 2 * m₄ * (t ^ 2 * m₃) / t ^ 2))
    (g / 2 * (t * m₅ - t * m₂ * (t ^ 2 * m₃) / t ^ 2))
  have hs2 := abs_sub (3 / 2 * (t * m₃ - locThirdCoeff lam alpha g x₀ / t) -
    alpha / 12 * ((t ^ 2 * m₆ - 15 / lam ^ 3 / t) - t ^ 2 * m₃ * (t ^ 2 * m₃) / t ^ 2))
    (gamma / 24 * (t ^ 2 * m₇ - t ^ 2 * m₄ * (t ^ 2 * m₃) / t ^ 2))
  have hs3 := abs_sub (3 / 2 * (t * m₃ - locThirdCoeff lam alpha g x₀ / t))
    (alpha / 12 * ((t ^ 2 * m₆ - 15 / lam ^ 3 / t) - t ^ 2 * m₃ * (t ^ 2 * m₃) / t ^ 2))
  have hfin : (3 / 2 * K₃ + |alpha| / 12 * (K₆ + (|locThirdCoeff lam alpha g x₀| + K₃) *
      (|locThirdCoeff lam alpha g x₀| + K₃)) +
    gamma / 24 * (K₇ + (|3 / lam ^ 2| + K₄) * (|locThirdCoeff lam alpha g x₀| + K₃)) +
    g / 2 * ((|locFifthCoeff lam alpha g x₀| + K₅) +
      (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) *
        (|locThirdCoeff lam alpha g x₀| + K₃)) +
    |g * x₀| / 2 * (K₄ + (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| +
      (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) * (|locThirdCoeff lam alpha g x₀| + K₃))) /
      t ^ 2 =
    3 / 2 * (K₃ / t ^ 2) + |alpha| / 12 * ((K₆ + (|locThirdCoeff lam alpha g x₀| + K₃) *
      (|locThirdCoeff lam alpha g x₀| + K₃)) / t ^ 2) +
    gamma / 24 * ((K₇ + (|3 / lam ^ 2| + K₄) * (|locThirdCoeff lam alpha g x₀| + K₃)) / t ^ 2) +
    g / 2 * (((|locFifthCoeff lam alpha g x₀| + K₅) +
      (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) *
        (|locThirdCoeff lam alpha g x₀| + K₃)) / t ^ 2) +
    |g * x₀| / 2 * ((K₄ + (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| +
      (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) * (|locThirdCoeff lam alpha g x₀| + K₃)) /
      t ^ 2) := by ring
  rw [hfin]
  linarith [hA, hB, hC, hD, hE, hsum, hs1, hs2, hs3]

/-- **`t²Cov_loc[ℓ, x⁴]` to second order**: `|t²Cov[ℓ, x⁴] − 6/(λ²t)| ≤ K/t²`. -/
theorem locCovK_quartic_order2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x ^ 4) - 6 / lam ^ 2 / t| ≤ K / t ^ 2 :=
              by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := locMean_loc_order2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locSecondMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locThirdMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := locFifthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := locSixthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₇, T₇, hK₇, hT₇, h₇⟩ := locSeventhMoment_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₈, T₈, hK₈, hT₈, h₈⟩ := locEven_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀) 4 le_rfl
  refine ⟨4 / 2 * K₄ + |alpha| / 12 * (K₇ + (|locThirdCoeff lam alpha g x₀| + K₃) *
      (|3 / lam ^ 2| + K₄)) +
    gamma / 24 * (K₈ + (|3 / lam ^ 2| + K₄) * (|3 / lam ^ 2| + K₄)) +
    g / 2 * ((|15 / lam ^ 3| + K₆) +
      (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) * (|3 / lam ^ 2| + K₄)) +
    |g * x₀| / 2 * ((|locFifthCoeff lam alpha g x₀| + K₅) +
      (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| + (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) *
        (|3 / lam ^ 2| + K₄)),
    T₁ + T₂ + T₃ + T₄ + T₅ + T₆ + T₇ + T₈, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have ht' : t ≠ 0 := ht0.ne'
  rw [stein_loc_cov_reduction hlam hgamma hdisc hg ht0 (x₀ := x₀) 4]
  have e34 : (fun x : ℝ => x ^ 3 * x ^ 4) = fun x => x ^ 7 := by funext x; ring
  have e44 : (fun x : ℝ => x ^ 4 * x ^ 4) = fun x => x ^ 8 := by funext x; ring
  have e24 : (fun x : ℝ => x ^ 2 * x ^ 4) = fun x => x ^ 6 := by funext x; ring
  have e14 : (fun x : ℝ => x * x ^ 4) = fun x => x ^ 5 := by funext x; ring
  simp only [_root_.Laplace.gibbsCov, e34, e44, e24, e14, Nat.cast_ofNat]
  set m₁ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x)
    with hm₁
  set m₂ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 2) with hm₂
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
  set m₈ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 8) with hm₈
  have hB₁ : |t * m₁| ≤ |-alpha / (2 * lam ^ 2) + g * x₀ / lam| +
      (|meanLocCoeff2 lam alpha gamma g x₀| + K₁) :=
    bound_of_rate2 ht1 hK₁ (h₁ (t := t) (by linarith))
  have hB₂ : |t * m₂| ≤ |1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂) :=
    bound_of_rate2 ht1 hK₂ (h₂ (t := t) (by linarith))
  have hB₃ : |t ^ 2 * m₃| ≤ |locThirdCoeff lam alpha g x₀| + K₃ :=
    bound_of_rate ht1 hK₃ (h₃ (t := t) (by linarith))
  have hB₄ : |t ^ 2 * m₄| ≤ |3 / lam ^ 2| + K₄ := bound_of_rate ht1 hK₄ (h₄ (t := t) (by linarith))
  have hB₅ : |t ^ 3 * m₅| ≤ |locFifthCoeff lam alpha g x₀| + K₅ :=
    bound_of_rate ht1 hK₅ (h₅ (t := t) (by linarith))
  have hB₆ : |t ^ 3 * m₆| ≤ |15 / lam ^ 3| + K₆ := bound_of_rate ht1 hK₆ (h₆ (t := t) (by linarith))
  have b1 : |t * m₄ - 3 / lam ^ 2 / t| ≤ K₄ / t ^ 2 := rate_shift_one ht0 (h₄ (t := t) (by
      linarith))
  have b2 : |t ^ 2 * m₇| ≤ K₇ / t ^ 2 := scale_down_sq ht0 (h₇ (t := t) (by linarith))
  have b3 := prod_div_sq_bound ht0 hB₃ hB₄
  have b4 : |t ^ 2 * m₈| ≤ K₈ / t ^ 2 := scale_down_sq ht0 (h₈ (t := t) (by linarith))
  have b5 := prod_div_sq_bound ht0 hB₄ hB₄
  have b6 : |t * m₆| ≤ (|15 / lam ^ 3| + K₆) / t ^ 2 := scale_down_one ht0 hB₆
  have b7 := prod_div_sq_bound ht0 hB₂ hB₄
  have b8 : |t * m₅| ≤ (|locFifthCoeff lam alpha g x₀| + K₅) / t ^ 2 := scale_down_one ht0 hB₅
  have b9 := prod_div_sq_bound ht0 hB₁ hB₄
  have key : (4 : ℝ) / 2 * (t * m₄) - alpha / 12 * (t ^ 2 * (m₇ - m₃ * m₄)) -
      gamma / 24 * (t ^ 2 * (m₈ - m₄ * m₄)) - g / 2 * (t * (m₆ - m₂ * m₄)) +
      g * x₀ / 2 * (t * (m₅ - m₁ * m₄)) - 6 / lam ^ 2 / t =
      4 / 2 * (t * m₄ - 3 / lam ^ 2 / t) -
      alpha / 12 * (t ^ 2 * m₇ - t ^ 2 * m₃ * (t ^ 2 * m₄) / t ^ 2) -
      gamma / 24 * (t ^ 2 * m₈ - t ^ 2 * m₄ * (t ^ 2 * m₄) / t ^ 2) -
      g / 2 * (t * m₆ - t * m₂ * (t ^ 2 * m₄) / t ^ 2) +
      g * x₀ / 2 * (t * m₅ - t * m₁ * (t ^ 2 * m₄) / t ^ 2) := by
    field_simp
    ring
  rw [key]
  have hA : |4 / 2 * (t * m₄ - 3 / lam ^ 2 / t)| ≤ 4 / 2 * (K₄ / t ^ 2) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 2)]
    exact mul_le_mul_of_nonneg_left b1 (by norm_num)
  have hB : |alpha / 12 * (t ^ 2 * m₇ - t ^ 2 * m₃ * (t ^ 2 * m₄) / t ^ 2)| ≤
      |alpha| / 12 * ((K₇ + (|locThirdCoeff lam alpha g x₀| + K₃) * (|3 / lam ^ 2| + K₄)) / t ^
          2) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ |t ^ 2 * m₇| + |t ^ 2 * m₃ * (t ^ 2 * m₄) / t ^ 2| := abs_sub _ _
      _ ≤ K₇ / t ^ 2 + (|locThirdCoeff lam alpha g x₀| + K₃) * (|3 / lam ^ 2| + K₄) / t ^ 2 :=
          add_le_add b2 b3
      _ = _ := by ring
  have hC : |gamma / 24 * (t ^ 2 * m₈ - t ^ 2 * m₄ * (t ^ 2 * m₄) / t ^ 2)| ≤
      gamma / 24 * ((K₈ + (|3 / lam ^ 2| + K₄) * (|3 / lam ^ 2| + K₄)) / t ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 24)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ |t ^ 2 * m₈| + |t ^ 2 * m₄ * (t ^ 2 * m₄) / t ^ 2| := abs_sub _ _
      _ ≤ K₈ / t ^ 2 + (|3 / lam ^ 2| + K₄) * (|3 / lam ^ 2| + K₄) / t ^ 2 := add_le_add b4 b5
      _ = _ := by ring
  have hD : |g / 2 * (t * m₆ - t * m₂ * (t ^ 2 * m₄) / t ^ 2)| ≤
      g / 2 * (((|15 / lam ^ 3| + K₆) +
        (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) * (|3 / lam ^ 2| + K₄)) /
        t ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ |t * m₆| + |t * m₂ * (t ^ 2 * m₄) / t ^ 2| := abs_sub _ _
      _ ≤ (|15 / lam ^ 3| + K₆) / t ^ 2 +
          (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) * (|3 / lam ^ 2| + K₄) /
            t ^ 2 := add_le_add b6 b7
      _ = _ := by ring
  have hE : |g * x₀ / 2 * (t * m₅ - t * m₁ * (t ^ 2 * m₄) / t ^ 2)| ≤
      |g * x₀| / 2 * (((|locFifthCoeff lam alpha g x₀| + K₅) +
        (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| + (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) *
          (|3 / lam ^ 2| + K₄)) / t ^ 2) := by
    rw [abs_mul, abs_div, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ |t * m₅| + |t * m₁ * (t ^ 2 * m₄) / t ^ 2| := abs_sub _ _
      _ ≤ (|locFifthCoeff lam alpha g x₀| + K₅) / t ^ 2 +
          (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| + (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) *
            (|3 / lam ^ 2| + K₄) / t ^ 2 := add_le_add b8 b9
      _ = _ := by ring
  have hsum := abs_add_le (4 / 2 * (t * m₄ - 3 / lam ^ 2 / t) -
    alpha / 12 * (t ^ 2 * m₇ - t ^ 2 * m₃ * (t ^ 2 * m₄) / t ^ 2) -
    gamma / 24 * (t ^ 2 * m₈ - t ^ 2 * m₄ * (t ^ 2 * m₄) / t ^ 2) -
    g / 2 * (t * m₆ - t * m₂ * (t ^ 2 * m₄) / t ^ 2))
    (g * x₀ / 2 * (t * m₅ - t * m₁ * (t ^ 2 * m₄) / t ^ 2))
  have hs1 := abs_sub (4 / 2 * (t * m₄ - 3 / lam ^ 2 / t) -
    alpha / 12 * (t ^ 2 * m₇ - t ^ 2 * m₃ * (t ^ 2 * m₄) / t ^ 2) -
    gamma / 24 * (t ^ 2 * m₈ - t ^ 2 * m₄ * (t ^ 2 * m₄) / t ^ 2))
    (g / 2 * (t * m₆ - t * m₂ * (t ^ 2 * m₄) / t ^ 2))
  have hs2 := abs_sub (4 / 2 * (t * m₄ - 3 / lam ^ 2 / t) -
    alpha / 12 * (t ^ 2 * m₇ - t ^ 2 * m₃ * (t ^ 2 * m₄) / t ^ 2))
    (gamma / 24 * (t ^ 2 * m₈ - t ^ 2 * m₄ * (t ^ 2 * m₄) / t ^ 2))
  have hs3 := abs_sub (4 / 2 * (t * m₄ - 3 / lam ^ 2 / t))
    (alpha / 12 * (t ^ 2 * m₇ - t ^ 2 * m₃ * (t ^ 2 * m₄) / t ^ 2))
  have hfin : (4 / 2 * K₄ + |alpha| / 12 * (K₇ + (|locThirdCoeff lam alpha g x₀| + K₃) *
      (|3 / lam ^ 2| + K₄)) +
    gamma / 24 * (K₈ + (|3 / lam ^ 2| + K₄) * (|3 / lam ^ 2| + K₄)) +
    g / 2 * ((|15 / lam ^ 3| + K₆) +
      (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) * (|3 / lam ^ 2| + K₄)) +
    |g * x₀| / 2 * ((|locFifthCoeff lam alpha g x₀| + K₅) +
      (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| + (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) *
        (|3 / lam ^ 2| + K₄))) / t ^ 2 =
    4 / 2 * (K₄ / t ^ 2) + |alpha| / 12 * ((K₇ + (|locThirdCoeff lam alpha g x₀| + K₃) *
      (|3 / lam ^ 2| + K₄)) / t ^ 2) +
    gamma / 24 * ((K₈ + (|3 / lam ^ 2| + K₄) * (|3 / lam ^ 2| + K₄)) / t ^ 2) +
    g / 2 * (((|15 / lam ^ 3| + K₆) +
      (|1 / lam| + (|locSecondCoeff2 lam alpha gamma g x₀| + K₂)) * (|3 / lam ^ 2| + K₄)) / t ^ 2) +
    |g * x₀| / 2 * (((|locFifthCoeff lam alpha g x₀| + K₅) +
      (|-alpha / (2 * lam ^ 2) + g * x₀ / lam| + (|meanLocCoeff2 lam alpha gamma g x₀| + K₁)) *
        (|3 / lam ^ 2| + K₄)) / t ^ 2) := by ring
  rw [hfin]
  linarith [hA, hB, hC, hD, hE, hsum, hs1, hs2, hs3]

omit hgamma hdisc in
/-- The coefficient identity: `λc₂' + (α/6)C₃' + γ/(4λ²) = 2e₁`. -/
theorem varOrder2_coeff_identity :
    lam * locSecondCoeff2 lam alpha gamma g x₀ +
      alpha / 6 * (3 / 2 * locThirdCoeff lam alpha g x₀ - alpha / 12 * (15 / lam ^ 3) +
        g * x₀ / 2 * (3 / lam ^ 2)) + gamma / 24 * (6 / lam ^ 2) -
      2 * energyLocCoeff1 lam alpha gamma g x₀ = 0 := by
  have hl : lam ≠ 0 := hlam.ne'
  rw [energyLocCoeff1_eq _ _ _ _ _ hlam]
  unfold locSecondCoeff2 locN2 locD1 locP₃ locThirdCoeff
  field_simp
  ring

/-- **The second-order localised energy variance**: `|t² Var_loc(ℓ) − ½ − 2e₁/t| ≤ K/t²` — the
variance's `1/t` coefficient is twice the energy's first correction. -/
theorem locEnergyVar_order2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (anharmonicPotential lam alpha gamma) - 1 / 2 -
        2 * energyLocCoeff1 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := localisedCovK_sq_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locCovK_cubic_order2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locCovK_quartic_order2 hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨lam / 2 * K₂ + (|alpha| / 6 * K₃ + gamma / 24 * K₄), T₂ + T₃ + T₄, by positivity,
    by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have ht' : t ≠ 0 := ht0.ne'
  have e₂ := h₂ (t := t) (by linarith)
  have e₃ := h₃ (t := t) (by linarith)
  have e₄ := h₄ (t := t) (by linarith)
  have hid := varOrder2_coeff_identity hlam (alpha := alpha) (gamma := gamma) (g := g) (x₀ := x₀)
  rw [locEnergyVar_split hlam hgamma hdisc hg ht0]
  have key : t ^ 2 * (lam / 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
      (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) +
      (alpha / 6 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 3) +
      gamma / 24 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 4))) - 1 / 2 -
      2 * energyLocCoeff1 lam alpha gamma g x₀ / t =
      lam / 2 * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) - 1 / lam -
        2 * locSecondCoeff2 lam alpha gamma g x₀ / t) +
      (alpha / 6 * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 3) -
        (3 / 2 * locThirdCoeff lam alpha g x₀ - alpha / 12 * (15 / lam ^ 3) +
          g * x₀ / 2 * (3 / lam ^ 2)) / t) +
      gamma / 24 * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 4) - 6 / lam ^ 2 / t)) := by
    have hhalf : lam / 2 * (1 / lam) = 1 / 2 := by
      have hl : lam ≠ 0 := hlam.ne'
      field_simp
    linear_combination (1 / t) * hid + hhalf
  rw [key]
  have hA : |lam / 2 * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
      (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) - 1 / lam -
      2 * locSecondCoeff2 lam alpha gamma g x₀ / t)| ≤ lam / 2 * (K₂ / t ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam / 2)]
    exact mul_le_mul_of_nonneg_left e₂ (by positivity)
  have hB : |alpha / 6 * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
      (anharmonicPotential lam alpha gamma) (fun x => x ^ 3) -
      (3 / 2 * locThirdCoeff lam alpha g x₀ - alpha / 12 * (15 / lam ^ 3) +
        g * x₀ / 2 * (3 / lam ^ 2)) / t)| ≤ |alpha| / 6 * (K₃ / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact mul_le_mul_of_nonneg_left e₃ (by positivity)
  have hC : |gamma / 24 * (t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
      (anharmonicPotential lam alpha gamma) (fun x => x ^ 4) - 6 / lam ^ 2 / t)| ≤
      gamma / 24 * (K₄ / t ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 24)]
    exact mul_le_mul_of_nonneg_left e₄ (by positivity)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ lam / 2 * (K₂ / t ^ 2) + (|alpha| / 6 * (K₃ / t ^ 2) + gamma / 24 * (K₄ / t ^ 2)) :=
        add_le_add hA ((abs_add_le _ _).trans (add_le_add hB hC))
    _ = _ := by ring

end OneD

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- The Gaussian trace prediction `P(t) = ½tr(HS(t))` as a scalar finite sum, for `t > 0`. -/
theorem tracePrediction_eq (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) :
    1 / 2 * ((Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace =
      1 / 2 * ∑ i, lam i * (1 / (t * lam i + g)) := by
  rw [locS_rot hQ hlam hg ht, trace_mul_conj_diagonal, conj_conj hQ]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.diagonal_apply_eq]

/-- `P'(t) = −½∑ᵢ λᵢ²/(tλᵢ + g)²`. -/
theorem hasDerivAt_tracePrediction (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s => 1 / 2 * ((Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) s).trace)
      (-(1 / 2 * ∑ i, lam i ^ 2 / (t * lam i + g) ^ 2)) t := by
  have heq : (fun s => 1 / 2 * ((Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) s).trace)
      =ᶠ[𝓝 t] fun s => 1 / 2 * ∑ i, lam i * (1 / (s * lam i + g)) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => tracePrediction_eq hQ hlam hg hs
  have h : HasDerivAt (fun s => 1 / 2 * ∑ i, lam i * (1 / (s * lam i + g)))
      (1 / 2 * ∑ i, lam i * (-(lam i) / (t * lam i + g) ^ 2)) t := by
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ => ?_)
    have hd : t * lam i + g ≠ 0 := by have := hlam i; positivity
    have h1 : HasDerivAt (fun s => s * lam i + g) (lam i) t := by
      simpa using ((hasDerivAt_id t).mul_const (lam i)).add_const g
    simp only [one_div]
    exact (h1.inv hd).const_mul _
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Per coordinate, `½λ²t³/(tλ + g)² = t/2 − g/λ + O(1/t)`: exactly
`½λ²t³/(tλ+g)² − t/2 + g/λ = g²(3λt + 2g)/(2λ(tλ+g)²) ≤ g²(3λ + 2g)/(2λ³t)`. -/
theorem tracePrediction_coord_rate {lam g t : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) (ht : 1 ≤ t) :
    |t ^ 3 * (1 / 2 * (lam ^ 2 / (t * lam + g) ^ 2)) - t / 2 + g / lam| ≤
      g ^ 2 * (3 * lam + 2 * g) / (2 * lam ^ 3) / t := by
  have ht0 : 0 < t := by linarith
  have hden : 0 < t * lam + g := by positivity
  have e : t ^ 3 * (1 / 2 * (lam ^ 2 / (t * lam + g) ^ 2)) - t / 2 + g / lam =
      g ^ 2 * (3 * lam * t + 2 * g) / (2 * lam * (t * lam + g) ^ 2) := by
    field_simp
    ring
  rw [e, abs_of_nonneg (by positivity)]
  have h1 : g ^ 2 * (3 * lam * t + 2 * g) / (2 * lam * (t * lam + g) ^ 2) ≤
      g ^ 2 * (3 * lam * t + 2 * g) / (2 * lam * (t * lam) ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
    linarith
  have h2 : g ^ 2 * (3 * lam * t + 2 * g) / (2 * lam * (t * lam) ^ 2) ≤
      g ^ 2 * (t * (3 * lam + 2 * g)) / (2 * lam * (t * lam) ^ 2) := by
    gcongr
    nlinarith
  refine h1.trans (h2.trans (le_of_eq ?_))
  field_simp

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The second-order localised energy variance on E2**:
`|t² Var_loc(L∘A) − d/2 − 2(∑ᵢ e₁ᵢ)/t| ≤ K/t²`. -/
theorem localisedVar_energy_order2 (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) -
        (d : ℝ) / 2 -
        2 * (∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sq (fun _ : Fin d => (1 : ℝ))
    (fun i t => t ^ 2 * _root_.Laplace.gibbsCov
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
      (anharmonicPotential (lam i) (alpha i) (gamma i))
      (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 -
      2 * energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t)
    (fun i => locEnergyVar_order2 (hlam i) (hgamma i) (hdisc i) hg (x₀ := affineFrame Q c w₀ i))
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedVar_energy_eq_sum hlam hgamma hdisc hQ c w₀ hg ht0]
  have key : ∀ (F E : Fin d → ℝ), t ^ 2 * ∑ i, F i - (d : ℝ) / 2 - 2 * (∑ i, E i) / t =
      ∑ i, (1 : ℝ) * (t ^ 2 * F i - 1 / 2 - 2 * E i / t) := by
    intro F E
    simp only [one_mul, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [key]
  exact h ht

/-- **The second-order localised susceptibility expansion**:
`|t²(−∂ₜ⟨L∘A⟩_loc) − d/2 − 2(∑ᵢ e₁ᵢ)/t| ≤ K/t²`, i.e.
`−∂ₜ⟨L∘A⟩_loc = d/(2t²) + 2∑e₁/t³ + O(t⁻⁴)` — the coefficientwise derivative of
`t⟨L∘A⟩_loc = d/2 + ∑e₁/t + O(t⁻²)`, established from moments. -/
theorem localisedEnergy_neg_deriv_order2 (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * (-deriv (fun s =>
          gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
            (rotatedAnharmonic Q c lam alpha gamma)) t) - (d : ℝ) / 2 -
        2 * (∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedVar_energy_order2 hlam hgamma hdisc hQ c w₀ hg
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedEnergy_neg_deriv_eq_var hlam hgamma hdisc hQ c w₀ hg ht0]
  exact h ht

/-- **The derivative of the Gaussian-trace discrepancy**: with `P(t) = ½tr(HS(t))`,
`|t³(Var_loc(L∘A) + P'(t)) − 2C₁| ≤ K/t`, `C₁ = ∑ᵢ (e₁ᵢ + g/(2λᵢ))` — i.e.
`−∂ₜ(⟨L∘A⟩_loc − P) = 2C₁/t³ + O(t⁻⁴)`, twice the invariant discrepancy coefficient. -/
theorem localisedVar_energy_add_tracePrediction_deriv (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) +
          deriv (fun s => 1 / 2 * ((Q * diagonal lam * Qᵀ) *
            locS g (Q * diagonal lam * Qᵀ) s).trace) t) -
        2 * ∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
          g / (2 * lam i))| ≤ K / t := by
  obtain ⟨Kv, Tv, hKv, hTv, hv⟩ := localisedVar_energy_order2 hlam hgamma hdisc hQ c w₀ hg
  obtain ⟨Kp, Tp, hKp, hTp, hp⟩ := sum_rate_div (fun _ : Fin d => (1 : ℝ))
    (fun i t => t ^ 3 * (1 / 2 * (lam i ^ 2 / (t * lam i + g) ^ 2)) - t / 2 + g / lam i) fun i =>
      ⟨g ^ 2 * (3 * lam i + 2 * g) / (2 * lam i ^ 3), 1, by have := hlam i; positivity, le_rfl,
        fun {t} ht => tracePrediction_coord_rate (hlam i) hg ht⟩
  refine ⟨Kv + Kp, Tv + Tp, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have ht' : t ≠ 0 := ht0.ne'
  rw [(hasDerivAt_tracePrediction hQ hlam hg ht0).deriv]
  have hv' := hv (t := t) (by linarith)
  have hp' := hp (t := t) (by linarith)
  set V := gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
    (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) with hV
  have hv3 : |t ^ 3 * V - t * ((d : ℝ) / 2) -
      2 * ∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)| ≤ Kv / t := by
    have e : t ^ 3 * V - t * ((d : ℝ) / 2) -
        2 * ∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) =
        t * (t ^ 2 * V - (d : ℝ) / 2 -
          2 * (∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t) := by
      field_simp
    rw [e, abs_mul, abs_of_pos ht0]
    calc t * |t ^ 2 * V - (d : ℝ) / 2 -
          2 * (∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t| ≤
        t * (Kv / t ^ 2) := by gcongr
      _ = Kv / t := by field_simp
  have hsum1 : ∑ i, (1 : ℝ) * (t ^ 3 * (1 / 2 * (lam i ^ 2 / (t * lam i + g) ^ 2)) - t / 2 +
      g / lam i) =
      t ^ 3 * (1 / 2 * ∑ i, lam i ^ 2 / (t * lam i + g) ^ 2) - (d : ℝ) * (t / 2) +
        ∑ i, g / lam i := by
    simp only [one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have hsum2 : 2 * ∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
      g / (2 * lam i)) =
      2 * ∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
        ∑ i, g / lam i := by
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      have := (hlam i).ne'
      field_simp
  have key : t ^ 3 * (V + -(1 / 2 * ∑ i, lam i ^ 2 / (t * lam i + g) ^ 2)) -
      2 * ∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
        g / (2 * lam i)) =
      (t ^ 3 * V - t * ((d : ℝ) / 2) -
        2 * ∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) -
      ∑ i, (1 : ℝ) * (t ^ 3 * (1 / 2 * (lam i ^ 2 / (t * lam i + g) ^ 2)) - t / 2 +
        g / lam i) := by
    rw [hsum1, hsum2]
    ring
  rw [key]
  exact (abs_sub _ _).trans (add_le_add hv3 hp') |>.trans (le_of_eq (add_div _ _ _).symm)

end Multi

end Laplace.Multi
