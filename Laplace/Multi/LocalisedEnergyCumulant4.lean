/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedEnergyVarOrder2

/-!
# The fourth cumulant of the localised energy: the Gamma(d/2, t) hierarchy through order four

On E2's exact localised measure, per frame coordinate: the localised moments of degree `≥ 10` are
`O(t⁻⁵)`, the *signed* ninth moment is `O(t⁻⁵)` (the Stein recursion at `k = 8`), the eighth moment
has `t⁴⟨x⁸⟩_loc = 105/λ⁴ + O(1/t)` (the recursion at `k = 7`), `t⁴⟨ℓ⁴⟩_loc → 105/16`, and the fourth
cumulant `κ₄(ℓ) = ⟨ℓ⁴⟩ − 4⟨ℓ³⟩⟨ℓ⟩ − 3⟨ℓ²⟩² + 12⟨ℓ²⟩⟨ℓ⟩² − 6⟨ℓ⟩⁴` has `t⁴κ₄ → 3`. On E2, exactly
`∂ₜ³⟨L∘A⟩_loc = −∑ᵢ κ₄,ᵢ` (the localiser is temperature-independent, so `∂ₜκ₃ = −κ₄`
coordinatewise),
`|t⁴∂ₜ³⟨L∘A⟩_loc + 3d| ≤ K/t`, and the normalised fourth-cumulant ratio
`∑ᵢκ₄,ᵢ / (∑ᵢ Var_loc,ᵢ(ℓᵢ))² → 12/d` — the excess kurtosis of a `Gamma(d/2)` law — with the
derivative-response corollary `(−∂ₜ³⟨L∘A⟩_loc)/(∂ₜ⟨L∘A⟩_loc)² → 12/d`.

With `LocalisedEnergyInvariant` and `LocalisedEnergyCumulant3`: the first four cumulants of the
localised energy have the leading asymptotics `κₙ = (n − 1)!·(d/2)/tⁿ` of a Gamma law with shape
`d/2` and rate `t`, with `O(1/t)` errors after the `tⁿ` rescaling.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section OneD

variable {lam alpha gamma g x₀ : ℝ} (hlam : 0 < lam) (hgamma : 0 < gamma)
  (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- Dividing a bounded `t⁵`-weighted quantity by the denominator. -/
theorem loc_ratio_bounded5 (f : ℝ → ℝ) (hg : 0 ≤ g)
    (hN : ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 5 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => f x * locWeight g x₀ x)| ≤ K) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 5 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t f| ≤ K := by
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
  calc |t ^ 5 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => f x * locWeight g x₀ x)| ≤ KN := eN
    _ = 2 * KN * (1 / 2) := by ring
    _ ≤ 2 * KN * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (locWeight g x₀) := by gcongr

/-- Even weighted moments of degree `2k ≥ 10`: `|t⁵ ⟨x^{2k} φ⟩| ≤ K`. -/
theorem locEven_weighted_bound5 (hg : 0 ≤ g) (k : ℕ) (hk : 5 ≤ k) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 5 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
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
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 5)]
  calc t ^ 5 * |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (2 * k) * locWeight g x₀ x)|
      ≤ t ^ 5 * (Real.exp (g * x₀ ^ 2 / 2) *
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ (2 * k))) :=
        mul_le_mul_of_nonneg_left ((abs_gibbsExpectation_le' hZ _).trans hmono) (by positivity)
    _ ≤ t ^ 5 * (Real.exp (g * x₀ ^ 2 / 2) * (C / t ^ k)) := by
        gcongr
        exact h (t := t) ht
    _ = Real.exp (g * x₀ ^ 2 / 2) * C * (t ^ 5 / t ^ k) := by ring
    _ ≤ Real.exp (g * x₀ ^ 2 / 2) * C * 1 := by
        gcongr
        exact div_le_one_of_le₀ (pow_le_pow_right₀ ht1 hk) (by positivity)
    _ = Real.exp (g * x₀ ^ 2 / 2) * C := mul_one _

/-- Odd weighted moments of degree `2k + 1 ≥ 11`: `|t⁵ ⟨x^{2k+1} φ⟩| ≤ K`, via
`|x|^{2k+1} ≤ (x^{2k} + x^{2(k+1)})/2`. -/
theorem locOdd_weighted_bound5 (hg : 0 ≤ g) (k : ℕ) (hk : 5 ≤ k) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 5 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
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
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 5)]
  have hk1 : t ^ 5 ≤ t ^ k := pow_le_pow_right₀ ht1 hk
  have hk2 : t ^ 5 ≤ t ^ (k + 1) := pow_le_pow_right₀ ht1 (by omega)
  calc t ^ 5 * |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ (2 * k + 1) * locWeight g x₀ x)|
      ≤ t ^ 5 * (Real.exp (g * x₀ ^ 2 / 2) * (1 / 2 *
          (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ (2 * k)) +
          _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ (2 * (k + 1)))))) :=
        mul_le_mul_of_nonneg_left ((abs_gibbsExpectation_le' hZ _).trans hmono) (by positivity)
    _ ≤ t ^ 5 * (Real.exp (g * x₀ ^ 2 / 2) * (1 / 2 * (C₁ / t ^ k + C₂ / t ^ (k + 1)))) := by
        gcongr
        · exact h₁ (t := t) (by linarith)
        · exact h₂ (t := t) (by linarith)
    _ = Real.exp (g * x₀ ^ 2 / 2) * ((C₁ * (t ^ 5 / t ^ k) + C₂ * (t ^ 5 / t ^ (k + 1))) / 2) := by
        ring
    _ ≤ Real.exp (g * x₀ ^ 2 / 2) * ((C₁ * 1 + C₂ * 1) / 2) := by
        gcongr
        · exact div_le_one_of_le₀ hk1 (by positivity)
        · exact div_le_one_of_le₀ hk2 (by positivity)
    _ = Real.exp (g * x₀ ^ 2 / 2) * ((C₁ + C₂) / 2) := by ring

theorem locEven_loc_bound5 (hg : 0 ≤ g) (k : ℕ) (hk : 5 ≤ k) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 5 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ (2 * k))| ≤ K :=
  loc_ratio_bounded5 hlam hgamma hdisc (fun x => x ^ (2 * k)) hg
    (locEven_weighted_bound5 hlam hgamma hdisc hg k hk)

theorem locOdd_loc_bound5 (hg : 0 ≤ g) (k : ℕ) (hk : 5 ≤ k) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 5 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ (2 * k + 1))| ≤ K :=
  loc_ratio_bounded5 hlam hgamma hdisc (fun x => x ^ (2 * k + 1)) hg
    (locOdd_weighted_bound5 hlam hgamma hdisc hg k hk)

/-- **The signed localised ninth moment is `O(t⁻⁵)`**: `|t⁵ ⟨x⁹⟩_loc| ≤ K` eventually, from the
Stein recursion at `k = 8` (`t⁵m₉ = (t/(tλ+g))·(8t⁴m₇ + gx₀t⁴m₈ − (α/2)t⁵m₁₀ − (γ/6)t⁵m₁₁)`). -/
theorem locNinthMoment_loc_bound5 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 5 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 9)| ≤ K := by
  obtain ⟨K₇, T₇, hK₇, hT₇, h₇⟩ := locSeventhMoment_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₈, T₈, hK₈, hT₈, h₈⟩ := locEven_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀) 4 le_rfl
  obtain ⟨K₁₀, T₁₀, hK₁₀, hT₁₀, h₁₀⟩ := locEven_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 5
    le_rfl
  obtain ⟨K₁₁, T₁₁, hK₁₁, hT₁₁, h₁₁⟩ := locOdd_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 5 le_rfl
  refine ⟨1 / lam * (8 * K₇ + |g * x₀| * K₈ + |alpha| / 2 * K₁₀ + gamma / 6 * K₁₁),
    T₇ + T₈ + T₁₀ + T₁₁, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hden : 0 < t * lam + g := by positivity
  have hrec := stein_loc_recursion hlam hgamma hdisc hg ht0 (x₀ := x₀) 8
  norm_num at hrec
  set m₇ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 7) with hm₇
  set m₈ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 8) with hm₈
  set m₉ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 9) with hm₉
  set m₁₀ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 10) with hm₁₀
  set m₁₁ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 11) with hm₁₁
  have e₇ := h₇ (t := t) (by linarith)
  have e₈ := h₈ (t := t) (by linarith)
  have e₁₀ := h₁₀ (t := t) (by linarith)
  have e₁₁ := h₁₁ (t := t) (by linarith)
  set r := t / (t * lam + g) with hr_def
  have hr : r * (t * lam + g) = t := by rw [hr_def]; field_simp
  have hr_le : r ≤ 1 / lam := by
    rw [hr_def, div_le_div_iff₀ hden hlam]
    nlinarith
  have hr_nonneg : 0 ≤ r := by positivity
  have key : t ^ 5 * m₉ = r * (8 * (t ^ 4 * m₇) + g * x₀ * (t ^ 4 * m₈) -
      alpha / 2 * (t ^ 5 * m₁₀) - gamma / 6 * (t ^ 5 * m₁₁)) := by
    linear_combination t ^ 4 * r * hrec - t ^ 4 * m₉ * hr
  have hb : |8 * (t ^ 4 * m₇) + g * x₀ * (t ^ 4 * m₈) - alpha / 2 * (t ^ 5 * m₁₀) -
      gamma / 6 * (t ^ 5 * m₁₁)| ≤
      8 * K₇ + |g * x₀| * K₈ + |alpha| / 2 * K₁₀ + gamma / 6 * K₁₁ := by
    have a1 := abs_add_le (8 * (t ^ 4 * m₇)) (g * x₀ * (t ^ 4 * m₈))
    have a2 := abs_sub (8 * (t ^ 4 * m₇) + g * x₀ * (t ^ 4 * m₈)) (alpha / 2 * (t ^ 5 * m₁₀))
    have a3 := abs_sub (8 * (t ^ 4 * m₇) + g * x₀ * (t ^ 4 * m₈) - alpha / 2 * (t ^ 5 * m₁₀))
      (gamma / 6 * (t ^ 5 * m₁₁))
    have b1 : |8 * (t ^ 4 * m₇)| ≤ 8 * K₇ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      exact mul_le_mul_of_nonneg_left e₇ (by norm_num)
    have b2 : |g * x₀ * (t ^ 4 * m₈)| ≤ |g * x₀| * K₈ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left e₈ (abs_nonneg _)
    have b3 : |alpha / 2 * (t ^ 5 * m₁₀)| ≤ |alpha| / 2 * K₁₀ := by
      rw [abs_mul, abs_div, abs_two]
      exact mul_le_mul_of_nonneg_left e₁₀ (by positivity)
    have b4 : |gamma / 6 * (t ^ 5 * m₁₁)| ≤ gamma / 6 * K₁₁ := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 6)]
      exact mul_le_mul_of_nonneg_left e₁₁ (by positivity)
    linarith
  rw [key, abs_mul, abs_of_nonneg hr_nonneg]
  exact mul_le_mul hr_le hb (abs_nonneg _) (by positivity)

/-- **The leading localised eighth moment**: `|t⁴⟨x⁸⟩_loc − 105/λ⁴| ≤ K/t`, from the Stein recursion
at `k = 7` (`t⁴m₈ = (t/(tλ+g))·(7t³m₆ + gx₀t³m₇ − (α/2)t⁴m₉ − (γ/6)t⁴m₁₀)`), the sixth-moment rate,
and the `t⁴`/`t⁵`-scaled bounds on `m₇`, `m₉`, `m₁₀`. -/
theorem locEighthMoment_loc_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 8) - 105 / lam ^ 4| ≤ K / t := by
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := locSixthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₇, T₇, hK₇, hT₇, h₇⟩ := locSeventhMoment_loc_bound4 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₉, T₉, hK₉, hT₉, h₉⟩ := locNinthMoment_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₁₀, T₁₀, hK₁₀, hT₁₀, h₁₀⟩ := locEven_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 5
    le_rfl
  refine ⟨1 / lam * (7 * K₆ + |g * x₀| * K₇ + |alpha| / 2 * K₉ + gamma / 6 * K₁₀) +
    g / lam ^ 2 * (105 / lam ^ 3), T₆ + T₇ + T₉ + T₁₀, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hden : 0 < t * lam + g := by positivity
  have hrec := stein_loc_recursion hlam hgamma hdisc hg ht0 (x₀ := x₀) 7
  norm_num at hrec
  set m₆ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 6) with hm₆
  set m₇ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 7) with hm₇
  set m₈ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 8) with hm₈
  set m₉ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 9) with hm₉
  set m₁₀ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 10) with hm₁₀
  have e₆ := h₆ (t := t) (by linarith)
  have e₇ := h₇ (t := t) (by linarith)
  have e₉ := h₉ (t := t) (by linarith)
  have e₁₀ := h₁₀ (t := t) (by linarith)
  set r := t / (t * lam + g) with hr_def
  have hr : r * (t * lam + g) = t := by rw [hr_def]; field_simp
  have hr_le : r ≤ 1 / lam := by
    rw [hr_def, div_le_div_iff₀ hden hlam]
    nlinarith
  have hr_nonneg : 0 ≤ r := by positivity
  have hr' : r - 1 / lam = -(g / (lam * (t * lam + g))) := by
    rw [hr_def]
    field_simp
    ring
  have hr'_le : |r - 1 / lam| ≤ g / lam ^ 2 / t := by
    rw [hr', abs_neg, abs_of_nonneg (by positivity), div_div]
    exact div_le_div_of_nonneg_left hg (by positivity) (by nlinarith [mul_nonneg hlam.le hg])
  have b₇ : |t ^ 3 * m₇| ≤ K₇ / t := by
    have e : t ^ 3 * m₇ = (t ^ 4 * m₇) / t := by rw [eq_div_iff ht0.ne']; ring
    rw [e, abs_div, abs_of_pos ht0]
    exact div_le_div_of_nonneg_right e₇ ht0.le
  have b₉ : |t ^ 4 * m₉| ≤ K₉ / t := by
    have e : t ^ 4 * m₉ = (t ^ 5 * m₉) / t := by rw [eq_div_iff ht0.ne']; ring
    rw [e, abs_div, abs_of_pos ht0]
    exact div_le_div_of_nonneg_right e₉ ht0.le
  have b₁₀ : |t ^ 4 * m₁₀| ≤ K₁₀ / t := by
    have e : t ^ 4 * m₁₀ = (t ^ 5 * m₁₀) / t := by rw [eq_div_iff ht0.ne']; ring
    rw [e, abs_div, abs_of_pos ht0]
    exact div_le_div_of_nonneg_right e₁₀ ht0.le
  have key : t ^ 4 * m₈ = r * (7 * (t ^ 3 * m₆) + g * x₀ * (t ^ 3 * m₇) -
      alpha / 2 * (t ^ 4 * m₉) - gamma / 6 * (t ^ 4 * m₁₀)) := by
    linear_combination t ^ 3 * r * hrec - t ^ 3 * m₈ * hr
  have key2 : t ^ 4 * m₈ - 105 / lam ^ 4 = r * (7 * (t ^ 3 * m₆ - 15 / lam ^ 3) +
      g * x₀ * (t ^ 3 * m₇) - alpha / 2 * (t ^ 4 * m₉) - gamma / 6 * (t ^ 4 * m₁₀)) +
      (r - 1 / lam) * (105 / lam ^ 3) := by
    rw [key]
    ring
  have hbr : |7 * (t ^ 3 * m₆ - 15 / lam ^ 3) + g * x₀ * (t ^ 3 * m₇) - alpha / 2 * (t ^ 4 * m₉) -
      gamma / 6 * (t ^ 4 * m₁₀)| ≤
      (7 * K₆ + |g * x₀| * K₇ + |alpha| / 2 * K₉ + gamma / 6 * K₁₀) / t := by
    have a1 := abs_add_le (7 * (t ^ 3 * m₆ - 15 / lam ^ 3)) (g * x₀ * (t ^ 3 * m₇))
    have a2 := abs_sub (7 * (t ^ 3 * m₆ - 15 / lam ^ 3) + g * x₀ * (t ^ 3 * m₇))
      (alpha / 2 * (t ^ 4 * m₉))
    have a3 := abs_sub (7 * (t ^ 3 * m₆ - 15 / lam ^ 3) + g * x₀ * (t ^ 3 * m₇) -
      alpha / 2 * (t ^ 4 * m₉)) (gamma / 6 * (t ^ 4 * m₁₀))
    have b1 : |7 * (t ^ 3 * m₆ - 15 / lam ^ 3)| ≤ 7 * (K₆ / t) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7)]
      exact mul_le_mul_of_nonneg_left e₆ (by norm_num)
    have b2 : |g * x₀ * (t ^ 3 * m₇)| ≤ |g * x₀| * (K₇ / t) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left b₇ (abs_nonneg _)
    have b3 : |alpha / 2 * (t ^ 4 * m₉)| ≤ |alpha| / 2 * (K₉ / t) := by
      rw [abs_mul, abs_div, abs_two]
      exact mul_le_mul_of_nonneg_left b₉ (by positivity)
    have b4 : |gamma / 6 * (t ^ 4 * m₁₀)| ≤ gamma / 6 * (K₁₀ / t) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 6)]
      exact mul_le_mul_of_nonneg_left b₁₀ (by positivity)
    have e : 7 * (K₆ / t) + |g * x₀| * (K₇ / t) + |alpha| / 2 * (K₉ / t) + gamma / 6 * (K₁₀ / t) =
        (7 * K₆ + |g * x₀| * K₇ + |alpha| / 2 * K₉ + gamma / 6 * K₁₀) / t := by ring
    linarith
  rw [key2]
  calc _ ≤ |r * (7 * (t ^ 3 * m₆ - 15 / lam ^ 3) + g * x₀ * (t ^ 3 * m₇) -
        alpha / 2 * (t ^ 4 * m₉) - gamma / 6 * (t ^ 4 * m₁₀))| +
        |(r - 1 / lam) * (105 / lam ^ 3)| := abs_add_le _ _
    _ ≤ 1 / lam * ((7 * K₆ + |g * x₀| * K₇ + |alpha| / 2 * K₉ + gamma / 6 * K₁₀) / t) +
        g / lam ^ 2 / t * (105 / lam ^ 3) := by
        rw [abs_mul, abs_of_nonneg hr_nonneg, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 105 / lam ^ 3)]
        exact add_le_add (mul_le_mul hr_le hbr (abs_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right hr'_le (by positivity))
    _ = _ := by ring

/-- `⟨ℓ⁴⟩_loc` as a combination of the localised moments of degrees `8` to `16`. -/
theorem locEnergyFourth_eq (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
      anharmonicPotential lam alpha gamma x * (anharmonicPotential lam alpha gamma x *
      (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x))) = lam ^ 4 /
      16 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 8)
      + (lam ^ 3 * alpha / 12 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀
      t) t (fun x => x ^ 9) + ((lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 * gamma / 48) *
      _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 10) +
      ((lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) * _root_.Laplace.gibbsExpectation
      (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 11) + ((alpha ^ 4 / 1296 + lam * alpha
      ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * _root_.Laplace.gibbsExpectation
      (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 12) + ((alpha ^ 3 * gamma / 1296 + lam
      * alpha * gamma ^ 2 / 576) * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g
      x₀ t) t (fun x => x ^ 13) + ((alpha ^ 2 * gamma ^ 2 / 3456 + lam * gamma ^ 3 / 6912) *
      _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 14) +
      (alpha * gamma ^ 3 / 20736 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g
      x₀ t) t (fun x => x ^ 15) + (gamma ^ 4 / 331776 * _root_.Laplace.gibbsExpectation
      (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 16))))))))) := by
  have hp : ∀ m, Integrable (fun x : ℝ => x ^ m *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    integrable_pow_locPotential1 hlam hgamma hdisc hg ht
  have hc : ∀ (a : ℝ) (m : ℕ), Integrable (fun x : ℝ => a * x ^ m *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := fun a m =>
    ((hp m).const_mul a).congr (Eventually.of_forall fun x => by ring)
  have h16 := hc (gamma ^ 4 / 331776) 16
  have h15 : Integrable (fun x : ℝ => (alpha * gamma ^ 3 / 20736 * x ^ 15 + (gamma ^ 4 / 331776 * x
      ^ 16)) * Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (alpha * gamma ^ 3 / 20736) 15).add h16).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h14 : Integrable (fun x : ℝ => ((alpha ^ 2 * gamma ^ 2 / 3456 + lam * gamma ^ 3 / 6912) * x ^
      14 + (alpha * gamma ^ 3 / 20736 * x ^ 15 + (gamma ^ 4 / 331776 * x ^ 16))) * Real.exp (-(t *
      locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (alpha ^ 2 * gamma ^ 2 / 3456 + lam * gamma ^ 3 / 6912) 14).add h15).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h13 : Integrable (fun x : ℝ => ((alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576) *
      x ^ 13 + ((alpha ^ 2 * gamma ^ 2 / 3456 + lam * gamma ^ 3 / 6912) * x ^ 14 + (alpha * gamma ^
      3 / 20736 * x ^ 15 + (gamma ^ 4 / 331776 * x ^ 16)))) * Real.exp (-(t * locPotential1 lam
      alpha gamma g x₀ t x))) :=
    ((hc (alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576) 13).add h14).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h12 : Integrable (fun x : ℝ => ((alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 *
      gamma ^ 2 / 384) * x ^ 12 + ((alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576) * x ^
      13 + ((alpha ^ 2 * gamma ^ 2 / 3456 + lam * gamma ^ 3 / 6912) * x ^ 14 + (alpha * gamma ^ 3 /
      20736 * x ^ 15 + (gamma ^ 4 / 331776 * x ^ 16))))) * Real.exp (-(t * locPotential1 lam alpha
      gamma g x₀ t x))) :=
    ((hc (alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) 12).add
      h13).congr (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h11 : Integrable (fun x : ℝ => ((lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) * x ^
      11 + ((alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * x ^ 12
      + ((alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576) * x ^ 13 + ((alpha ^ 2 * gamma ^
      2 / 3456 + lam * gamma ^ 3 / 6912) * x ^ 14 + (alpha * gamma ^ 3 / 20736 * x ^ 15 + (gamma ^ 4
      / 331776 * x ^ 16)))))) * Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) 11).add h12).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h10 : Integrable (fun x : ℝ => ((lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 * gamma / 48) * x ^ 10 +
      ((lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) * x ^ 11 + ((alpha ^ 4 / 1296 + lam *
      alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * x ^ 12 + ((alpha ^ 3 * gamma / 1296 +
      lam * alpha * gamma ^ 2 / 576) * x ^ 13 + ((alpha ^ 2 * gamma ^ 2 / 3456 + lam * gamma ^ 3 /
      6912) * x ^ 14 + (alpha * gamma ^ 3 / 20736 * x ^ 15 + (gamma ^ 4 / 331776 * x ^ 16))))))) *
      Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 * gamma / 48) 10).add h11).congr (Eventually.of_forall
      fun x => by simp only [Pi.add_apply]; ring)
  have h9 : Integrable (fun x : ℝ => (lam ^ 3 * alpha / 12 * x ^ 9 + ((lam ^ 2 * alpha ^ 2 / 24 +
      lam ^ 3 * gamma / 48) * x ^ 10 + ((lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) * x ^
      11 + ((alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * x ^ 12
      + ((alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576) * x ^ 13 + ((alpha ^ 2 * gamma ^
      2 / 3456 + lam * gamma ^ 3 / 6912) * x ^ 14 + (alpha * gamma ^ 3 / 20736 * x ^ 15 + (gamma ^ 4
      / 331776 * x ^ 16)))))))) * Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) :=
    ((hc (lam ^ 3 * alpha / 12) 9).add h10).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have e : (fun x => anharmonicPotential lam alpha gamma x * (anharmonicPotential lam alpha gamma x
      * (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x))) = fun x =>
      lam ^ 4 / 16 * x ^ 8 + (lam ^ 3 * alpha / 12 * x ^ 9 + ((lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 *
      gamma / 48) * x ^ 10 + ((lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) * x ^ 11 +
      ((alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * x ^ 12 +
      ((alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576) * x ^ 13 + ((alpha ^ 2 * gamma ^ 2
      / 3456 + lam * gamma ^ 3 / 6912) * x ^ 14 + (alpha * gamma ^ 3 / 20736 * x ^ 15 + (gamma ^ 4 /
      331776 * x ^ 16)))))))) := by
    funext x
    simp only [anharmonicPotential]
    ring
  rw [e, _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam ^ 4 / 16) 8) h9,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam ^ 3 * alpha / 12) 9) h10,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 * gamma /
    48) 10) h11, _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (lam * alpha ^ 3 / 108 + lam ^ 2 *
    alpha * gamma / 48) 11) h12, _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (alpha ^ 4 / 1296 +
    lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) 12) h13,
    _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (alpha ^ 3 * gamma / 1296 + lam * alpha * gamma
    ^ 2 / 576) 13) h14, _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (alpha ^ 2 * gamma ^ 2 /
    3456 + lam * gamma ^ 3 / 6912) 14) h15, _root_.Laplace.gibbsExpectation_add _ _ _ _ (hc (alpha *
    gamma ^ 3 / 20736) 15) h16, _root_.Laplace.gibbsExpectation_smul,
    _root_.Laplace.gibbsExpectation_smul, _root_.Laplace.gibbsExpectation_smul,
    _root_.Laplace.gibbsExpectation_smul, _root_.Laplace.gibbsExpectation_smul,
    _root_.Laplace.gibbsExpectation_smul, _root_.Laplace.gibbsExpectation_smul,
    _root_.Laplace.gibbsExpectation_smul, _root_.Laplace.gibbsExpectation_smul]

omit hlam hgamma hdisc in
/-- Assembly: `|t⁴⟨ℓ⁴⟩_loc − 105/16| ≤ K/t` from the eighth-moment rate and the `t⁵`-scaled
bounds on the moments of degrees `9` to `16`. -/
theorem energyFourth_assembly (lam alpha gamma t M8 M9 M10 M11 M12 M13 M14 M15 M16 : ℝ)
    (K8 K9 K10 K11 K12 K13 K14 K15 K16 : ℝ) (hlam : 0 < lam) (ht1 : 1 ≤ t)
    (e8 : |t ^ 4 * M8 - 105 / lam ^ 4| ≤ K8 / t)
    (e9 : |t ^ 5 * M9| ≤ K9) (e10 : |t ^ 5 * M10| ≤ K10) (e11 : |t ^ 5 * M11| ≤ K11) (e12 : |t ^ 5 *
    M12| ≤ K12) (e13 : |t ^ 5 * M13| ≤ K13) (e14 : |t ^ 5 * M14| ≤ K14) (e15 : |t ^ 5 * M15| ≤ K15)
    (e16 : |t ^ 5 * M16| ≤ K16) :
    |t ^ 4 * (lam ^ 4 / 16 * M8 + (lam ^ 3 * alpha / 12 * M9 + ((lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3
      * gamma / 48) * M10 + ((lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) * M11 + ((alpha
      ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * M12 + ((alpha ^ 3 *
      gamma / 1296 + lam * alpha * gamma ^ 2 / 576) * M13 + ((alpha ^ 2 * gamma ^ 2 / 3456 + lam *
      gamma ^ 3 / 6912) * M14 + (alpha * gamma ^ 3 / 20736 * M15 + (gamma ^ 4 / 331776 *
      M16))))))))) - 105 / 16| ≤ (lam ^ 4 / 16 * K8 + (|lam ^ 3 * alpha / 12| * K9 + (|lam ^ 2 *
      alpha ^ 2 / 24 + lam ^ 3 * gamma / 48| * K10 + (|lam * alpha ^ 3 / 108 + lam ^ 2 * alpha *
      gamma / 48| * K11 + (|alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 /
      384| * K12 + (|alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576| * K13 + (|alpha ^ 2 *
      gamma ^ 2 / 3456 + lam * gamma ^ 3 / 6912| * K14 + (|alpha * gamma ^ 3 / 20736| * K15 +
      (|gamma ^ 4 / 331776| * K16))))))))) / t := by
  have ht0 : 0 < t := by linarith
  have hl : lam ≠ 0 := hlam.ne'
  have key : t ^ 4 * (lam ^ 4 / 16 * M8 + (lam ^ 3 * alpha / 12 * M9 + ((lam ^ 2 * alpha ^ 2 / 24 +
      lam ^ 3 * gamma / 48) * M10 + ((lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) * M11 +
      ((alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * M12 +
      ((alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576) * M13 + ((alpha ^ 2 * gamma ^ 2 /
      3456 + lam * gamma ^ 3 / 6912) * M14 + (alpha * gamma ^ 3 / 20736 * M15 + (gamma ^ 4 / 331776
      * M16))))))))) - 105 / 16 = lam ^ 4 / 16 * (t ^ 4 * M8 - 105 / lam ^ 4) + (lam ^ 3 * alpha /
      12 * (t ^ 5 * M9) + ((lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 * gamma / 48) * (t ^ 5 * M10) + ((lam
      * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) * (t ^ 5 * M11) + ((alpha ^ 4 / 1296 + lam *
      alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * (t ^ 5 * M12) + ((alpha ^ 3 * gamma /
      1296 + lam * alpha * gamma ^ 2 / 576) * (t ^ 5 * M13) + ((alpha ^ 2 * gamma ^ 2 / 3456 + lam *
      gamma ^ 3 / 6912) * (t ^ 5 * M14) + (alpha * gamma ^ 3 / 20736 * (t ^ 5 * M15) + (gamma ^ 4 /
      331776 * (t ^ 5 * M16))))))))) / t := by
    field_simp
    ring
  rw [key]
  have h8 : |lam ^ 4 / 16 * (t ^ 4 * M8 - 105 / lam ^ 4)| ≤ lam ^ 4 / 16 * (K8 / t) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam ^ 4 / 16)]
    exact mul_le_mul_of_nonneg_left e8 (by positivity)
  have hb : ∀ (c X K : ℝ), |t ^ 5 * X| ≤ K → |c * (t ^ 5 * X)| ≤ |c| * K := fun c X K h => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hrest : |lam ^ 3 * alpha / 12 * (t ^ 5 * M9) + ((lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 * gamma /
      48) * (t ^ 5 * M10) + ((lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48) * (t ^ 5 * M11)
      + ((alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * (t ^ 5 *
      M12) + ((alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576) * (t ^ 5 * M13) + ((alpha ^
      2 * gamma ^ 2 / 3456 + lam * gamma ^ 3 / 6912) * (t ^ 5 * M14) + (alpha * gamma ^ 3 / 20736 *
      (t ^ 5 * M15) + (gamma ^ 4 / 331776 * (t ^ 5 * M16))))))))| ≤ |lam ^ 3 * alpha / 12| * K9 +
      (|lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 * gamma / 48| * K10 + (|lam * alpha ^ 3 / 108 + lam ^ 2 *
      alpha * gamma / 48| * K11 + (|alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 *
      gamma ^ 2 / 384| * K12 + (|alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576| * K13 +
      (|alpha ^ 2 * gamma ^ 2 / 3456 + lam * gamma ^ 3 / 6912| * K14 + (|alpha * gamma ^ 3 / 20736|
      * K15 + (|gamma ^ 4 / 331776| * K16))))))) :=
    (abs_add_le _ _).trans (add_le_add (hb _ _ _ e9) ((abs_add_le _ _).trans (add_le_add (hb _ _ _
      e10) ((abs_add_le _ _).trans (add_le_add (hb _ _ _ e11) ((abs_add_le _ _).trans (add_le_add
      (hb _ _ _ e12) ((abs_add_le _ _).trans (add_le_add (hb _ _ _ e13) ((abs_add_le _ _).trans
      (add_le_add (hb _ _ _ e14) ((abs_add_le _ _).trans (add_le_add (hb _ _ _ e15) (hb _ _ _
      e16))))))))))))))
  calc _ ≤ |lam ^ 4 / 16 * (t ^ 4 * M8 - 105 / lam ^ 4)| + |lam ^ 3 * alpha / 12 * (t ^ 5 * M9) +
        ((lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 * gamma / 48) * (t ^ 5 * M10) + ((lam * alpha ^ 3 / 108
        + lam ^ 2 * alpha * gamma / 48) * (t ^ 5 * M11) + ((alpha ^ 4 / 1296 + lam * alpha ^ 2 *
        gamma / 144 + lam ^ 2 * gamma ^ 2 / 384) * (t ^ 5 * M12) + ((alpha ^ 3 * gamma / 1296 + lam
        * alpha * gamma ^ 2 / 576) * (t ^ 5 * M13) + ((alpha ^ 2 * gamma ^ 2 / 3456 + lam * gamma ^
        3 / 6912) * (t ^ 5 * M14) + (alpha * gamma ^ 3 / 20736 * (t ^ 5 * M15) + (gamma ^ 4 / 331776
        * (t ^ 5 * M16))))))))| / t := by
        rw [← abs_of_pos ht0, ← abs_div, abs_of_pos ht0]
        exact abs_add_le _ _
    _ ≤ lam ^ 4 / 16 * (K8 / t) + (|lam ^ 3 * alpha / 12| * K9 + (|lam ^ 2 * alpha ^ 2 / 24 + lam ^
        3 * gamma / 48| * K10 + (|lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48| * K11 +
        (|alpha ^ 4 / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384| * K12 +
        (|alpha ^ 3 * gamma / 1296 + lam * alpha * gamma ^ 2 / 576| * K13 + (|alpha ^ 2 * gamma ^ 2
        / 3456 + lam * gamma ^ 3 / 6912| * K14 + (|alpha * gamma ^ 3 / 20736| * K15 + (|gamma ^ 4 /
        331776| * K16)))))))) / t := by gcongr
    _ = _ := by ring

/-- **The leading localised energy fourth moment**: `|t⁴⟨ℓ⁴⟩_loc − 105/16| ≤ K/t`. -/
theorem locEnergyFourth_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
        anharmonicPotential lam alpha gamma x * (anharmonicPotential lam alpha gamma x *
        (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x))) - 105 /
        16| ≤ K / t := by
  obtain ⟨K8, T8, hK8, hT8, h8⟩ := locEighthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K9, T9, hK9, hT9, h9⟩ := locNinthMoment_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K10, T10, hK10, hT10, h10⟩ := locEven_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 5 le_rfl
  obtain ⟨K11, T11, hK11, hT11, h11⟩ := locOdd_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 5 le_rfl
  obtain ⟨K12, T12, hK12, hT12, h12⟩ := locEven_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 6 (by
    norm_num)
  obtain ⟨K13, T13, hK13, hT13, h13⟩ := locOdd_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 6 (by
    norm_num)
  obtain ⟨K14, T14, hK14, hT14, h14⟩ := locEven_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 7 (by
    norm_num)
  obtain ⟨K15, T15, hK15, hT15, h15⟩ := locOdd_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 7 (by
    norm_num)
  obtain ⟨K16, T16, hK16, hT16, h16⟩ := locEven_loc_bound5 hlam hgamma hdisc hg (x₀ := x₀) 8 (by
    norm_num)
  refine ⟨lam ^ 4 / 16 * K8 + (|lam ^ 3 * alpha / 12| * K9 + (|lam ^ 2 * alpha ^ 2 / 24 + lam ^ 3 *
    gamma / 48| * K10 + (|lam * alpha ^ 3 / 108 + lam ^ 2 * alpha * gamma / 48| * K11 + (|alpha ^ 4
    / 1296 + lam * alpha ^ 2 * gamma / 144 + lam ^ 2 * gamma ^ 2 / 384| * K12 + (|alpha ^ 3 * gamma
    / 1296 + lam * alpha * gamma ^ 2 / 576| * K13 + (|alpha ^ 2 * gamma ^ 2 / 3456 + lam * gamma ^ 3
    / 6912| * K14 + (|alpha * gamma ^ 3 / 20736| * K15 + (|gamma ^ 4 / 331776| * K16)))))))), T8 +
    T9 + T10 + T11 + T12 + T13 + T14 + T15 + T16, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [locEnergyFourth_eq hlam hgamma hdisc hg ht0]
  exact energyFourth_assembly lam alpha gamma t _ _ _ _ _ _ _ _ _ K8 K9 K10 K11 K12 K13 K14 K15 K16
    hlam ht1 (h8 (t := t) (by linarith)) (h9 (t := t) (by linarith)) (h10 (t := t) (by linarith))
    (h11 (t := t) (by linarith)) (h12 (t := t) (by linarith)) (h13 (t := t) (by linarith)) (h14 (t
    := t) (by linarith)) (h15 (t := t) (by linarith)) (h16 (t := t) (by linarith))

/-- **The fourth cumulant of the localised energy at leading order**:
`|t⁴ (⟨ℓ⁴⟩ − 4⟨ℓ³⟩⟨ℓ⟩ − 3⟨ℓ²⟩² + 12⟨ℓ²⟩⟨ℓ⟩² − 6⟨ℓ⟩⁴) − 3| ≤ K/t` — the fourth cumulant `3!·½ = 3` of
a `Gamma(½, t)` law. -/
theorem locEnergyCum4_leading (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
        anharmonicPotential lam alpha gamma x * (anharmonicPotential lam alpha gamma x *
        (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x))) - 4 *
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
        anharmonicPotential lam alpha gamma x * (anharmonicPotential lam alpha gamma x *
        anharmonicPotential lam alpha gamma x)) * _root_.Laplace.gibbsExpectation (locPotential1 lam
        alpha gamma g x₀ t) t (anharmonicPotential lam alpha gamma) - 3 *
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
        anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) ^ 2 + 12 *
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
        anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) *
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) ^ 2 - 6 * _root_.Laplace.gibbsExpectation
        (locPotential1 lam alpha gamma g x₀ t) t (anharmonicPotential lam alpha gamma) ^ 4) - 3| ≤ K
        / t := by
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locEnergyFourth_leading hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locEnergyCube_leading hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locEnergySq_leading hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := locEnergy_leading hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K₄ + 4 * (K₃ * (|(1 : ℝ) / 2| + K₁) + |(15 : ℝ) / 8| * K₁) + 3 * (2 * |(3 : ℝ) / 4| * K₂ +
    K₂ ^ 2) + 12 * (K₂ * (|((1 : ℝ) / 2) ^ 2| + (2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2)) + |(3 : ℝ) / 4| *
    (2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2)) + 6 * (2 * |((1 : ℝ) / 2) ^ 2| * (2 * |(1 : ℝ) / 2| * K₁ + K₁
    ^ 2) + (2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2) ^ 2), T₄ + T₃ + T₂ + T₁, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have e₄ := h₄ (t := t) (by linarith)
  have e₃ := h₃ (t := t) (by linarith)
  have e₂ := h₂ (t := t) (by linarith)
  have e₁ := h₁ (t := t) (by linarith)
  set X₄ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
    anharmonicPotential lam alpha gamma x * (anharmonicPotential lam alpha gamma x *
    (anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x))) with hX₄
  set X₃ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
    anharmonicPotential lam alpha gamma x * (anharmonicPotential lam alpha gamma x *
    anharmonicPotential lam alpha gamma x)) with hX₃
  set X₂ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x =>
    anharmonicPotential lam alpha gamma x * anharmonicPotential lam alpha gamma x) with hX₂
  set X₁ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (anharmonicPotential lam alpha gamma) with hX₁
  have p₃₁ := prod_rate t _ _ (15 / 8) (1 / 2) K₃ K₁ ht1 hK₃ hK₁ e₃ e₁
  have s₂ := sq_rate ht1 hK₂ e₂
  have s₁ := sq_rate ht1 hK₁ e₁
  have p₂₁₁ := prod_rate t _ _ (3 / 4) ((1 / 2) ^ 2) K₂ (2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2) ht1 hK₂
    (by positivity) e₂ s₁
  have s₁₁ := sq_rate ht1 (by positivity) s₁
  have key : t ^ 4 * (X₄ - 4 * X₃ * X₁ - 3 * X₂ ^ 2 + 12 * X₂ * X₁ ^ 2 - 6 * X₁ ^ 4) - 3 =
      (t ^ 4 * X₄ - 105 / 16) - 4 * (t ^ 3 * X₃ * (t * X₁) - 15 / 8 * (1 / 2)) -
        3 * ((t ^ 2 * X₂) ^ 2 - (3 / 4) ^ 2) +
        12 * (t ^ 2 * X₂ * (t * X₁) ^ 2 - 3 / 4 * (1 / 2) ^ 2) -
        6 * (((t * X₁) ^ 2) ^ 2 - ((1 / 2) ^ 2) ^ 2) := by ring
  rw [key]
  have hT : |(t ^ 4 * X₄ - 105 / 16) - 4 * (t ^ 3 * X₃ * (t * X₁) - 15 / 8 * (1 / 2)) -
      3 * ((t ^ 2 * X₂) ^ 2 - (3 / 4) ^ 2) +
      12 * (t ^ 2 * X₂ * (t * X₁) ^ 2 - 3 / 4 * (1 / 2) ^ 2) -
      6 * (((t * X₁) ^ 2) ^ 2 - ((1 / 2) ^ 2) ^ 2)| ≤
      |t ^ 4 * X₄ - 105 / 16| + |4 * (t ^ 3 * X₃ * (t * X₁) - 15 / 8 * (1 / 2))| +
      |3 * ((t ^ 2 * X₂) ^ 2 - (3 / 4) ^ 2)| +
      |12 * (t ^ 2 * X₂ * (t * X₁) ^ 2 - 3 / 4 * (1 / 2) ^ 2)| +
      |6 * (((t * X₁) ^ 2) ^ 2 - ((1 / 2) ^ 2) ^ 2)| := by
    have a1 := abs_sub (t ^ 4 * X₄ - 105 / 16) (4 * (t ^ 3 * X₃ * (t * X₁) - 15 / 8 * (1 / 2)))
    have a2 := abs_sub ((t ^ 4 * X₄ - 105 / 16) - 4 * (t ^ 3 * X₃ * (t * X₁) - 15 / 8 * (1 / 2)))
      (3 * ((t ^ 2 * X₂) ^ 2 - (3 / 4) ^ 2))
    have a3 := abs_add_le ((t ^ 4 * X₄ - 105 / 16) -
      4 * (t ^ 3 * X₃ * (t * X₁) - 15 / 8 * (1 / 2)) - 3 * ((t ^ 2 * X₂) ^ 2 - (3 / 4) ^ 2))
      (12 * (t ^ 2 * X₂ * (t * X₁) ^ 2 - 3 / 4 * (1 / 2) ^ 2))
    have a4 := abs_sub ((t ^ 4 * X₄ - 105 / 16) -
      4 * (t ^ 3 * X₃ * (t * X₁) - 15 / 8 * (1 / 2)) - 3 * ((t ^ 2 * X₂) ^ 2 - (3 / 4) ^ 2) +
      12 * (t ^ 2 * X₂ * (t * X₁) ^ 2 - 3 / 4 * (1 / 2) ^ 2))
      (6 * (((t * X₁) ^ 2) ^ 2 - ((1 / 2) ^ 2) ^ 2))
    linarith
  refine hT.trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (by norm_num : (0 : ℝ) < 12),
    abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  calc _ ≤ K₄ / t + 4 * ((K₃ * (|(1 : ℝ) / 2| + K₁) + |(15 : ℝ) / 8| * K₁) / t) + 3 * ((2 * |(3 : ℝ)
        / 4| * K₂ + K₂ ^ 2) / t) + 12 * ((K₂ * (|((1 : ℝ) / 2) ^ 2| + (2 * |(1 : ℝ) / 2| * K₁ + K₁ ^
        2)) + |(3 : ℝ) / 4| * (2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2)) / t) + 6 * ((2 * |((1 : ℝ) / 2) ^
        2| * (2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2) + (2 * |(1 : ℝ) / 2| * K₁ + K₁ ^ 2) ^ 2) / t) := by
        gcongr
    _ = _ := by ring

end OneD

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- Integrability of `ℓₖ(uₖ) ℓᵢ(uᵢ)³` against the unlocalised separable measure. -/
theorem integrable_energy_energyCube_coord (k i : Fin d) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      (anharmonicPotential (lam i) (alpha i) (gamma i) (u i) * (anharmonicPotential (lam i) (alpha
      i) (gamma i) (u i) * anharmonicPotential (lam i) (alpha i) (gamma i) (u i))) * Real.exp (-(s *
      separableAnharmonic lam alpha gamma u))) := by
  have h6 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 6
  have h7 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 7
  have h8 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 8
  have h9 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 9
  have h10 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 10
  have h11 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 11
  have h12 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc hs k i 12
  refine (((((((h6.const_mul (lam i ^ 3 / 8)).add (h7.const_mul (lam i ^ 2 * alpha i / 8))).add
    (h8.const_mul (lam i ^ 2 * gamma i / 32 + lam i * alpha i ^ 2 / 24))).add (h9.const_mul (lam i *
    alpha i * gamma i / 48 + alpha i ^ 3 / 216))).add (h10.const_mul (lam i * gamma i ^ 2 / 384 +
    alpha i ^ 2 * gamma i / 288))).add (h11.const_mul (alpha i * gamma i ^ 2 / 1152))).add
    (h12.const_mul (gamma i ^ 3 / 13824))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

/-- Integrability of `ℓᵢ(uᵢ)³` against the unlocalised separable measure. -/
theorem integrable_energyCube_coord_alone (i : Fin d) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u : Fin d → ℝ => (anharmonicPotential (lam i) (alpha i) (gamma i) (u i) *
      (anharmonicPotential (lam i) (alpha i) (gamma i) (u i) * anharmonicPotential (lam i) (alpha i)
      (gamma i) (u i))) * Real.exp (-(s * separableAnharmonic lam alpha gamma u))) := by
  have h6 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 6
  have h7 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 7
  have h8 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 8
  have h9 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 9
  have h10 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 10
  have h11 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 11
  have h12 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc hs i i 0 12
  refine (((((((h6.const_mul (lam i ^ 3 / 8)).add (h7.const_mul (lam i ^ 2 * alpha i / 8))).add
    (h8.const_mul (lam i ^ 2 * gamma i / 32 + lam i * alpha i ^ 2 / 24))).add (h9.const_mul (lam i *
    alpha i * gamma i / 48 + alpha i ^ 3 / 216))).add (h10.const_mul (lam i * gamma i ^ 2 / 384 +
    alpha i ^ 2 * gamma i / 288))).add (h11.const_mul (alpha i * gamma i ^ 2 / 1152))).add
    (h12.const_mul (gamma i ^ 3 / 13824))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential, pow_zero, one_mul]
  ring

/-- Integrability of `ℓₖ(uₖ) ℓᵢ(uᵢ)³` on the frame family. -/
theorem integrable_energy_energyCube_locFamily (hg : 0 ≤ g) (u₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (k i : Fin d) :
    Integrable (fun u : Fin d → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      (anharmonicPotential (lam i) (alpha i) (gamma i) (u i) * (anharmonicPotential (lam i) (alpha
      i) (gamma i) (u i) * anharmonicPotential (lam i) (alpha i) (gamma i) (u i))) * Real.exp (-(t *
      separablePotential (locFamily lam alpha gamma g u₀ t) u))) := by
  have h6 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 6
  have h7 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 7
  have h8 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 8
  have h9 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 9
  have h10 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 10
  have h11 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 11
  have h12 := integrable_energy_pow_locFamily hlam hgamma hdisc hg u₀ ht k i 12
  refine (((((((h6.const_mul (lam i ^ 3 / 8)).add (h7.const_mul (lam i ^ 2 * alpha i / 8))).add
    (h8.const_mul (lam i ^ 2 * gamma i / 32 + lam i * alpha i ^ 2 / 24))).add (h9.const_mul (lam i *
    alpha i * gamma i / 48 + alpha i ^ 3 / 216))).add (h10.const_mul (lam i * gamma i ^ 2 / 384 +
    alpha i ^ 2 * gamma i / 288))).add (h11.const_mul (alpha i * gamma i ^ 2 / 1152))).add
    (h12.const_mul (gamma i ^ 3 / 13824))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

/-- The coordinatewise third cumulants, rewritten through the frame expectations. -/
theorem localisedCum3_eq_frame_sum (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {s : ℝ}
    (hs : 0 < s) :
    ∑ i, (_root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame
      Q c w₀ i) s) s (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
      (anharmonicPotential (lam i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i)
      (gamma i) x)) - 3 * _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i)
      g (affineFrame Q c w₀ i) s) s (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
      anharmonicPotential (lam i) (alpha i) (gamma i) x) * _root_.Laplace.gibbsExpectation
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) s) s (anharmonicPotential
      (lam i) (alpha i) (gamma i)) + 2 * _root_.Laplace.gibbsExpectation (locPotential1 (lam i)
      (alpha i) (gamma i) g (affineFrame Q c w₀ i) s) s (anharmonicPotential (lam i) (alpha i)
      (gamma i)) ^ 3) = ∑ i, (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀
      s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) *
      (anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) * anharmonicPotential
      (lam i) (alpha i) (gamma i) (affineFrame Q c w i))) - 3 * (gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam
      i) (alpha i) (gamma i) (affineFrame Q c w i) * anharmonicPotential (lam i) (alpha i) (gamma i)
      (affineFrame Q c w i)) * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀
      s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i))) + 2 *
      (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w =>
      anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) * (gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam
      i) (alpha i) (gamma i) (affineFrame Q c w i)) * gibbsExpectation (localisedRotatedAnharmonic Q
      c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i)
      (affineFrame Q c w i))))) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcont : Continuous (anharmonicPotential (lam i) (alpha i) (gamma i)) := by
    unfold anharmonicPotential; fun_prop
  rw [localised_frame_fun_expectation hlam hgamma hdisc hQ c w₀ hg hs i (fun x =>
    anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i)
    (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x)) (hcont.mul (hcont.mul hcont)),
    localised_frame_fun_expectation hlam hgamma hdisc hQ c w₀ hg hs i (fun x => anharmonicPotential
    (lam i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x) (hcont.mul
    hcont), localised_frame_fun_expectation hlam hgamma hdisc hQ c w₀ hg hs i (anharmonicPotential
    (lam i) (alpha i) (gamma i)) hcont]
  ring

/-- **The derivative of the `i`-th coordinate third cumulant**: `d/ds κ₃,loc,ᵢ(s) = −κ₄,loc,ᵢ(t)`
with `κ₄ = ⟨ℓ⁴⟩ − 4⟨ℓ³⟩⟨ℓ⟩ − 3⟨ℓ²⟩² + 12⟨ℓ²⟩⟨ℓ⟩² − 6⟨ℓ⟩⁴`, through the frame expectations. -/
theorem hasDerivAt_localised_frame_cum3 (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (i : Fin d) :
    HasDerivAt (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
      (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) *
      (anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) * anharmonicPotential
      (lam i) (alpha i) (gamma i) (affineFrame Q c w i))) - 3 * (gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam
      i) (alpha i) (gamma i) (affineFrame Q c w i) * anharmonicPotential (lam i) (alpha i) (gamma i)
      (affineFrame Q c w i)) * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀
      s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i))) + 2 *
      (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w =>
      anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) * (gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam
      i) (alpha i) (gamma i) (affineFrame Q c w i)) * gibbsExpectation (localisedRotatedAnharmonic Q
      c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i)
      (affineFrame Q c w i))))) (-(_root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i)
      (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma
      i) x * (anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i)
      (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x))) - 4 *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential
      (lam i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x)) *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) - 3 *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x * anharmonicPotential
      (lam i) (alpha i) (gamma i) x) ^ 2 + 12 * _root_.Laplace.gibbsExpectation (locPotential1 (lam
      i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => anharmonicPotential (lam i)
      (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x) *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 2 - 6 *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 4)) t := by
  have ht2 := half_pos ht
  have hcont : Continuous (anharmonicPotential (lam i) (alpha i) (gamma i)) := by
    unfold anharmonicPotential; fun_prop
  have h3 := hasDerivAt_localised_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i (fun x =>
    anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i)
    (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x)) (hcont.mul (hcont.mul hcont))
    (fun k => integrable_energy_energyCube_coord hlam hgamma hdisc k i ht2)
    (integrable_energyCube_coord_alone hlam hgamma hdisc i ht2)
  have h2 := hasDerivAt_localised_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i (fun x =>
    anharmonicPotential (lam i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma
    i) x) (hcont.mul hcont) (fun k => integrable_energy_energySq_coord hlam hgamma hdisc k i ht2)
    (integrable_energySq_coord_alone hlam hgamma hdisc i ht2)
  have h1 := hasDerivAt_localised_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i (anharmonicPotential
    (lam i) (alpha i) (gamma i)) hcont (fun k => integrable_energy_energy_coord hlam hgamma hdisc k
    i ht2) (integrable_energy_coord_alone hlam hgamma hdisc i ht2)
  refine ((h3.sub ((h2.mul h1).const_mul 3)).add
    ((h1.mul (h1.mul h1)).const_mul 2)).congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [localisedCovK_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i
      (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
        (anharmonicPotential (lam i) (alpha i) (gamma i) x *
          anharmonicPotential (lam i) (alpha i) (gamma i) x))
      (hcont.mul (hcont.mul hcont))
      (fun k => integrable_energy_energyCube_locFamily hlam hgamma hdisc hg _ ht k i),
    localisedCovK_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i
      (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
        anharmonicPotential (lam i) (alpha i) (gamma i) x)
      (hcont.mul hcont)
      (fun k => integrable_energy_energySq_locFamily hlam hgamma hdisc hg _ ht k i),
    localisedCovK_frame_fun hlam hgamma hdisc hQ c w₀ hg ht i
      (anharmonicPotential (lam i) (alpha i) (gamma i)) hcont
      (fun k => integrable_energy_energy_locFamily hlam hgamma hdisc hg _ ht k i),
    localised_frame_fun_expectation hlam hgamma hdisc hQ c w₀ hg ht i
      (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
        anharmonicPotential (lam i) (alpha i) (gamma i) x)
      (hcont.mul hcont),
    localised_frame_fun_expectation hlam hgamma hdisc hQ c w₀ hg ht i
      (anharmonicPotential (lam i) (alpha i) (gamma i)) hcont]
  unfold _root_.Laplace.gibbsCov
  ring

/-- **The exact third temperature derivative**: `d/ds (∂ₛ²⟨L∘A⟩_loc)(t) = −∑ᵢ κ₄,loc,ᵢ(t)` — the
localiser is temperature-independent, so each coordinate's `κ₃` differentiates to `−κ₄`. -/
theorem hasDerivAt_localised_energy_deriv2 (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (deriv fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
      gamma g w₀ s) s (rotatedAnharmonic Q c lam alpha gamma))) (-∑ i,
      (_root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential
      (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i) (gamma i) x *
      anharmonicPotential (lam i) (alpha i) (gamma i) x))) - 4 * _root_.Laplace.gibbsExpectation
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x =>
      anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i)
      (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x)) *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) - 3 *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x * anharmonicPotential
      (lam i) (alpha i) (gamma i) x) ^ 2 + 12 * _root_.Laplace.gibbsExpectation (locPotential1 (lam
      i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => anharmonicPotential (lam i)
      (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x) *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 2 - 6 *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 4)) t := by
  have hderiv : (deriv (deriv fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
      gamma g w₀ s) s (rotatedAnharmonic Q c lam alpha gamma))) =ᶠ[𝓝 t] fun s => ∑ i,
      (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w =>
      anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) * (anharmonicPotential
      (lam i) (alpha i) (gamma i) (affineFrame Q c w i) * anharmonicPotential (lam i) (alpha i)
      (gamma i) (affineFrame Q c w i))) - 3 * (gibbsExpectation (localisedRotatedAnharmonic Q c lam
      alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q
      c w i) * anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) *
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w =>
      anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i))) + 2 *
      (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w =>
      anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) * (gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam
      i) (alpha i) (gamma i) (affineFrame Q c w i)) * gibbsExpectation (localisedRotatedAnharmonic Q
      c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i)
      (affineFrame Q c w i))))) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => by
      rw [(hasDerivAt_localised_energy_deriv hlam hgamma hdisc hQ c w₀ hg hs).deriv,
        localisedCum3_eq_frame_sum hlam hgamma hdisc hQ c w₀ hg hs]
  have h : HasDerivAt (fun s => ∑ i, (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
      gamma g w₀ s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w
      i) * (anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) *
      anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i))) - 3 *
      (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w =>
      anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i) * anharmonicPotential
      (lam i) (alpha i) (gamma i) (affineFrame Q c w i)) * gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam
      i) (alpha i) (gamma i) (affineFrame Q c w i))) + 2 * (gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam
      i) (alpha i) (gamma i) (affineFrame Q c w i)) * (gibbsExpectation (localisedRotatedAnharmonic
      Q c lam alpha gamma g w₀ s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i)
      (affineFrame Q c w i)) * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀
      s) s (fun w => anharmonicPotential (lam i) (alpha i) (gamma i) (affineFrame Q c w i)))))) (∑
      i, -(_root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame
      Q c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
      (anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i)
      (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x))) - 4 *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential
      (lam i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x)) *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) - 3 *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x * anharmonicPotential
      (lam i) (alpha i) (gamma i) x) ^ 2 + 12 * _root_.Laplace.gibbsExpectation (locPotential1 (lam
      i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x => anharmonicPotential (lam i)
      (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x) *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 2 - 6 *
      _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
      w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 4)) t :=
    HasDerivAt.fun_sum fun i _ =>
      hasDerivAt_localised_frame_cum3 hlam hgamma hdisc hQ c w₀ hg ht i
  refine (h.congr_of_eventuallyEq hderiv).congr_deriv ?_
  rw [Finset.sum_neg_distrib]

/-- **The LLC governs the third temperature derivative**: `|t⁴ ∂ₜ³⟨L∘A⟩_loc + 3d| ≤ K/t`, i.e.
`∂ₜ³⟨L∘A⟩_loc = −3d/t⁴ + O(t⁻⁵)` — minus the fourth cumulant `3!·(d/2)/t⁴` of a `Gamma(d/2, t)`
law. -/
theorem localisedEnergy_deriv3_leading (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * deriv (deriv (deriv fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam
        alpha gamma g w₀ s) s (rotatedAnharmonic Q c lam alpha gamma))) t + 3 * (d : ℝ)| ≤ K / t :=
        by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div (fun _ : Fin d => (1 : ℝ)) (fun i t => t ^ 4 *
    (_root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
    w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential
    (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i) (gamma i) x *
    anharmonicPotential (lam i) (alpha i) (gamma i) x))) - 4 * _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x =>
    anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i)
    (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x)) *
    _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀
    i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) - 3 * _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x =>
    anharmonicPotential (lam i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma
    i) x) ^ 2 + 12 * _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g
    (affineFrame Q c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
    anharmonicPotential (lam i) (alpha i) (gamma i) x) * _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (anharmonicPotential
    (lam i) (alpha i) (gamma i)) ^ 2 - 6 * _root_.Laplace.gibbsExpectation (locPotential1 (lam i)
    (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma
    i)) ^ 4) - 3) (fun i => locEnergyCum4_leading (hlam i) (hgamma i) (hdisc i) hg (x₀ :=
    affineFrame Q c w₀ i))
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [(hasDerivAt_localised_energy_deriv2 hlam hgamma hdisc hQ c w₀ hg ht0).deriv]
  have key : ∀ (F : Fin d → ℝ), t ^ 4 * (-∑ i, F i) + 3 * (d : ℝ) =
      -∑ i, (1 : ℝ) * (t ^ 4 * F i - 3) := by
    intro F
    simp only [one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [key, abs_neg]
  exact h ht

/-- **The normalised fourth-cumulant ratio**: `|∑ᵢκ₄,ᵢ / (∑ᵢ Var_loc,ᵢ(ℓᵢ))² − 12/d| ≤ K/t` for
`d > 0` — the excess kurtosis `6/(d/2) = 12/d` of a `Gamma(d/2)` law. -/
theorem localisedCum4_ratio_leading (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hd : 0 < d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |(∑ i, (_root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g
        (affineFrame Q c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
        (anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i)
        (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x))) - 4 *
        _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q
        c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
        (anharmonicPotential (lam i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i)
        (gamma i) x)) * _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g
        (affineFrame Q c w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) - 3 *
        _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q
        c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
        anharmonicPotential (lam i) (alpha i) (gamma i) x) ^ 2 + 12 *
        _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q
        c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
        anharmonicPotential (lam i) (alpha i) (gamma i) x) * _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 2 - 6 * _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) ^ 4)) / (∑ i, _root_.Laplace.gibbsCov
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) (anharmonicPotential (lam i) (alpha i)
        (gamma i))) ^ 2 - 12 / (d : ℝ)| ≤ K / t := by
  obtain ⟨KH, TH, hKH, hTH, hH⟩ := sum_rate_div (fun _ : Fin d => (1 : ℝ)) (fun i t => t ^ 4 *
    (_root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
    w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential
    (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i) (gamma i) x *
    anharmonicPotential (lam i) (alpha i) (gamma i) x))) - 4 * _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x =>
    anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i)
    (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x)) *
    _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀
    i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) - 3 * _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x =>
    anharmonicPotential (lam i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma
    i) x) ^ 2 + 12 * _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g
    (affineFrame Q c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
    anharmonicPotential (lam i) (alpha i) (gamma i) x) * _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (anharmonicPotential
    (lam i) (alpha i) (gamma i)) ^ 2 - 6 * _root_.Laplace.gibbsExpectation (locPotential1 (lam i)
    (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma
    i)) ^ 4) - 3) (fun i => locEnergyCum4_leading (hlam i) (hgamma i) (hdisc i) hg (x₀ :=
    affineFrame Q c w₀ i))
  obtain ⟨KV, TV, hKV, hTV, hV⟩ := localisedVar_energy_leading hlam hgamma hdisc hQ c w₀ hg
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hT8 : (0 : ℝ) ≤ 8 * KV / d := by positivity
  refine ⟨2 * KH / ((d : ℝ) / 2) ^ 2 +
    2 * |3 * (d : ℝ)| * (2 * |(d : ℝ) / 2| * KV + KV ^ 2) / (((d : ℝ) / 2) ^ 2) ^ 2,
    TH + TV + 8 * KV / d, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hHt := hH (t := t) (by linarith)
  have hVt := hV (t := t) (by linarith)
  have key : ∀ (F : Fin d → ℝ), ∑ i, (1 : ℝ) * (t ^ 4 * F i - 3) =
      t ^ 4 * ∑ i, F i - 3 * (d : ℝ) := by
    intro F
    simp only [one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [key] at hHt
  rw [localisedVar_energy_eq_sum hlam hgamma hdisc hQ c w₀ hg ht0] at hVt
  set H := ∑ i, (_root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g
    (affineFrame Q c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
    (anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam i) (alpha i)
    (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x))) - 4 *
    _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀
    i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x * (anharmonicPotential (lam
    i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma i) x)) *
    _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀
    i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) - 3 * _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (fun x =>
    anharmonicPotential (lam i) (alpha i) (gamma i) x * anharmonicPotential (lam i) (alpha i) (gamma
    i) x) ^ 2 + 12 * _root_.Laplace.gibbsExpectation (locPotential1 (lam i) (alpha i) (gamma i) g
    (affineFrame Q c w₀ i) t) t (fun x => anharmonicPotential (lam i) (alpha i) (gamma i) x *
    anharmonicPotential (lam i) (alpha i) (gamma i) x) * _root_.Laplace.gibbsExpectation
    (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (anharmonicPotential
    (lam i) (alpha i) (gamma i)) ^ 2 - 6 * _root_.Laplace.gibbsExpectation (locPotential1 (lam i)
    (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma
    i)) ^ 4) with hHdef
  set V := ∑ i, _root_.Laplace.gibbsCov (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q
    c w₀ i) t) t (anharmonicPotential (lam i) (alpha i) (gamma i)) (anharmonicPotential (lam i)
    (alpha i) (gamma i)) with hVdef
  have hKVt : KV / t ≤ (d : ℝ) / 8 := by
    have h8 : 8 * KV / (d : ℝ) ≤ t := by linarith
    rw [div_le_iff₀ hd'] at h8
    rw [div_le_iff₀ ht0]
    linarith
  have hlow : 3 * (d : ℝ) / 8 ≤ t ^ 2 * V := by
    have := (abs_le.mp hVt).1
    linarith
  have hb2 : ((d : ℝ) / 2) ^ 2 / 2 ≤ (t ^ 2 * V) ^ 2 := by
    have h1 : (3 * (d : ℝ) / 8) ^ 2 ≤ (t ^ 2 * V) ^ 2 := pow_le_pow_left₀ (by positivity) hlow 2
    nlinarith
  have hsq := sq_rate ht1 hKV hVt
  have hr := ratio_rate (a := t ^ 4 * H) (b := (t ^ 2 * V) ^ 2) (a₀ := 3 * (d : ℝ))
    (L := ((d : ℝ) / 2) ^ 2) (by positivity) hKH (by positivity) ht0 hb2 hHt hsq
  have e1 : t ^ 4 * H / (t ^ 2 * V) ^ 2 = H / V ^ 2 := by
    have e0 : (t ^ 2 * V) ^ 2 = t ^ 4 * V ^ 2 := by ring
    rw [e0, mul_div_mul_left _ _ (by positivity : (t : ℝ) ^ 4 ≠ 0)]
  have e2 : 3 * (d : ℝ) / ((d : ℝ) / 2) ^ 2 = 12 / d := by
    field_simp
    ring
  rw [e1, e2] at hr
  exact hr

/-- **The derivative-response form of the excess kurtosis**:
`|(−∂ₜ³⟨L∘A⟩_loc)/(∂ₜ⟨L∘A⟩_loc)² − 12/d| ≤ K/t` for `d > 0`. -/
theorem localisedEnergy_deriv3_ratio_leading (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hd : 0 < d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |(-deriv (deriv (deriv fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
        gamma g w₀ s) s (rotatedAnharmonic Q c lam alpha gamma))) t) / (deriv (fun s =>
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (rotatedAnharmonic Q c lam alpha gamma)) t) ^ 2 - 12 / (d : ℝ)| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedCum4_ratio_leading hlam hgamma hdisc hQ c w₀ hg hd
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e1 : deriv (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s)
      s (rotatedAnharmonic Q c lam alpha gamma)) t = -∑ i, _root_.Laplace.gibbsCov (locPotential1
      (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t (anharmonicPotential (lam i) (alpha
      i) (gamma i)) (anharmonicPotential (lam i) (alpha i) (gamma i)) := by
    rw [← localisedVar_energy_eq_sum hlam hgamma hdisc hQ c w₀ hg ht0]
    exact neg_eq_iff_eq_neg.mp (localisedEnergy_neg_deriv_eq_var hlam hgamma hdisc hQ c w₀ hg ht0)
  rw [(hasDerivAt_localised_energy_deriv2 hlam hgamma hdisc hQ c w₀ hg ht0).deriv, neg_neg, e1,
    neg_sq]
  exact h ht

end Multi

end Laplace.Multi
