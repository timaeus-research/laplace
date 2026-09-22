/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedAnharmonicMulti

/-!
# eq:mean's `O(S²)` remainder on the exact localised anharmonic measure

Tides `localised-mean-1d` and `localised-mean-multi` certified eq:mean's two terms on the exact
localised anharmonic measure to `O(t^{−3/2})`, one half power short of the note's `O(S²) = O(t⁻²)`,
because the first-order expansion of the localised weight `φ = e^{y}`, `y = g x₀ x − (g/2)x²`,
left odd absolute moments. Expanding to second order, `|e^y − 1 − y − y²/2| ≤ (e^M + 3)|y|³`
(`abs_exp_sub_taylor2_le`), the remainder of `xφ` is controlled by *even* powers only
(`locNumerator_pointwise`: `|xφ − x − g x₀ x² − c₂ x³| ≤ A x⁴ + B x⁶ + C x⁸`,
`c₂ = (g²x₀² − g)/2`), and the signed third moment enters through the seabed's
`oddMoment_anharmonic_rate`. Results:

* `localisedMean_anharmonic_rate_sharp`: `|t⟨x⟩_loc − (−α/(2λ²) + g x₀/λ)| ≤ K/t`;
* `localisedMean_sub_locLeading_rate_sharp`: `|⟨x⟩_loc − P_t| ≤ K/t²` with
  `P_t = −αt/(2(tλ + g)²) + g x₀/(tλ + g)` — eq:mean's `O(S²)` remainder in one dimension;
* `localisedRotatedAnharmonic_displayed_rate_sharp`: on E2's rotated oscillator with the isotropic
  localiser, `|(⟨w⟩_loc − c − meanShiftLoc − g (tH + gI)⁻¹(w₀ − c))ⱼ| ≤ K/t²` for every ambient
  coordinate — the displayed eq:mean with its `O(S²)` remainder, `S = (tH + gI)⁻¹ = O(1/t)`.
-/

open Real MeasureTheory Filter Topology Matrix
open scoped Nat

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

/-! ### The second-order expansion of the localised weight -/

section Weight

variable {g x₀ : ℝ}

/-- `|e^y − 1 − y − y²/2| ≤ (e^M + 3)|y|³` for `y ≤ M`. -/
theorem abs_exp_sub_taylor2_le {y M : ℝ} (hy : y ≤ M) :
    |Real.exp y - 1 - y - y ^ 2 / 2| ≤ (Real.exp M + 3) * |y| ^ 3 := by
  have hy3 : 0 ≤ |y| ^ 3 := by positivity
  rcases le_or_gt |y| 1 with h1 | h1
  · have h := Real.exp_bound h1 (n := 3) (by norm_num)
    have hs : Real.exp y - 1 - y - y ^ 2 / 2 =
        Real.exp y - ∑ m ∈ Finset.range 3, y ^ m / (m.factorial : ℝ) := by
      simp [Finset.sum_range_succ, Nat.factorial]
      ring
    have hc : (((3 : ℕ).succ : ℕ) : ℝ) / (((3 : ℕ).factorial : ℝ) * ((3 : ℕ) : ℝ)) ≤ 3 := by
      norm_num [Nat.factorial]
    calc |Real.exp y - 1 - y - y ^ 2 / 2|
        = |Real.exp y - ∑ m ∈ Finset.range 3, y ^ m / (m.factorial : ℝ)| := by rw [hs]
      _ ≤ |y| ^ 3 * ((((3 : ℕ).succ : ℕ) : ℝ) / (((3 : ℕ).factorial : ℝ) * ((3 : ℕ) : ℝ))) := h
      _ ≤ |y| ^ 3 * 3 := by gcongr
      _ ≤ (Real.exp M + 3) * |y| ^ 3 := by nlinarith [Real.exp_pos M]
  · have hy1 : |y| ≤ |y| ^ 3 := by
      have : 1 ≤ |y| ^ 2 := one_le_pow₀ h1.le
      nlinarith [abs_nonneg y]
    have hy2 : y ^ 2 ≤ |y| ^ 3 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg y, sq_nonneg |y|]
    have hexp : Real.exp y ≤ Real.exp M := Real.exp_le_exp.mpr hy
    have h13 : 1 ≤ |y| ^ 3 := one_le_pow₀ h1.le
    calc |Real.exp y - 1 - y - y ^ 2 / 2|
        = |Real.exp y - (1 + y + y ^ 2 / 2)| := by ring_nf
      _ ≤ |Real.exp y| + |1 + y + y ^ 2 / 2| := abs_sub _ _
      _ ≤ Real.exp M + (1 + |y| + y ^ 2 / 2) := by
          gcongr
          · rw [abs_of_pos (Real.exp_pos _)]; exact hexp
          · calc |1 + y + y ^ 2 / 2| ≤ |1 + y| + |y ^ 2 / 2| := abs_add_le _ _
              _ ≤ 1 + |y| + y ^ 2 / 2 := by
                  gcongr
                  · exact (abs_add_le 1 y).trans (by rw [abs_one])
                  · rw [abs_of_nonneg (by positivity)]
      _ ≤ (Real.exp M + 3) * |y| ^ 3 := by nlinarith [Real.exp_pos M]

/-- The localised weight to second order: `|φ − 1 − y − y²/2| ≤ (e^{g x₀²/2} + 3)|y|³`,
`y = g x₀ x − (g/2)x²`. -/
theorem locWeight_taylor2 (hg : 0 ≤ g) (x : ℝ) :
    |locWeight g x₀ x - 1 - (g * x₀ * x - g / 2 * x ^ 2) - (g * x₀ * x - g / 2 * x ^ 2) ^ 2 / 2| ≤
      (Real.exp (g * x₀ ^ 2 / 2) + 3) * |g * x₀ * x - g / 2 * x ^ 2| ^ 3 := by
  have hyM : g * x₀ * x - g / 2 * x ^ 2 ≤ g * x₀ ^ 2 / 2 := by
    nlinarith [mul_nonneg hg (sq_nonneg (x - x₀))]
  exact abs_exp_sub_taylor2_le hyM

theorem cube_add_le (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) : (p + q) ^ 3 ≤ 4 * (p ^ 3 + q ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hp hq) (sq_nonneg (p - q))]

/-- `|y|³ ≤ 4(|g x₀|³|x|³ + (g/2)³x⁶)`. -/
theorem abs_locExponent_cube_le (hg : 0 ≤ g) (x : ℝ) :
    |g * x₀ * x - g / 2 * x ^ 2| ^ 3 ≤ 4 * (|g * x₀| ^ 3 * |x| ^ 3 + (g / 2) ^ 3 * x ^ 6) := by
  have h1 : |g * x₀ * x - g / 2 * x ^ 2| ≤ |g * x₀| * |x| + g / 2 * x ^ 2 := by
    calc |g * x₀ * x - g / 2 * x ^ 2| ≤ |g * x₀ * x| + |g / 2 * x ^ 2| := abs_sub _ _
      _ = |g * x₀| * |x| + g / 2 * x ^ 2 := by
          rw [abs_mul (g * x₀) x, abs_mul (g / 2) (x ^ 2),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ g / 2), abs_of_nonneg (sq_nonneg x)]
  calc |g * x₀ * x - g / 2 * x ^ 2| ^ 3 ≤ (|g * x₀| * |x| + g / 2 * x ^ 2) ^ 3 := by gcongr
    _ ≤ 4 * ((|g * x₀| * |x|) ^ 3 + (g / 2 * x ^ 2) ^ 3) :=
        cube_add_le _ _ (by positivity) (by positivity)
    _ = 4 * (|g * x₀| ^ 3 * |x| ^ 3 + (g / 2) ^ 3 * x ^ 6) := by ring

/-- The numerator's remainder is even: with `c₂ = (g²x₀² − g)/2`,
`|xφ − x − g x₀ x² − c₂ x³| ≤ A x⁴ + B x⁶ + C x⁸`. -/
theorem locNumerator_pointwise (hg : 0 ≤ g) (x : ℝ) :
    |x * locWeight g x₀ x - x - g * x₀ * x ^ 2 - (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 3| ≤
      (4 * (Real.exp (g * x₀ ^ 2 / 2) + 3) * |g * x₀| ^ 3 + g ^ 2 * |x₀| / 2 + g ^ 2 / 16) * x ^ 4 +
        (2 * (Real.exp (g * x₀ ^ 2 / 2) + 3) * (g / 2) ^ 3 + g ^ 2 / 16) * x ^ 6 +
        2 * (Real.exp (g * x₀ ^ 2 / 2) + 3) * (g / 2) ^ 3 * x ^ 8 := by
  set y := g * x₀ * x - g / 2 * x ^ 2 with hy
  set E := Real.exp (g * x₀ ^ 2 / 2) + 3 with hE
  have hE0 : 0 ≤ E := by positivity
  have hT : |locWeight g x₀ x - 1 - y - y ^ 2 / 2| ≤ E * |y| ^ 3 := locWeight_taylor2 hg x
  have hy3 : |y| ^ 3 ≤ 4 * (|g * x₀| ^ 3 * |x| ^ 3 + (g / 2) ^ 3 * x ^ 6) :=
    abs_locExponent_cube_le hg x
  have e : x * locWeight g x₀ x - x - g * x₀ * x ^ 2 - (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 3 =
      x * (locWeight g x₀ x - 1 - y - y ^ 2 / 2) +
        (-(g ^ 2 * x₀ / 2) * x ^ 4 + g ^ 2 / 8 * x ^ 5) := by
    rw [hy]; ring
  have hx4 : x ^ 4 = |x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx6 : x ^ 6 = |x| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : x ^ 8 = |x| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h5 : |x| ^ 5 ≤ (|x| ^ 4 + |x| ^ 6) / 2 := by nlinarith [sq_nonneg (|x| ^ 2 - |x| ^ 3)]
  have h7 : |x| ^ 7 ≤ (|x| ^ 6 + |x| ^ 8) / 2 := by nlinarith [sq_nonneg (|x| ^ 3 - |x| ^ 4)]
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hgx : 0 ≤ |g * x₀| ^ 3 := by positivity
  have hg3 : 0 ≤ (g / 2) ^ 3 := by positivity
  have hmain : |x * (locWeight g x₀ x - 1 - y - y ^ 2 / 2) +
        (-(g ^ 2 * x₀ / 2) * x ^ 4 + g ^ 2 / 8 * x ^ 5)|
      ≤ |x| * (E * (4 * (|g * x₀| ^ 3 * |x| ^ 3 + (g / 2) ^ 3 * x ^ 6))) +
        (g ^ 2 * |x₀| / 2 * |x| ^ 4 + g ^ 2 / 8 * |x| ^ 5) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul x]
    gcongr
    · exact hT.trans (mul_le_mul_of_nonneg_left hy3 hE0)
    · calc |-(g ^ 2 * x₀ / 2) * x ^ 4 + g ^ 2 / 8 * x ^ 5|
          ≤ |-(g ^ 2 * x₀ / 2) * x ^ 4| + |g ^ 2 / 8 * x ^ 5| := abs_add_le _ _
        _ = g ^ 2 * |x₀| / 2 * |x| ^ 4 + g ^ 2 / 8 * |x| ^ 5 := by
            simp only [abs_mul, abs_neg, abs_div, abs_pow, abs_of_nonneg hg, abs_two,
              abs_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num)]
  rw [e]
  refine hmain.trans ?_
  rw [hx4, hx6, hx8]
  have hx4' : |x| * |x| ^ 3 = |x| ^ 4 := by ring
  have hx7' : |x| * |x| ^ 6 = |x| ^ 7 := by ring
  have hE7 := mul_le_mul_of_nonneg_left h7 (by positivity : 0 ≤ 4 * E * (g / 2) ^ 3)
  nlinarith [hE7, h5, mul_nonneg hE0 hgx, mul_nonneg hE0 hg3, hx4', hx7']

/-- The three constants of `locNumerator_pointwise`. -/
noncomputable def locA (g x₀ : ℝ) : ℝ :=
  4 * (Real.exp (g * x₀ ^ 2 / 2) + 3) * |g * x₀| ^ 3 + g ^ 2 * |x₀| / 2 + g ^ 2 / 16

noncomputable def locB (g x₀ : ℝ) : ℝ :=
  2 * (Real.exp (g * x₀ ^ 2 / 2) + 3) * (g / 2) ^ 3 + g ^ 2 / 16

noncomputable def locC (g x₀ : ℝ) : ℝ := 2 * (Real.exp (g * x₀ ^ 2 / 2) + 3) * (g / 2) ^ 3

theorem locA_nonneg (g x₀ : ℝ) : 0 ≤ locA g x₀ := by unfold locA; positivity

theorem locB_nonneg (hg : 0 ≤ g) : 0 ≤ locB g x₀ := by unfold locB; positivity

theorem locC_nonneg (hg : 0 ≤ g) : 0 ≤ locC g x₀ := by unfold locC; positivity

theorem locNumerator_pointwise' (hg : 0 ≤ g) (x : ℝ) :
    |x * locWeight g x₀ x - x - g * x₀ * x ^ 2 - (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 3| ≤
      locA g x₀ * x ^ 4 + locB g x₀ * x ^ 6 + locC g x₀ * x ^ 8 :=
  locNumerator_pointwise hg x

end Weight

/-! ### Three-term linearity -/

theorem gibbs_lin3 {L : ℝ → ℝ} {t a b c : ℝ} {f h k : ℝ → ℝ}
    (hf : Integrable (fun x => f x * Real.exp (-(t * L x))))
    (hh : Integrable (fun x => h x * Real.exp (-(t * L x))))
    (hk : Integrable (fun x => k x * Real.exp (-(t * L x)))) :
    _root_.Laplace.gibbsExpectation L t (fun x => a * f x + b * h x + c * k x) =
      a * _root_.Laplace.gibbsExpectation L t f + b * _root_.Laplace.gibbsExpectation L t h +
        c * _root_.Laplace.gibbsExpectation L t k := by
  have h1 : Integrable (fun x => (a * f x + b * h x) * Real.exp (-(t * L x))) := by
    have := (hf.const_mul a).add (hh.const_mul b)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have e : (fun x => a * f x + b * h x + c * k x) =
      fun x => 1 * (a * f x + b * h x) + c * k x := by
    funext x; ring
  rw [e, gibbsExpectation_lin h1 hk, gibbsExpectation_lin hf hh]
  ring

/-! ### The numerator at order `1/t` -/

section Anharmonic

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `|⟨xφ⟩ − ⟨x⟩ − g x₀⟨x²⟩ − c₂⟨x³⟩| ≤ A⟨x⁴⟩ + B⟨x⁶⟩ + C⟨x⁸⟩`, `c₂ = (g²x₀² − g)/2`. -/
theorem locNumerator_expansion2 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x * locWeight g x₀ x) -
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x) -
      g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2) -
      (g ^ 2 * x₀ ^ 2 - g) / 2 *
        _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3)| ≤
      locA g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locB g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locC g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_mul_locWeight hlam hgamma hdisc hg ht (x₀ := x₀)
  have h1 := integrable_pow_exp' hlam hgamma hdisc ht 1
  simp only [pow_one] at h1
  have h2 := integrable_pow_exp' hlam hgamma hdisc ht 2
  have h3 := integrable_pow_exp' hlam hgamma hdisc ht 3
  have hF3 : Integrable (fun x => (x * locWeight g x₀ x - x - g * x₀ * x ^ 2) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (hf.sub h1).sub (h2.const_mul (g * x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hF : Integrable (fun x => (x * locWeight g x₀ x - x - g * x₀ * x ^ 2 -
      (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 3) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := hF3.sub (h3.const_mul ((g ^ 2 * x₀ ^ 2 - g) / 2))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locA g x₀ * x ^ 4 + locB g x₀ * x ^ 6 + locC g x₀ * x ^ 8) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (((integrable_pow_exp' hlam hgamma hdisc ht 4).const_mul (locA g x₀)).add
      ((integrable_pow_exp' hlam hgamma hdisc ht 6).const_mul (locB g x₀))).add
      ((integrable_pow_exp' hlam hgamma hdisc ht 8).const_mul (locC g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hsplit : (fun x => x * locWeight g x₀ x - x - g * x₀ * x ^ 2 -
      (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 3) =
      fun x => 1 * (x * locWeight g x₀ x - x - g * x₀ * x ^ 2) +
        (-((g ^ 2 * x₀ ^ 2 - g) / 2)) * x ^ 3 := by
    funext x; ring
  rw [← gibbs_sub_sub hf h1 h2, ← gibbs_lin3 (integrable_pow_exp' hlam hgamma hdisc ht 4)
    (integrable_pow_exp' hlam hgamma hdisc ht 6) (integrable_pow_exp' hlam hgamma hdisc ht 8)]
  have e : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x * locWeight g x₀ x - x - g * x₀ * x ^ 2) -
      (g ^ 2 * x₀ ^ 2 - g) / 2 * _root_.Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x * locWeight g x₀ x - x - g * x₀ * x ^ 2 -
          (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 3) := by
    rw [hsplit, gibbsExpectation_lin hF3 h3]
    ring
  rw [e]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG
      fun x => locNumerator_pointwise' hg x)

/-- `|t⟨x³⟩| ≤ M/t` eventually, from the seabed's signed third-moment rate. -/
theorem thirdMoment_bound :
    ∃ M T : ℝ, 0 ≤ M ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 3)| ≤ M / t := by
  obtain ⟨K, T, hK, hT, h⟩ := Laplace.OneD.oddMoment_anharmonic_rate hlam hgamma hdisc 1
  simp only [show (2 * 1 + 1 : ℕ) = 3 from rfl, show (1 + 1 : ℕ) = 2 from rfl,
    show (2 * 1 + 3 : ℕ) = 5 from rfl] at h
  refine ⟨|alpha * ((5 : ℕ)‼ : ℝ) / (6 * lam ^ 3)| + K, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have h' : |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 3) - -(alpha * ((5 : ℕ)‼ : ℝ) / (6 * lam ^ 3))| ≤ K / t := by
    rw [sub_neg_eq_add]
    exact h ht
  have hb := Laplace.OneD.rate_bounded ht1 hK h'
  rw [abs_neg] at hb
  have e : t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 3) = (t ^ 2 * _root_.Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3)) / t := by
    field_simp
  rw [e, abs_div, abs_of_pos ht0]
  exact div_le_div_of_nonneg_right hb ht0.le

/-- **The numerator at its sharp rate**: `|t⟨xφ⟩ − (−α/(2λ²) + g x₀/λ)| ≤ K/t`. -/
theorem locNumerator_rate_sharp (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x * locWeight g x₀ x) - (-alpha / (2 * lam ^ 2) + g * x₀ / lam)| ≤ K / t := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := Laplace.OneD.mean_anharmonic_O2_rate hlam hgamma hdisc
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := Laplace.OneD.evenMoment_anharmonic_rate hlam hgamma hdisc 1
  obtain ⟨M₃, T₃, hM₃, hT₃, h₃⟩ := thirdMoment_bound hlam hgamma hdisc
  obtain ⟨C₄, T₄, hC₄, hT₄, h₄⟩ := evenMoment_bound hlam hgamma hdisc 2
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  simp only [show (2 * 2 : ℕ) = 4 from rfl, show (2 * 3 : ℕ) = 6 from rfl,
    show (2 * 4 : ℕ) = 8 from rfl] at h₄ h₆ h₈
  have hA := locA_nonneg g x₀
  have hB := locB_nonneg (x₀ := x₀) hg
  have hC := locC_nonneg (x₀ := x₀) hg
  refine ⟨K₁ + |g * x₀| * K₂ + |(g ^ 2 * x₀ ^ 2 - g) / 2| * M₃ +
      (locA g x₀ * C₄ + locB g x₀ * C₆ + locC g x₀ * C₈), T₁ + T₂ + T₃ + T₄ + T₆ + T₈,
    by positivity, by linarith, fun {t} ht => ?_⟩
  have hT₁t : T₁ ≤ t := by linarith
  have hT₂t : T₂ ≤ t := by linarith
  have hT₃t : T₃ ≤ t := by linarith
  have hT₄t : T₄ ≤ t := by linarith
  have hT₆t : T₆ ≤ t := by linarith
  have hT₈t : T₈ ≤ t := by linarith
  have ht1 : 1 ≤ t := hT₁.trans hT₁t
  have ht0 : 0 < t := by linarith
  have e₁ := h₁ hT₁t
  have e₂ : |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 2) - 1 / lam| ≤ K₂ / t := by
    simpa [Nat.doubleFactorial] using h₂ hT₂t
  have e₃ := h₃ hT₃t
  have hR := (locNumerator_expansion2 hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h₄ hT₄t) hA)
      (mul_le_mul_of_nonneg_left (h₆ hT₆t) hB)) (mul_le_mul_of_nonneg_left (h₈ hT₈t) hC))
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x * locWeight g x₀ x) with hN
  set M₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x) with hM₁
  set M₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2) with hM₂
  set M₃' := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3) with hM₃'
  set c₂ := (g ^ 2 * x₀ ^ 2 - g) / 2 with hc₂
  have key : t * N - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) =
      ((t * M₁ - -alpha / (2 * lam ^ 2)) + g * x₀ * (t * M₂ - 1 / lam) + c₂ * (t * M₃')) +
        t * (N - M₁ - g * x₀ * M₂ - c₂ * M₃') := by ring
  have htt : t ≤ t ^ 2 := by nlinarith
  have htt3 : t ≤ t ^ 3 := by nlinarith
  have hRt : t * (locA g x₀ * (C₄ / t ^ 2) + locB g x₀ * (C₆ / t ^ 3) + locC g x₀ * (C₈ / t ^ 4)) ≤
      (locA g x₀ * C₄ + locB g x₀ * C₆ + locC g x₀ * C₈) / t := by
    have e : t * (locA g x₀ * (C₄ / t ^ 2) + locB g x₀ * (C₆ / t ^ 3) + locC g x₀ * (C₈ / t ^ 4)) =
        locA g x₀ * C₄ / t + locB g x₀ * C₆ / t ^ 2 + locC g x₀ * C₈ / t ^ 3 := by
      field_simp
    have h6 : locB g x₀ * C₆ / t ^ 2 ≤ locB g x₀ * C₆ / t :=
      div_le_div_of_nonneg_left (by positivity) ht0 htt
    have h8 : locC g x₀ * C₈ / t ^ 3 ≤ locC g x₀ * C₈ / t :=
      div_le_div_of_nonneg_left (by positivity) ht0 htt3
    rw [e, add_div, add_div]
    linarith
  rw [key]
  calc |(t * M₁ - -alpha / (2 * lam ^ 2)) + g * x₀ * (t * M₂ - 1 / lam) + c₂ * (t * M₃') +
        t * (N - M₁ - g * x₀ * M₂ - c₂ * M₃')|
      ≤ |(t * M₁ - -alpha / (2 * lam ^ 2)) + g * x₀ * (t * M₂ - 1 / lam) + c₂ * (t * M₃')| +
          |t * (N - M₁ - g * x₀ * M₂ - c₂ * M₃')| := abs_add_le _ _
    _ ≤ |t * M₁ - -alpha / (2 * lam ^ 2)| + |g * x₀ * (t * M₂ - 1 / lam)| + |c₂ * (t * M₃')| +
          |t * (N - M₁ - g * x₀ * M₂ - c₂ * M₃')| :=
        add_le_add (abs_add_three _ _ _) le_rfl
    _ = |t * M₁ - -alpha / (2 * lam ^ 2)| + |g * x₀| * |t * M₂ - 1 / lam| + |c₂| * |t * M₃'| +
          t * |N - M₁ - g * x₀ * M₂ - c₂ * M₃'| := by
        rw [abs_mul (g * x₀), abs_mul c₂, abs_mul t (N - M₁ - g * x₀ * M₂ - c₂ * M₃'),
          abs_of_pos ht0]
    _ ≤ K₁ / t + |g * x₀| * (K₂ / t) + |c₂| * (M₃ / t) +
          t * (locA g x₀ * (C₄ / t ^ 2) + locB g x₀ * (C₆ / t ^ 3) + locC g x₀ * (C₈ / t ^ 4)) := by
        gcongr
    _ ≤ K₁ / t + |g * x₀| * (K₂ / t) + |c₂| * (M₃ / t) +
          (locA g x₀ * C₄ + locB g x₀ * C₆ + locC g x₀ * C₈) / t := by gcongr
    _ = (K₁ + |g * x₀| * K₂ + |c₂| * M₃ +
          (locA g x₀ * C₄ + locB g x₀ * C₆ + locC g x₀ * C₈)) / t := by ring

/-- **eq:mean's localisation term at its sharp rate (1D)**:
`|t⟨x⟩_loc − (−α/(2λ²) + g x₀/λ)| ≤ K/t`. -/
theorem localisedMean_anharmonic_rate_sharp (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * localisedMean lam alpha gamma g x₀ t - (-alpha / (2 * lam ^ 2) + g * x₀ / lam)| ≤
        K / t := by
  obtain ⟨KN, TN, hKN, hTN, hN⟩ := locNumerator_rate_sharp hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate hlam hgamma hdisc hg (x₀ := x₀)
  set c := -alpha / (2 * lam ^ 2) + g * x₀ / lam with hc
  refine ⟨2 * KN + 2 * |c| * KD, max (max TN TD) (2 * KD), by positivity,
    le_max_of_le_left (le_max_of_le_left hTN), fun {t} ht => ?_⟩
  have hTNt : TN ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht)
  have hTDt : TD ≤ t := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ht)
  have h2K : 2 * KD ≤ t := le_trans (le_max_right _ _) ht
  have ht1 : 1 ≤ t := hTN.trans hTNt
  have ht0 : 0 < t := by linarith
  rw [localisedMean_eq_ratio hlam hgamma hdisc ht0]
  have eN := hN hTNt
  have eD := hD hTDt
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x * locWeight g x₀ x) with hNdef
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
  have hDhalf : 1 / 2 ≤ D := by
    have h1 : KD / t ≤ 1 / 2 := by rw [div_le_iff₀ ht0]; linarith
    have h2 := (abs_le.mp (eD.trans h1)).1
    linarith
  have hD0 : 0 < D := by linarith
  have hDne : D ≠ 0 := hD0.ne'
  have key : t * (N / D) - c = ((t * N - c) + c * (1 - D)) / D := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  calc |(t * N - c) + c * (1 - D)| ≤ |t * N - c| + |c| * |1 - D| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ KN / t + |c| * (KD / t) := by rw [abs_sub_comm 1 D]; gcongr
    _ = (2 * KN + 2 * |c| * KD) / t * (1 / 2) := by ring
    _ ≤ (2 * KN + 2 * |c| * KD) / t * D := by gcongr

/-- **eq:mean's `O(S²)` remainder in one dimension**: `|⟨x⟩_loc − P_t| ≤ K/t²` with
`P_t = −αt/(2(tλ + g)²) + g x₀/(tλ + g)` the displayed right-hand side (`S = (tλ + g)⁻¹`). -/
theorem localisedMean_sub_locLeading_rate_sharp (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |localisedMean lam alpha gamma g x₀ t - locLeading lam alpha g x₀ t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedMean_anharmonic_rate_sharp hlam hgamma hdisc hg (x₀ := x₀)
  set c := -alpha / (2 * lam ^ 2) + g * x₀ / lam with hc
  set K' := |alpha| / 2 * (2 * lam * g + g ^ 2) / lam ^ 4 + g ^ 2 * |x₀| / lam ^ 2 with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨K + K', T, by positivity, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  set m := localisedMean lam alpha gamma g x₀ t with hm
  have h1 : |m - c / t| ≤ K / t ^ 2 := by
    have e : m - c / t = (t * m - c) / t := by field_simp
    rw [e, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    calc |t * m - c| ≤ K / t := h ht
      _ = K / t ^ 2 * t := by field_simp
  have h2 := locLeading_sub_le hlam hg ht1 (alpha := alpha) (x₀ := x₀)
  calc |m - locLeading lam alpha g x₀ t|
      = |(m - c / t) - (locLeading lam alpha g x₀ t - c / t)| := by rw [sub_sub_sub_cancel_right]
    _ ≤ |m - c / t| + |locLeading lam alpha g x₀ t - c / t| := abs_sub _ _
    _ ≤ K / t ^ 2 + K' / t ^ 2 := add_le_add h1 h2
    _ = (K + K') / t ^ 2 := by ring

end Anharmonic

/-! ### `d` dimensions: E2's oscillator with the isotropic localiser -/

theorem sum_rate_div_sq {κ : Type*} [Fintype κ] (a : κ → ℝ) (e : κ → ℝ → ℝ)
    (h : ∀ i, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |e i t| ≤ K / t ^ 2) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |∑ i, a i * e i t| ≤ K / t ^ 2 := by
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
    _ ≤ ∑ i, |a i| * (K i / t ^ 2) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i (hTi i)) (abs_nonneg _)
    _ = (∑ i, |a i| * K i) / t ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring

section E2

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- The frame coordinates of eq:mean at the sharp rate `K/t`. -/
theorem localisedRotatedAnharmonic_frame_rate_sharp (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (i : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i) -
        (-alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i)| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedMean_anharmonic_rate_sharp (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [localisedRotatedAnharmonic_frame_coord hQ c w₀ hlam hgamma hdisc hg ht0 i]
  exact h ht

/-- **eq:mean with its `O(S²)` remainder on E2's exact localised measure**: for every ambient
coordinate, `|(⟨w⟩_loc − c − meanShiftLoc − g (tH + gI)⁻¹(w₀ − c))ⱼ| ≤ K/t²`; since
`‖(tH + gI)⁻¹‖ = 1/(tλ_min + g)`, this is the displayed formula's `O(S²)` remainder. -/
theorem localisedRotatedAnharmonic_displayed_rate_sharp (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (j : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j) -
        c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sq (fun i => Q j i)
    (fun i t => localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) t)
    (fun i => localisedMean_sub_locLeading_rate_sharp (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => w j) - c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j =
      ∑ i, Q j i * (localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
        locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) t) := by
    rw [localisedRotatedAnharmonic_ambient_coord hQ c w₀ hlam hgamma hdisc hg ht0 j,
      displayed_mean_rot hQ hlam hg ht0 alpha c w₀]
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [key]
  exact h ht

end E2

end Laplace.Multi
