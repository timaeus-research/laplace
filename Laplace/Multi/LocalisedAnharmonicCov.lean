/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedAnharmonicSharp

/-!
# eq:cov with the localiser on the exact localised anharmonic measure

E3 localises the posterior with `(γ/2)|w − w₀|²` and eq:cov then reads `Σ = S + O(S²)`,
`S = (tH + γI)⁻¹`. On the exact one-dimensional localised anharmonic measure the variance is
`Var_loc = ⟨x²φ⟩/⟨φ⟩ − (⟨xφ⟩/⟨φ⟩)²` with the localised weight `φ` (`localisedVar_eq`); the
second-order expansion of `x²φ` has an even remainder (`locSecond_pointwise`), so

* `localisedVar_rate`: `|t·Var_loc − 1/λ| ≤ K/t`;
* `localisedVar_sub_displayed_rate`: `|Var_loc − 1/(tλ + g)| ≤ K/t²` — eq:cov's `O(S²)` remainder.

On E2's rotated oscillator with the isotropic localiser the frame covariances vanish by
separability, `Cov_loc[wⱼ, wₖ] = ∑ᵢ QⱼᵢQₖᵢ Var_loc,i` (`localisedRotatedAnharmonic_cov_coord`), and
`localisedRotatedAnharmonic_cov_rate`: `|Cov_loc[wⱼ, wₖ] − ((tH + gI)⁻¹)ⱼₖ| ≤ K/t²` — the displayed
eq:cov with its `O(S²)` remainder on the exact localised measure.
-/

open Real MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

/-! ### The second-order expansion of `x²φ` -/

section Weight

variable {g x₀ : ℝ}

/-- The constants of `locSecond_pointwise`. -/
noncomputable def locQ₄ (g x₀ : ℝ) : ℝ :=
  2 * (Real.exp (g * x₀ ^ 2 / 2) + 3) * |g * x₀| ^ 3 + g ^ 2 * |x₀| / 4

noncomputable def locQ₆ (g x₀ : ℝ) : ℝ :=
  2 * (Real.exp (g * x₀ ^ 2 / 2) + 3) * |g * x₀| ^ 3 + g ^ 2 * |x₀| / 4 + g ^ 2 / 8

noncomputable def locQ₈ (g x₀ : ℝ) : ℝ := 4 * (Real.exp (g * x₀ ^ 2 / 2) + 3) * (g / 2) ^ 3

theorem locQ₄_nonneg (g x₀ : ℝ) : 0 ≤ locQ₄ g x₀ := by unfold locQ₄; positivity

theorem locQ₆_nonneg (g x₀ : ℝ) : 0 ≤ locQ₆ g x₀ := by unfold locQ₆; positivity

theorem locQ₈_nonneg (hg : 0 ≤ g) : 0 ≤ locQ₈ g x₀ := by unfold locQ₈; positivity

/-- `|x²φ − x² − g x₀ x³ − c₂ x⁴| ≤ Q₄x⁴ + Q₆x⁶ + Q₈x⁸`, `c₂ = (g²x₀² − g)/2`: the remainder is
even. -/
theorem locSecond_pointwise (hg : 0 ≤ g) (x : ℝ) :
    |x ^ 2 * locWeight g x₀ x - x ^ 2 - g * x₀ * x ^ 3 - (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 4| ≤
      locQ₄ g x₀ * x ^ 4 + locQ₆ g x₀ * x ^ 6 + locQ₈ g x₀ * x ^ 8 := by
  set y := g * x₀ * x - g / 2 * x ^ 2 with hy
  set E := Real.exp (g * x₀ ^ 2 / 2) + 3 with hE
  have hE0 : 0 ≤ E := by positivity
  have hT : |locWeight g x₀ x - 1 - y - y ^ 2 / 2| ≤ E * |y| ^ 3 := locWeight_taylor2 hg x
  have hy3 : |y| ^ 3 ≤ 4 * (|g * x₀| ^ 3 * |x| ^ 3 + (g / 2) ^ 3 * x ^ 6) :=
    abs_locExponent_cube_le hg x
  have e : x ^ 2 * locWeight g x₀ x - x ^ 2 - g * x₀ * x ^ 3 - (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 4 =
      x ^ 2 * (locWeight g x₀ x - 1 - y - y ^ 2 / 2) +
        (-(g ^ 2 * x₀ / 2) * x ^ 5 + g ^ 2 / 8 * x ^ 6) := by
    rw [hy]; ring
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hx4 : x ^ 4 = |x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx6 : x ^ 6 = |x| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : x ^ 8 = |x| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h5 : |x| ^ 5 ≤ (|x| ^ 4 + |x| ^ 6) / 2 := by nlinarith [sq_nonneg (|x| ^ 2 - |x| ^ 3)]
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hgx : 0 ≤ |g * x₀| ^ 3 := by positivity
  have hg3 : 0 ≤ (g / 2) ^ 3 := by positivity
  have hmain : |x ^ 2 * (locWeight g x₀ x - 1 - y - y ^ 2 / 2) +
        (-(g ^ 2 * x₀ / 2) * x ^ 5 + g ^ 2 / 8 * x ^ 6)|
      ≤ |x| ^ 2 * (E * (4 * (|g * x₀| ^ 3 * |x| ^ 3 + (g / 2) ^ 3 * x ^ 6))) +
        (g ^ 2 * |x₀| / 2 * |x| ^ 5 + g ^ 2 / 8 * |x| ^ 6) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (x ^ 2), abs_pow]
    gcongr
    · exact hT.trans (mul_le_mul_of_nonneg_left hy3 hE0)
    · calc |-(g ^ 2 * x₀ / 2) * x ^ 5 + g ^ 2 / 8 * x ^ 6|
          ≤ |-(g ^ 2 * x₀ / 2) * x ^ 5| + |g ^ 2 / 8 * x ^ 6| := abs_add_le _ _
        _ = g ^ 2 * |x₀| / 2 * |x| ^ 5 + g ^ 2 / 8 * |x| ^ 6 := by
            simp only [abs_mul, abs_neg, abs_div, abs_pow, abs_of_nonneg hg, abs_two,
              abs_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num)]
  rw [e]
  refine hmain.trans ?_
  rw [hx4, hx6, hx8]
  calc _ = 4 * E * |g * x₀| ^ 3 * |x| ^ 5 + 4 * E * (g / 2) ^ 3 * |x| ^ 8 +
        g ^ 2 * |x₀| / 2 * |x| ^ 5 + g ^ 2 / 8 * |x| ^ 6 := by ring
    _ ≤ 4 * E * |g * x₀| ^ 3 * ((|x| ^ 4 + |x| ^ 6) / 2) + 4 * E * (g / 2) ^ 3 * |x| ^ 8 +
        g ^ 2 * |x₀| / 2 * ((|x| ^ 4 + |x| ^ 6) / 2) + g ^ 2 / 8 * |x| ^ 6 := by gcongr
    _ = locQ₄ g x₀ * |x| ^ 4 + locQ₆ g x₀ * |x| ^ 6 + locQ₈ g x₀ * |x| ^ 8 := by
        rw [hE]
        unfold locQ₄ locQ₆ locQ₈
        ring

end Weight

/-! ### The localised variance in one dimension -/

section OneDim

variable {lam alpha gamma g x₀ : ℝ}

/-- The one-dimensional localised potential `ℓ + (g/(2t))(x − x₀)²`, whose Boltzmann factor at
temperature `t` is the localised measure `e^{−tℓ − (g/2)(x − x₀)²}`. -/
noncomputable def locPotential1 (lam alpha gamma g x₀ t : ℝ) : ℝ → ℝ :=
  fun x => anharmonicPotential lam alpha gamma x + g / (2 * t) * (x - x₀) ^ 2

/-- The localised variance `Var_loc = Cov_loc[x, x]`. -/
noncomputable def localisedVar (lam alpha gamma g x₀ t : ℝ) : ℝ :=
  _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t (fun x => x) (fun x => x)

variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- Every localised expectation is a ratio of weighted anharmonic expectations:
`⟨f⟩_loc = ⟨fφ⟩_t/⟨φ⟩_t`. -/
theorem gibbsExpectation_locPotential1 {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t f =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => f x * locWeight g x₀ x) /
        _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (locWeight g x₀) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hc : 0 < Real.exp (-(g * x₀ ^ 2 / 2)) := Real.exp_pos _
  have e : ∀ x, Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x)) =
      Real.exp (-(g * x₀ ^ 2 / 2)) *
        (locWeight g x₀ x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    intro x
    unfold locPotential1 locWeight
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hZ' : (∫ x, Real.exp (-(t * anharmonicPotential lam alpha gamma x))) ≠ 0 := hZ.ne'
  have hnum : ∫ x, f x * Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x)) =
      Real.exp (-(g * x₀ ^ 2 / 2)) * ∫ x, f x * locWeight g x₀ x *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [e x]; ring)
  have hden : ∫ x, Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x)) =
      Real.exp (-(g * x₀ ^ 2 / 2)) * ∫ x, locWeight g x₀ x *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => e x)
  unfold _root_.Laplace.gibbsExpectation _root_.Laplace.partitionFunction
  rw [hnum, hden, mul_div_mul_left _ _ hc.ne', div_div_div_cancel_right₀ hZ']

omit hlam hgamma hdisc in
theorem gibbsExpectation_locPotential1_id {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x) =
      localisedMean lam alpha gamma g x₀ t :=
  gibbsExpectation_localisedAnharmonic_id ht.ne'

/-- `Var_loc = ⟨x²φ⟩/⟨φ⟩ − (⟨xφ⟩/⟨φ⟩)²`. -/
theorem localisedVar_eq {t : ℝ} (ht : 0 < t) :
    localisedVar lam alpha gamma g x₀ t =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2 * locWeight g x₀ x) /
        _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (locWeight g x₀) -
      (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x * locWeight g x₀ x) /
        _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (locWeight g x₀)) ^ 2 := by
  unfold localisedVar _root_.Laplace.gibbsCov
  rw [gibbsExpectation_locPotential1 hlam hgamma hdisc ht,
    gibbsExpectation_locPotential1 hlam hgamma hdisc ht, sq]
  have e : (fun x => (fun x : ℝ => x) x * (fun x : ℝ => x) x * locWeight g x₀ x) =
      fun x => x ^ 2 * locWeight g x₀ x := by
    funext x
    change x * x * locWeight g x₀ x = x ^ 2 * locWeight g x₀ x
    ring
  rw [e]

/-- `|⟨x²φ⟩ − ⟨x²⟩ − g x₀⟨x³⟩ − c₂⟨x⁴⟩| ≤ A₂⟨x⁴⟩ + B₂⟨x⁶⟩ + C₂⟨x⁸⟩`. -/
theorem locSecond_expansion2 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2 * locWeight g x₀ x) -
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2) -
      g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 3) -
      (g ^ 2 * x₀ ^ 2 - g) / 2 *
        _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4)| ≤
      locQ₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locQ₆ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locQ₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 2
  have h2 := integrable_pow_exp' hlam hgamma hdisc ht 2
  have h3 := integrable_pow_exp' hlam hgamma hdisc ht 3
  have h4 := integrable_pow_exp' hlam hgamma hdisc ht 4
  have hF3 : Integrable (fun x => (x ^ 2 * locWeight g x₀ x - x ^ 2 - g * x₀ * x ^ 3) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (hf.sub h2).sub (h3.const_mul (g * x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hF : Integrable (fun x => (x ^ 2 * locWeight g x₀ x - x ^ 2 - g * x₀ * x ^ 3 -
      (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 4) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := hF3.sub (h4.const_mul ((g ^ 2 * x₀ ^ 2 - g) / 2))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locQ₄ g x₀ * x ^ 4 + locQ₆ g x₀ * x ^ 6 + locQ₈ g x₀ * x ^ 8) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((h4.const_mul (locQ₄ g x₀)).add
      ((integrable_pow_exp' hlam hgamma hdisc ht 6).const_mul (locQ₆ g x₀))).add
      ((integrable_pow_exp' hlam hgamma hdisc ht 8).const_mul (locQ₈ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hsplit : (fun x => x ^ 2 * locWeight g x₀ x - x ^ 2 - g * x₀ * x ^ 3 -
      (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 4) =
      fun x => 1 * (x ^ 2 * locWeight g x₀ x - x ^ 2 - g * x₀ * x ^ 3) +
        (-((g ^ 2 * x₀ ^ 2 - g) / 2)) * x ^ 4 := by
    funext x; ring
  rw [← gibbs_sub_sub hf h2 h3, ← gibbs_lin3 h4 (integrable_pow_exp' hlam hgamma hdisc ht 6)
    (integrable_pow_exp' hlam hgamma hdisc ht 8)]
  have e : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2 * locWeight g x₀ x - x ^ 2 - g * x₀ * x ^ 3) -
      (g ^ 2 * x₀ ^ 2 - g) / 2 * _root_.Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2 * locWeight g x₀ x - x ^ 2 - g * x₀ * x ^ 3 -
          (g ^ 2 * x₀ ^ 2 - g) / 2 * x ^ 4) := by
    rw [hsplit, gibbsExpectation_lin hF3 h4]
    ring
  rw [e]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x => locSecond_pointwise hg x)

/-- **The second weighted moment at its rate**: `|t⟨x²φ⟩ − 1/λ| ≤ K/t`. -/
theorem locSecond_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2 * locWeight g x₀ x) - 1 / lam| ≤ K / t := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := Laplace.OneD.evenMoment_anharmonic_rate hlam hgamma hdisc 1
  obtain ⟨M₃, T₃, hM₃, hT₃, h₃⟩ := thirdMoment_bound hlam hgamma hdisc
  obtain ⟨C₄, T₄, hC₄, hT₄, h₄⟩ := evenMoment_bound hlam hgamma hdisc 2
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  simp only [show (2 * 2 : ℕ) = 4 from rfl, show (2 * 3 : ℕ) = 6 from rfl,
    show (2 * 4 : ℕ) = 8 from rfl] at h₄ h₆ h₈
  have hA := locQ₄_nonneg g x₀
  have hB := locQ₆_nonneg g x₀
  have hC := locQ₈_nonneg (x₀ := x₀) hg
  set c₂ := (g ^ 2 * x₀ ^ 2 - g) / 2 with hc₂
  refine ⟨K₂ + |g * x₀| * M₃ + |c₂| * C₄ + (locQ₄ g x₀ * C₄ + locQ₆ g x₀ * C₆ + locQ₈ g x₀ * C₈),
    T₂ + T₃ + T₄ + T₆ + T₈, by positivity, by linarith, fun {t} ht => ?_⟩
  have hT₂t : T₂ ≤ t := by linarith
  have hT₃t : T₃ ≤ t := by linarith
  have hT₄t : T₄ ≤ t := by linarith
  have hT₆t : T₆ ≤ t := by linarith
  have hT₈t : T₈ ≤ t := by linarith
  have ht1 : 1 ≤ t := hT₂.trans hT₂t
  have ht0 : 0 < t := by linarith
  have e₂ : |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 2) - 1 / lam| ≤ K₂ / t := by
    simpa [Nat.doubleFactorial] using h₂ hT₂t
  have e₃ := h₃ hT₃t
  have e₄ := h₄ hT₄t
  have hM4 : 0 ≤ _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 4) :=
    gibbsExpectation_nonneg' (partition_pos' hlam hgamma hdisc ht0) fun x => by positivity
  have hR := (locSecond_expansion2 hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left e₄ hA)
      (mul_le_mul_of_nonneg_left (h₆ hT₆t) hB)) (mul_le_mul_of_nonneg_left (h₈ hT₈t) hC))
  set N₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2 * locWeight g x₀ x) with hN₂
  set M₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2) with hM₂
  set M₃' := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3) with hM₃'
  set M₄ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4) with hM₄
  have key : t * N₂ - 1 / lam =
      ((t * M₂ - 1 / lam) + g * x₀ * (t * M₃') + c₂ * (t * M₄)) +
        t * (N₂ - M₂ - g * x₀ * M₃' - c₂ * M₄) := by ring
  have htt : t ≤ t ^ 2 := by nlinarith
  have htt3 : t ≤ t ^ 3 := by nlinarith
  have hRt : t * (locQ₄ g x₀ * (C₄ / t ^ 2) + locQ₆ g x₀ * (C₆ / t ^ 3) +
      locQ₈ g x₀ * (C₈ / t ^ 4)) ≤
      (locQ₄ g x₀ * C₄ + locQ₆ g x₀ * C₆ + locQ₈ g x₀ * C₈) / t := by
    have e : t * (locQ₄ g x₀ * (C₄ / t ^ 2) + locQ₆ g x₀ * (C₆ / t ^ 3) +
        locQ₈ g x₀ * (C₈ / t ^ 4)) =
        locQ₄ g x₀ * C₄ / t + locQ₆ g x₀ * C₆ / t ^ 2 + locQ₈ g x₀ * C₈ / t ^ 3 := by
      field_simp
    have h6 : locQ₆ g x₀ * C₆ / t ^ 2 ≤ locQ₆ g x₀ * C₆ / t :=
      div_le_div_of_nonneg_left (by positivity) ht0 htt
    have h8 : locQ₈ g x₀ * C₈ / t ^ 3 ≤ locQ₈ g x₀ * C₈ / t :=
      div_le_div_of_nonneg_left (by positivity) ht0 htt3
    rw [e, add_div, add_div]
    linarith
  have h4t : t * M₄ ≤ C₄ / t := by
    have : t * M₄ ≤ t * (C₄ / t ^ 2) := mul_le_mul_of_nonneg_left e₄ ht0.le
    calc t * M₄ ≤ t * (C₄ / t ^ 2) := this
      _ = C₄ / t := by field_simp
  have h4abs : |t * M₄| ≤ C₄ / t := by
    rw [abs_of_nonneg (mul_nonneg ht0.le hM4)]; exact h4t
  rw [key]
  calc |(t * M₂ - 1 / lam) + g * x₀ * (t * M₃') + c₂ * (t * M₄) +
        t * (N₂ - M₂ - g * x₀ * M₃' - c₂ * M₄)|
      ≤ |(t * M₂ - 1 / lam) + g * x₀ * (t * M₃') + c₂ * (t * M₄)| +
          |t * (N₂ - M₂ - g * x₀ * M₃' - c₂ * M₄)| := abs_add_le _ _
    _ ≤ |t * M₂ - 1 / lam| + |g * x₀ * (t * M₃')| + |c₂ * (t * M₄)| +
          |t * (N₂ - M₂ - g * x₀ * M₃' - c₂ * M₄)| := add_le_add (abs_add_three _ _ _) le_rfl
    _ = |t * M₂ - 1 / lam| + |g * x₀| * |t * M₃'| + |c₂| * |t * M₄| +
          t * |N₂ - M₂ - g * x₀ * M₃' - c₂ * M₄| := by
        rw [abs_mul (g * x₀), abs_mul c₂, abs_mul t (N₂ - M₂ - g * x₀ * M₃' - c₂ * M₄),
          abs_of_pos ht0]
    _ ≤ K₂ / t + |g * x₀| * (M₃ / t) + |c₂| * (C₄ / t) +
          t * (locQ₄ g x₀ * (C₄ / t ^ 2) + locQ₆ g x₀ * (C₆ / t ^ 3) +
            locQ₈ g x₀ * (C₈ / t ^ 4)) := by gcongr
    _ ≤ K₂ / t + |g * x₀| * (M₃ / t) + |c₂| * (C₄ / t) +
          (locQ₄ g x₀ * C₄ + locQ₆ g x₀ * C₆ + locQ₈ g x₀ * C₈) / t := by gcongr
    _ = (K₂ + |g * x₀| * M₃ + |c₂| * C₄ +
          (locQ₄ g x₀ * C₄ + locQ₆ g x₀ * C₆ + locQ₈ g x₀ * C₈)) / t := by ring

/-- **The localised variance at leading order with rate**: `|t·Var_loc − 1/λ| ≤ K/t`. -/
theorem localisedVar_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * localisedVar lam alpha gamma g x₀ t - 1 / lam| ≤ K / t := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locSecond_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := locNumerator_rate_sharp hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate hlam hgamma hdisc hg (x₀ := x₀)
  set c := -alpha / (2 * lam ^ 2) + g * x₀ / lam with hc
  have hlam' : 0 < 1 / lam := by positivity
  refine ⟨2 * K₂ + 2 * (1 / lam) * KD + 4 * (|c| + K₁) ^ 2, T₂ + T₁ + TD + 2 * KD,
    by positivity, by linarith, fun {t} ht => ?_⟩
  have hT₂t : T₂ ≤ t := by linarith
  have hT₁t : T₁ ≤ t := by linarith
  have hTDt : TD ≤ t := by linarith
  have h2K : 2 * KD ≤ t := by linarith
  have ht1 : 1 ≤ t := hT₂.trans hT₂t
  have ht0 : 0 < t := by linarith
  rw [localisedVar_eq hlam hgamma hdisc ht0]
  have e₂ := h₂ hT₂t
  have e₁ := h₁ hT₁t
  have eD := hD hTDt
  set N₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2 * locWeight g x₀ x) with hN₂
  set N₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x * locWeight g x₀ x) with hN₁
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
  have hDhalf : 1 / 2 ≤ D := by
    have h1 : KD / t ≤ 1 / 2 := by rw [div_le_iff₀ ht0]; linarith
    have h2 := (abs_le.mp (eD.trans h1)).1
    linarith
  have hD0 : 0 < D := by linarith
  have hDne : D ≠ 0 := hD0.ne'
  have hN₁b : |t * N₁| ≤ |c| + K₁ := Laplace.OneD.rate_bounded ht1 hK₁ e₁
  have hA : |t * (N₂ / D) - 1 / lam| ≤ (2 * K₂ + 2 * (1 / lam) * KD) / t := by
    have key : t * (N₂ / D) - 1 / lam = ((t * N₂ - 1 / lam) + 1 / lam * (1 - D)) / D := by
      field_simp
      ring
    rw [key, abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
    calc |(t * N₂ - 1 / lam) + 1 / lam * (1 - D)|
        ≤ |t * N₂ - 1 / lam| + |1 / lam * (1 - D)| := abs_add_le _ _
      _ = |t * N₂ - 1 / lam| + 1 / lam * |1 - D| := by rw [abs_mul, abs_of_pos hlam']
      _ ≤ K₂ / t + 1 / lam * (KD / t) := by rw [abs_sub_comm 1 D]; gcongr
      _ = (2 * K₂ + 2 * (1 / lam) * KD) / t * (1 / 2) := by ring
      _ ≤ (2 * K₂ + 2 * (1 / lam) * KD) / t * D := by gcongr
  have hB : t * (N₁ / D) ^ 2 ≤ 4 * (|c| + K₁) ^ 2 / t := by
    have e : t * (N₁ / D) ^ 2 = (t * N₁) ^ 2 / (t * D ^ 2) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) ht0]
    have h1 : (t * N₁) ^ 2 ≤ (|c| + K₁) ^ 2 := by
      rw [← sq_abs (t * N₁)]
      gcongr
    have h2 : 1 ≤ 4 * D ^ 2 := by nlinarith
    calc (t * N₁) ^ 2 * t ≤ (|c| + K₁) ^ 2 * t := mul_le_mul_of_nonneg_right h1 ht0.le
      _ = (|c| + K₁) ^ 2 * t * 1 := (mul_one _).symm
      _ ≤ (|c| + K₁) ^ 2 * t * (4 * D ^ 2) := by gcongr
      _ = 4 * (|c| + K₁) ^ 2 * (t * D ^ 2) := by ring
  have hsq : 0 ≤ t * (N₁ / D) ^ 2 := by positivity
  calc |t * (N₂ / D - (N₁ / D) ^ 2) - 1 / lam|
      = |(t * (N₂ / D) - 1 / lam) - t * (N₁ / D) ^ 2| := by ring_nf
    _ ≤ |t * (N₂ / D) - 1 / lam| + |t * (N₁ / D) ^ 2| := abs_sub _ _
    _ ≤ (2 * K₂ + 2 * (1 / lam) * KD) / t + 4 * (|c| + K₁) ^ 2 / t := by
        rw [abs_of_nonneg hsq]; exact add_le_add hA hB
    _ = (2 * K₂ + 2 * (1 / lam) * KD + 4 * (|c| + K₁) ^ 2) / t := by ring

/-- **eq:cov's `O(S²)` remainder in one dimension**: `|Var_loc − 1/(tλ + g)| ≤ K/t²`. -/
theorem localisedVar_sub_displayed_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |localisedVar lam alpha gamma g x₀ t - 1 / (t * lam + g)| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedVar_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K + g / lam ^ 2, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  set V := localisedVar lam alpha gamma g x₀ t with hV
  have h1 : |V - 1 / (lam * t)| ≤ K / t ^ 2 := by
    have e : V - 1 / (lam * t) = (t * V - 1 / lam) / t := by field_simp
    rw [e, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    calc |t * V - 1 / lam| ≤ K / t := h ht
      _ = K / t ^ 2 * t := by field_simp
  have h2 : |1 / (lam * t) - 1 / (t * lam + g)| ≤ g / lam ^ 2 / t ^ 2 := by
    have hd : 0 < t * lam + g := by positivity
    have e : 1 / (lam * t) - 1 / (t * lam + g) = g / (lam * t * (t * lam + g)) := by
      field_simp
      ring
    rw [e, abs_of_nonneg (by positivity), div_div]
    apply div_le_div_of_nonneg_left hg (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hg hlam.le) ht0.le]
  calc |V - 1 / (t * lam + g)|
      ≤ |V - 1 / (lam * t)| + |1 / (lam * t) - 1 / (t * lam + g)| := abs_sub_le _ _ _
    _ ≤ K / t ^ 2 + g / lam ^ 2 / t ^ 2 := add_le_add h1 h2
    _ = (K + g / lam ^ 2) / t ^ 2 := by ring

end OneDim

/-! ### `d` dimensions: E2's oscillator with the isotropic localiser -/

theorem sum_rate_div {κ : Type*} [Fintype κ] (a : κ → ℝ) (e : κ → ℝ → ℝ)
    (h : ∀ i, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |e i t| ≤ K / t) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |∑ i, a i * e i t| ≤ K / t := by
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
    _ ≤ ∑ i, |a i| * (K i / t) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i (hTi i)) (abs_nonneg _)
    _ = (∑ i, |a i| * K i) / t := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring

section E2

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- **Frame covariances of the localised measure vanish off the diagonal**:
`Cov_loc[(Aw)ᵢ, (Aw)ᵢ'] = if i = i' then Var_loc,i else 0`. -/
theorem localisedRotatedAnharmonic_cov_frame (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t)
    (i i' : Fin d) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w i') =
      if i = i' then localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t
      else 0 := by
  have hcont := continuous_localisedPotential (continuous_separableAnharmonic lam alpha gamma) g
    (affineFrame Q c w₀) t
  rw [separableAnharmonic, localisedPotential_separable] at hcont
  have h : gibbsCov (rotated Q c (separablePotential fun i x =>
        anharmonicPotential (lam i) (alpha i) (gamma i) x +
          g / (2 * t) * (x - affineFrame Q c w₀ i) ^ 2)) t
        (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w i') =
      gibbsCov (separablePotential fun i x =>
        anharmonicPotential (lam i) (alpha i) (gamma i) x +
          g / (2 * t) * (x - affineFrame Q c w₀ i) ^ 2) t (fun u => u i) (fun u => u i') :=
    gibbsCov_rotated_of_continuous hQ c hcont (continuous_apply i) (continuous_apply i') t
  rw [localisedRotatedAnharmonic_eq_rotated hQ, h,
    gibbsCov_coord_separable _ t (fun k => (partitionFunction_localisedAnharmonic_pos
      (hlam k) (hgamma k) (hdisc k) hg ht).ne') i i']
  rfl

/-- **The ambient localised covariance**: `Cov_loc[wⱼ, wₖ] = ∑ᵢ QⱼᵢQₖᵢ Var_loc,i`. -/
theorem localisedRotatedAnharmonic_cov_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t)
    (j k : Fin d) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
        (fun w => w k) =
      ∑ i, Q j i * Q k i * localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t := by
  set L := localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t with hLdef
  have hZ := (partitionFunction_localisedRotatedAnharmonic_pos hQ c w₀ hlam hgamma hdisc hg ht).ne'
  have hL := integrable_exp_localisedRotatedAnharmonic hQ c w₀ hlam hgamma hdisc hg ht
  have hA := integrable_frame_coord_localised hQ c w₀ hlam hgamma hdisc hg ht
  have hAA : ∀ i i', Integrable (fun w => affineFrame Q c w i * affineFrame Q c w i' *
      Real.exp (-(t * L w))) := by
    intro i i'
    have hL' : Continuous (localisedPotential (rotatedAnharmonic Q c lam alpha gamma) g w₀ t) :=
      continuous_localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t
    have hA' : Continuous fun w : Fin d → ℝ => affineFrame Q c w i := by
      unfold affineFrame; fun_prop
    have hA'' : Continuous fun w : Fin d → ℝ => affineFrame Q c w i' := by
      unfold affineFrame; fun_prop
    exact integrable_localised_of_integrable (L := rotatedAnharmonic Q c lam alpha gamma)
      (φ := fun w => affineFrame Q c w i * affineFrame Q c w i') hg w₀ ht
      (Continuous.aestronglyMeasurable (by fun_prop))
      (integrable_coord_mul_rotatedAnharmonic hQ c hlam hgamma hdisc ht i i')
  have hQA : ∀ j i, Integrable (fun w => Q j i * affineFrame Q c w i *
      Real.exp (-(t * L w))) := fun j i =>
    ((hA i).const_mul (Q j i)).congr (Eventually.of_forall fun w => by ring)
  have hF : ∀ j, Integrable (fun w => (∑ i, Q j i * affineFrame Q c w i) *
      Real.exp (-(t * L w))) := fun j =>
    (integrable_finsetSum Finset.univ fun i _ => hQA j i).congr (Eventually.of_forall fun w => by
      simp only [Finset.sum_mul])
  have hterm : ∀ j k i i', Integrable (fun w => Q j i * affineFrame Q c w i *
      (Q k i' * affineFrame Q c w i') * Real.exp (-(t * L w))) := fun j k i i' =>
    ((hAA i i').const_mul (Q j i * Q k i')).congr (Eventually.of_forall fun w => by ring)
  have hFF : ∀ j k, Integrable (fun w => (∑ i, Q j i * affineFrame Q c w i) *
      (∑ i, Q k i * affineFrame Q c w i) * Real.exp (-(t * L w))) := fun j k =>
    (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun i' _ =>
      hterm j k i i').congr (Eventually.of_forall fun w => by
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm)
  have hfun : ∀ j, (fun w : Fin d → ℝ => w j) =
      fun w => c j + ∑ i, Q j i * affineFrame Q c w i := fun j => by
    funext w
    exact coord_eq_sum_affineFrame hQ c w j
  rw [hfun j, hfun k, gibbsCov_const_add_both L t (c j) (c k) _ _ hZ hL (hF j) (hF k) (hFF j k),
    gibbsCov_linear_combination L t (fun i w => affineFrame Q c w i) (Q j) (Q k) hA hAA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun i' _ hi' => ?_) (fun h => absurd (Finset.mem_univ i) h)]
  · rw [localisedRotatedAnharmonic_cov_frame hQ c w₀ hlam hgamma hdisc hg ht i i, if_pos rfl]
  · rw [localisedRotatedAnharmonic_cov_frame hQ c w₀ hlam hgamma hdisc hg ht i i',
      if_neg (Ne.symm hi'), mul_zero]

/-- The displayed resolvent entrywise: `((tH + gI)⁻¹)ⱼₖ = ∑ᵢ QⱼᵢQₖᵢ/(tλᵢ + g)`. -/
theorem locS_rot_apply (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (j k : Fin d) :
    locS g (Q * diagonal lam * Qᵀ) t j k = ∑ i, Q j i * Q k i * (1 / (t * lam i + g)) := by
  rw [locS_rot hQ hlam hg ht, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `(Q diag(1/λ) Qᵀ)ⱼₖ = ∑ᵢ QⱼᵢQₖᵢ/λᵢ` (the leading covariance `H⁻¹`). -/
theorem conj_diagonal_inv_apply (Q : Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (j k : Fin d) :
    (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k = ∑ i, Q j i * Q k i * (1 / lam i) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **eq:cov with its `O(S²)` remainder on E2's exact localised measure**: for all ambient `j, k`,
`|Cov_loc[wⱼ, wₖ] − ((tH + gI)⁻¹)ⱼₖ| ≤ K/t²`. -/
theorem localisedRotatedAnharmonic_cov_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (j k : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
          (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sq (fun i => Q j i * Q k i)
    (fun i t => localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      1 / (t * lam i + g))
    (fun i => localisedVar_sub_displayed_rate (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
        (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k =
      ∑ i, Q j i * Q k i * (localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
        1 / (t * lam i + g)) := by
    rw [localisedRotatedAnharmonic_cov_coord hQ c w₀ hlam hgamma hdisc hg ht0 j k,
      locS_rot_apply hQ hlam hg ht0 j k, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  exact h ht

/-- **The localised covariance at leading order**: `|t·Cov_loc[wⱼ, wₖ] − (H⁻¹)ⱼₖ| ≤ K/t` with
`H⁻¹ = Q diag(1/λ) Qᵀ`. -/
theorem localisedRotatedAnharmonic_cov_rate_leading (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) (j k : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
          (fun w => w k) - (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div (fun i => Q j i * Q k i)
    (fun i t => t * localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      1 / lam i)
    (fun i => localisedVar_rate (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : t * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => w j) (fun w => w k) - (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k =
      ∑ i, Q j i * Q k i * (t * localisedVar (lam i) (alpha i) (gamma i) g
        (affineFrame Q c w₀ i) t - 1 / lam i) := by
    rw [localisedRotatedAnharmonic_cov_coord hQ c w₀ hlam hgamma hdisc hg ht0 j k,
      conj_diagonal_inv_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  exact h ht

end E2

end Laplace.Multi
