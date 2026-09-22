/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedAnharmonicCov

/-!
# E3's localised LLC on the exact anharmonic localised measure

E3 localises the posterior with `(γ/2)|w − w₀|²` and predicts the localised LLC
`λ̂_loc = ½ tr(tH(tH + γI)⁻¹) = ½∑ᵢ tλᵢ/(tλᵢ + γ)` from the Gaussian approximation. On the exact
localised anharmonic measure (localiser strength `g`, anchor `w₀`) with the *unlocalised* energy as
the observable:

* `localisedEnergy_rate` (1D): `|t⟨ℓ⟩_loc − ½·tλ/(tλ + g)| ≤ K/t`, from the localised raw second
  moment (`locSecondMoment_rate`, `t⟨x²⟩_loc = t·Var_loc + (t⟨x⟩_loc)²/t`), the localised third
  moment (`locThirdMoment_loc_rate`, via the even remainder of `x³φ`) and the localised fourth
  moment (`locFourthMoment_loc_le`, via `φ ≤ e^{g x₀²/2}`);
* `localisedRotatedAnharmonic_llc_rate` (E2's rotated oscillator, isotropic localiser):
  `|t⟨L∘A⟩_loc − ½ tr(tH(tH + gI)⁻¹)| ≤ K/t`, by separability
  (`localisedRotatedAnharmonic_energy_coord`: `⟨L∘A⟩_loc = ∑ᵢ⟨ℓᵢ⟩_loc,i`) and the trace identity
  `trace_smul_locS_rot`;
* the prediction's algebra, `½ tr(tH(tH + gI)⁻¹) = d/2 − ½∑ᵢ g/(tλᵢ + g) ≤ d/2`
  (`trace_smul_locS_rot_eq`, `trace_smul_locS_rot_le`), and the corollary
  `localisedRotatedAnharmonic_llc_leading`: `|t⟨L∘A⟩_loc − d/2| ≤ K/t`.

This certifies E3's trace prediction on a non-Gaussian target up to an absolute `O(1/t)` error; it
does not identify the `1/t` coefficient of the exact energy (whose sign the trace prediction alone
does not determine).
-/

open Real MeasureTheory Filter Topology Matrix

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

/-! ### The cubic weight `x³φ` -/

section Weight

variable {g x₀ : ℝ}

/-- The constants of `locCubic_pointwise`. -/
noncomputable def locR₄ (g x₀ : ℝ) : ℝ := locC₁ g x₀ / 2

noncomputable def locR₆ (g x₀ : ℝ) : ℝ := locC₁ g x₀ / 2 + locC₂ g x₀ / 2

noncomputable def locR₈ (g x₀ : ℝ) : ℝ := locC₂ g x₀ / 2

theorem locR₄_nonneg (hg : 0 ≤ g) : 0 ≤ locR₄ g x₀ := by
  unfold locR₄; have := locC₁_nonneg (x₀ := x₀) hg; positivity

theorem locR₆_nonneg (hg : 0 ≤ g) : 0 ≤ locR₆ g x₀ := by
  unfold locR₆; have := locC₁_nonneg (x₀ := x₀) hg; have := locC₂_nonneg g x₀; positivity

theorem locR₈_nonneg (g x₀ : ℝ) : 0 ≤ locR₈ g x₀ := by
  unfold locR₈; have := locC₂_nonneg g x₀; positivity

/-- `|x³φ − x³ − g x₀ x⁴| ≤ R₄x⁴ + R₆x⁶ + R₈x⁸`: the remainder of the cubic weight is even. -/
theorem locCubic_pointwise (hg : 0 ≤ g) (x : ℝ) :
    |x ^ 3 * locWeight g x₀ x - x ^ 3 - g * x₀ * x ^ 4| ≤
      locR₄ g x₀ * x ^ 4 + locR₆ g x₀ * x ^ 6 + locR₈ g x₀ * x ^ 8 := by
  have hT := locWeight_expansion' (x₀ := x₀) hg x
  have hC₁ := locC₁_nonneg (x₀ := x₀) hg
  have hC₂ := locC₂_nonneg g x₀
  have e : x ^ 3 * locWeight g x₀ x - x ^ 3 - g * x₀ * x ^ 4 =
      x ^ 3 * (locWeight g x₀ x - 1 - g * x₀ * x) := by ring
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hx4 : x ^ 4 = |x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx6 : x ^ 6 = |x| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : x ^ 8 = |x| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h5 : |x| ^ 5 ≤ (|x| ^ 4 + |x| ^ 6) / 2 := by nlinarith [sq_nonneg (|x| ^ 2 - |x| ^ 3)]
  have h7 : |x| ^ 7 ≤ (|x| ^ 6 + |x| ^ 8) / 2 := by nlinarith [sq_nonneg (|x| ^ 3 - |x| ^ 4)]
  have hmain : |x ^ 3 * (locWeight g x₀ x - 1 - g * x₀ * x)|
      ≤ |x| ^ 3 * (locC₁ g x₀ * x ^ 2 + locC₂ g x₀ * x ^ 4) := by
    rw [abs_mul (x ^ 3), abs_pow]
    gcongr
  rw [e]
  refine hmain.trans ?_
  rw [hx2, hx4, hx6, hx8]
  calc _ = locC₁ g x₀ * |x| ^ 5 + locC₂ g x₀ * |x| ^ 7 := by ring
    _ ≤ locC₁ g x₀ * ((|x| ^ 4 + |x| ^ 6) / 2) + locC₂ g x₀ * ((|x| ^ 6 + |x| ^ 8) / 2) := by
        gcongr
    _ = locR₄ g x₀ * |x| ^ 4 + locR₆ g x₀ * |x| ^ 6 + locR₈ g x₀ * |x| ^ 8 := by
        unfold locR₄ locR₆ locR₈
        ring

end Weight

/-! ### One dimension: the localised moments and energy -/

section OneDim

variable {lam alpha gamma g x₀ : ℝ}

theorem gibbsExpectation_const_mul₁ {L : ℝ → ℝ} {t c : ℝ} (f : ℝ → ℝ) :
    _root_.Laplace.gibbsExpectation L t (fun x => c * f x) =
      c * _root_.Laplace.gibbsExpectation L t f := by
  unfold _root_.Laplace.gibbsExpectation
  simp only [mul_assoc]
  rw [integral_const_mul, mul_div_assoc]

theorem exp_neg_locPotential1 {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x)) =
      Real.exp (-(g * x₀ ^ 2 / 2)) *
        (locWeight g x₀ x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  unfold locPotential1 locWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

theorem integrable_pow_locPotential1 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m * Real.exp (-(t * locPotential1 lam alpha gamma g x₀ t x))) := by
  have h := (integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) m).const_mul
    (Real.exp (-(g * x₀ ^ 2 / 2)))
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [exp_neg_locPotential1 (lam := lam) (alpha := alpha) (gamma := gamma) ht.ne' x]
  ring

theorem partitionFunction_locPotential1_pos (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    0 < _root_.Laplace.partitionFunction (locPotential1 lam alpha gamma g x₀ t) t :=
  partitionFunction_localisedAnharmonic_pos hlam hgamma hdisc hg ht

omit hlam hgamma hdisc in
/-- `⟨x²⟩_loc = Var_loc + ⟨x⟩_loc²`. -/
theorem locSecondMoment_eq {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2) =
      localisedVar lam alpha gamma g x₀ t + localisedMean lam alpha gamma g x₀ t ^ 2 := by
  unfold localisedVar _root_.Laplace.gibbsCov
  rw [gibbsExpectation_locPotential1_id ht]
  have e : (fun x => (fun x : ℝ => x) x * (fun x : ℝ => x) x) = fun x : ℝ => x ^ 2 := by
    funext x
    change x * x = x ^ 2
    ring
  rw [e]
  ring

/-- The localised raw second moment: `|t⟨x²⟩_loc − t/(tλ + g)| ≤ K/t`. -/
theorem locSecondMoment_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 2) - t / (t * lam + g)| ≤ K / t := by
  obtain ⟨KV, TV, hKV, hTV, hV⟩ := localisedVar_sub_displayed_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨Km, Tm, hKm, hTm, hm⟩ := localisedMean_anharmonic_rate_sharp hlam hgamma hdisc hg
    (x₀ := x₀)
  set c := -alpha / (2 * lam ^ 2) + g * x₀ / lam with hc
  refine ⟨KV + (|c| + Km) ^ 2, TV + Tm, by positivity, by linarith, fun {t} ht => ?_⟩
  have hTVt : TV ≤ t := by linarith
  have hTmt : Tm ≤ t := by linarith
  have ht1 : 1 ≤ t := hTV.trans hTVt
  have ht0 : 0 < t := by linarith
  rw [locSecondMoment_eq ht0]
  have hV' := hV hTVt
  have hm' : |t * localisedMean lam alpha gamma g x₀ t| ≤ |c| + Km :=
    Laplace.OneD.rate_bounded ht1 hKm (hm hTmt)
  set V := localisedVar lam alpha gamma g x₀ t with hVdef
  set m := localisedMean lam alpha gamma g x₀ t with hmdef
  have hm2 : (t * m) ^ 2 ≤ (|c| + Km) ^ 2 := by
    rw [← sq_abs (t * m)]
    gcongr
  have e : t * (V + m ^ 2) - t / (t * lam + g) = t * (V - 1 / (t * lam + g)) + (t * m) ^ 2 / t := by
    field_simp
    ring
  rw [e]
  calc |t * (V - 1 / (t * lam + g)) + (t * m) ^ 2 / t|
      ≤ |t * (V - 1 / (t * lam + g))| + |(t * m) ^ 2 / t| := abs_add_le _ _
    _ = t * |V - 1 / (t * lam + g)| + (t * m) ^ 2 / t := by
        rw [abs_mul, abs_of_pos ht0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t * m) ^ 2 / t)]
    _ ≤ t * (KV / t ^ 2) + (|c| + Km) ^ 2 / t := by gcongr
    _ = (KV + (|c| + Km) ^ 2) / t := by
        field_simp

/-- `|⟨x³φ⟩ − ⟨x³⟩ − g x₀⟨x⁴⟩| ≤ R₄⟨x⁴⟩ + R₆⟨x⁶⟩ + R₈⟨x⁸⟩`. -/
theorem locCubic_expansion (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 3 * locWeight g x₀ x) -
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3) -
      g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 4)| ≤
      locR₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locR₆ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locR₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 3
  have h3 := integrable_pow_exp' hlam hgamma hdisc ht 3
  have h4 := integrable_pow_exp' hlam hgamma hdisc ht 4
  have hF : Integrable (fun x => (x ^ 3 * locWeight g x₀ x - x ^ 3 - g * x₀ * x ^ 4) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (hf.sub h3).sub (h4.const_mul (g * x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locR₄ g x₀ * x ^ 4 + locR₆ g x₀ * x ^ 6 + locR₈ g x₀ * x ^ 8) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((h4.const_mul (locR₄ g x₀)).add
      ((integrable_pow_exp' hlam hgamma hdisc ht 6).const_mul (locR₆ g x₀))).add
      ((integrable_pow_exp' hlam hgamma hdisc ht 8).const_mul (locR₈ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← gibbs_sub_sub hf h3 h4, ← gibbs_lin3 h4 (integrable_pow_exp' hlam hgamma hdisc ht 6)
    (integrable_pow_exp' hlam hgamma hdisc ht 8)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x => locCubic_pointwise hg x)

/-- `|t⟨x³φ⟩| ≤ K/t` eventually. -/
theorem locCubic_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 3 * locWeight g x₀ x)| ≤ K / t := by
  obtain ⟨M₃, T₃, hM₃, hT₃, h₃⟩ := thirdMoment_bound hlam hgamma hdisc
  obtain ⟨C₄, T₄, hC₄, hT₄, h₄⟩ := evenMoment_bound hlam hgamma hdisc 2
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  simp only [show (2 * 2 : ℕ) = 4 from rfl, show (2 * 3 : ℕ) = 6 from rfl,
    show (2 * 4 : ℕ) = 8 from rfl] at h₄ h₆ h₈
  have hR₄ := locR₄_nonneg (x₀ := x₀) hg
  have hR₆ := locR₆_nonneg (x₀ := x₀) hg
  have hR₈ := locR₈_nonneg g x₀
  refine ⟨M₃ + |g * x₀| * C₄ + (locR₄ g x₀ * C₄ + locR₆ g x₀ * C₆ + locR₈ g x₀ * C₈),
    T₃ + T₄ + T₆ + T₈, by positivity, by linarith, fun {t} ht => ?_⟩
  have hT₃t : T₃ ≤ t := by linarith
  have hT₄t : T₄ ≤ t := by linarith
  have hT₆t : T₆ ≤ t := by linarith
  have hT₈t : T₈ ≤ t := by linarith
  have ht1 : 1 ≤ t := hT₃.trans hT₃t
  have ht0 : 0 < t := by linarith
  have e₃ := h₃ hT₃t
  have e₄ := h₄ hT₄t
  have hM4 : 0 ≤ _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 4) :=
    gibbsExpectation_nonneg' (partition_pos' hlam hgamma hdisc ht0) fun x => by positivity
  have hR := (locCubic_expansion hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left e₄ hR₄)
      (mul_le_mul_of_nonneg_left (h₆ hT₆t) hR₆)) (mul_le_mul_of_nonneg_left (h₈ hT₈t) hR₈))
  set N₃ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3 * locWeight g x₀ x) with hN₃
  set M₃' := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3) with hM₃'
  set M₄ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4) with hM₄
  have key : t * N₃ = t * M₃' + g * x₀ * (t * M₄) + t * (N₃ - M₃' - g * x₀ * M₄) := by ring
  have htt : t ≤ t ^ 2 := by nlinarith
  have htt3 : t ≤ t ^ 3 := by nlinarith
  have hRt : t * (locR₄ g x₀ * (C₄ / t ^ 2) + locR₆ g x₀ * (C₆ / t ^ 3) +
      locR₈ g x₀ * (C₈ / t ^ 4)) ≤
      (locR₄ g x₀ * C₄ + locR₆ g x₀ * C₆ + locR₈ g x₀ * C₈) / t := by
    have e : t * (locR₄ g x₀ * (C₄ / t ^ 2) + locR₆ g x₀ * (C₆ / t ^ 3) +
        locR₈ g x₀ * (C₈ / t ^ 4)) =
        locR₄ g x₀ * C₄ / t + locR₆ g x₀ * C₆ / t ^ 2 + locR₈ g x₀ * C₈ / t ^ 3 := by
      field_simp
    have h6 : locR₆ g x₀ * C₆ / t ^ 2 ≤ locR₆ g x₀ * C₆ / t :=
      div_le_div_of_nonneg_left (by positivity) ht0 htt
    have h8 : locR₈ g x₀ * C₈ / t ^ 3 ≤ locR₈ g x₀ * C₈ / t :=
      div_le_div_of_nonneg_left (by positivity) ht0 htt3
    rw [e, add_div, add_div]
    linarith
  have h4abs : |t * M₄| ≤ C₄ / t := by
    rw [abs_of_nonneg (mul_nonneg ht0.le hM4)]
    calc t * M₄ ≤ t * (C₄ / t ^ 2) := mul_le_mul_of_nonneg_left e₄ ht0.le
      _ = C₄ / t := by field_simp
  rw [key]
  calc |t * M₃' + g * x₀ * (t * M₄) + t * (N₃ - M₃' - g * x₀ * M₄)|
      ≤ |t * M₃'| + |g * x₀ * (t * M₄)| + |t * (N₃ - M₃' - g * x₀ * M₄)| := abs_add_three _ _ _
    _ = |t * M₃'| + |g * x₀| * |t * M₄| + t * |N₃ - M₃' - g * x₀ * M₄| := by
        rw [abs_mul (g * x₀), abs_mul t (N₃ - M₃' - g * x₀ * M₄), abs_of_pos ht0]
    _ ≤ M₃ / t + |g * x₀| * (C₄ / t) + t * (locR₄ g x₀ * (C₄ / t ^ 2) +
          locR₆ g x₀ * (C₆ / t ^ 3) + locR₈ g x₀ * (C₈ / t ^ 4)) := by gcongr
    _ ≤ M₃ / t + |g * x₀| * (C₄ / t) +
          (locR₄ g x₀ * C₄ + locR₆ g x₀ * C₆ + locR₈ g x₀ * C₈) / t := by gcongr
    _ = (M₃ + |g * x₀| * C₄ + (locR₄ g x₀ * C₄ + locR₆ g x₀ * C₆ + locR₈ g x₀ * C₈)) / t := by
        ring

/-- The localised third moment: `|t⟨x³⟩_loc| ≤ K/t`. -/
theorem locThirdMoment_loc_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 3)| ≤ K / t := by
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locCubic_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨2 * K₃, T₃ + TD + 2 * KD, by positivity, by linarith, fun {t} ht => ?_⟩
  have hT₃t : T₃ ≤ t := by linarith
  have hTDt : TD ≤ t := by linarith
  have h2K : 2 * KD ≤ t := by linarith
  have ht1 : 1 ≤ t := hT₃.trans hT₃t
  have ht0 : 0 < t := by linarith
  rw [gibbsExpectation_locPotential1 hlam hgamma hdisc ht0]
  have e₃ := h₃ hT₃t
  have eD := hD hTDt
  set N₃ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3 * locWeight g x₀ x) with hN₃
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
  have hDhalf : 1 / 2 ≤ D := by
    have h1 : KD / t ≤ 1 / 2 := by rw [div_le_iff₀ ht0]; linarith
    have h2 := (abs_le.mp (eD.trans h1)).1
    linarith
  have hD0 : 0 < D := by linarith
  rw [show t * (N₃ / D) = (t * N₃) / D by ring, abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  calc |t * N₃| ≤ K₃ / t := e₃
    _ = 2 * K₃ / t * (1 / 2) := by ring
    _ ≤ 2 * K₃ / t * D := by gcongr

/-- The localised fourth moment: `0 ≤ t⟨x⁴⟩_loc ≤ K/t`. -/
theorem locFourthMoment_loc_le (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      0 ≤ t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 4) ∧
        t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 4) ≤ K / t := by
  obtain ⟨C₄, T₄, hC₄, hT₄, h₄⟩ := evenMoment_bound hlam hgamma hdisc 2
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate hlam hgamma hdisc hg (x₀ := x₀)
  simp only [show (2 * 2 : ℕ) = 4 from rfl] at h₄
  refine ⟨2 * Real.exp (g * x₀ ^ 2 / 2) * C₄, T₄ + TD + 2 * KD, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have hT₄t : T₄ ≤ t := by linarith
  have hTDt : TD ≤ t := by linarith
  have h2K : 2 * KD ≤ t := by linarith
  have ht1 : 1 ≤ t := hT₄.trans hT₄t
  have ht0 : 0 < t := by linarith
  have hZ := partition_pos' hlam hgamma hdisc ht0
  rw [gibbsExpectation_locPotential1 hlam hgamma hdisc ht0]
  have e₄ := h₄ hT₄t
  have eD := hD hTDt
  set N₄ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4 * locWeight g x₀ x) with hN₄
  set M₄ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4) with hM₄
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
  have hDhalf : 1 / 2 ≤ D := by
    have h1 : KD / t ≤ 1 / 2 := by rw [div_le_iff₀ ht0]; linarith
    have h2 := (abs_le.mp (eD.trans h1)).1
    linarith
  have hD0 : 0 < D := by linarith
  have hN₄0 : 0 ≤ N₄ := gibbsExpectation_nonneg' hZ fun x => by
    have := locWeight_pos (g := g) (x₀ := x₀) x; positivity
  have hN₄le : N₄ ≤ Real.exp (g * x₀ ^ 2 / 2) * M₄ := by
    have hint : Integrable (fun x => Real.exp (g * x₀ ^ 2 / 2) * x ^ 4 *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
      ((integrable_pow_exp' hlam hgamma hdisc ht0 4).const_mul (Real.exp (g * x₀ ^ 2 / 2))).congr
        (Eventually.of_forall fun x => by ring)
    have := gibbsExpectation_mono' hZ
      (integrable_pow_locWeight hlam hgamma hdisc hg ht0 (x₀ := x₀) 4) hint (fun x => by
        rw [mul_comm (Real.exp _)]
        exact mul_le_mul_of_nonneg_left (locWeight_le hg x) (by positivity))
    rwa [gibbsExpectation_const_mul₁] at this
  refine ⟨by positivity, ?_⟩
  rw [show t * (N₄ / D) = (t * N₄) / D by ring, div_le_iff₀ hD0]
  calc t * N₄ ≤ t * (Real.exp (g * x₀ ^ 2 / 2) * M₄) := mul_le_mul_of_nonneg_left hN₄le ht0.le
    _ ≤ t * (Real.exp (g * x₀ ^ 2 / 2) * (C₄ / t ^ 2)) := by gcongr
    _ = 2 * Real.exp (g * x₀ ^ 2 / 2) * C₄ / t * (1 / 2) := by
        field_simp
    _ ≤ 2 * Real.exp (g * x₀ ^ 2 / 2) * C₄ / t * D := by gcongr

omit hlam hgamma hdisc in
theorem anharmonicPotential_eq_lin :
    anharmonicPotential lam alpha gamma =
      fun x => lam / 2 * x ^ 2 + alpha / 6 * x ^ 3 + gamma / 24 * x ^ 4 := rfl

/-- `⟨ℓ⟩_loc = (λ/2)⟨x²⟩_loc + (α/6)⟨x³⟩_loc + (γ/24)⟨x⁴⟩_loc`. -/
theorem locEnergy_eq (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) =
      lam / 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 2) +
        alpha / 6 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 3) +
        gamma / 24 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 4) := by
  rw [anharmonicPotential_eq_lin]
  exact gibbs_lin3 (integrable_pow_locPotential1 hlam hgamma hdisc hg ht 2)
    (integrable_pow_locPotential1 hlam hgamma hdisc hg ht 3)
    (integrable_pow_locPotential1 hlam hgamma hdisc hg ht 4)

/-- **E3's localised LLC in one dimension**: `|t⟨ℓ⟩_loc − ½·tλ/(tλ + g)| ≤ K/t`. -/
theorem localisedEnergy_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) - 1 / 2 * (t * lam / (t * lam + g))| ≤ K / t := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locSecondMoment_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locThirdMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_le hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨lam / 2 * K₂ + |alpha| / 6 * K₃ + gamma / 24 * K₄, T₂ + T₃ + T₄, by positivity,
    by linarith, fun {t} ht => ?_⟩
  have hT₂t : T₂ ≤ t := by linarith
  have hT₃t : T₃ ≤ t := by linarith
  have hT₄t : T₄ ≤ t := by linarith
  have ht1 : 1 ≤ t := hT₂.trans hT₂t
  have ht0 : 0 < t := by linarith
  rw [locEnergy_eq hlam hgamma hdisc hg ht0]
  have e₂ := h₂ hT₂t
  have e₃ := h₃ hT₃t
  obtain ⟨h₄0, h₄'⟩ := h₄ hT₄t
  set M₂ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 2) with hM₂
  set M₃ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 3) with hM₃
  set M₄ := _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
    (fun x => x ^ 4) with hM₄
  have key : t * (lam / 2 * M₂ + alpha / 6 * M₃ + gamma / 24 * M₄) -
      1 / 2 * (t * lam / (t * lam + g)) =
      lam / 2 * (t * M₂ - t / (t * lam + g)) + alpha / 6 * (t * M₃) + gamma / 24 * (t * M₄) := by
    ring
  rw [key]
  calc |lam / 2 * (t * M₂ - t / (t * lam + g)) + alpha / 6 * (t * M₃) + gamma / 24 * (t * M₄)|
      ≤ |lam / 2 * (t * M₂ - t / (t * lam + g))| + |alpha / 6 * (t * M₃)| +
          |gamma / 24 * (t * M₄)| := abs_add_three _ _ _
    _ = lam / 2 * |t * M₂ - t / (t * lam + g)| + |alpha| / 6 * |t * M₃| +
          gamma / 24 * (t * M₄) := by
        rw [abs_mul (lam / 2), abs_of_pos (by positivity : (0 : ℝ) < lam / 2),
          abs_mul (alpha / 6), abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6),
          abs_mul (gamma / 24), abs_of_pos (by positivity : (0 : ℝ) < gamma / 24),
          abs_of_nonneg h₄0]
    _ ≤ lam / 2 * (K₂ / t) + |alpha| / 6 * (K₃ / t) + gamma / 24 * (K₄ / t) := by gcongr
    _ = (lam / 2 * K₂ + |alpha| / 6 * K₃ + gamma / 24 * K₄) / t := by ring

end OneDim

/-! ### `d` dimensions: E2's oscillator with the isotropic localiser -/

section E2

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- **Separability of the localised energy**: `⟨L∘A⟩_loc = ∑ᵢ ⟨ℓᵢ⟩_loc,i`, the observable being the
unlocalised energy `L∘A` under the localised measure. -/
theorem localisedRotatedAnharmonic_energy_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) =
      ∑ i, _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) := by
  have hcont := continuous_localisedPotential (continuous_separableAnharmonic lam alpha gamma) g
    (affineFrame Q c w₀) t
  have hint : ∀ i, Integrable (fun u : Fin d → ℝ =>
      anharmonicPotential (lam i) (alpha i) (gamma i) (u i) *
        Real.exp (-(t * localisedPotential (separableAnharmonic lam alpha gamma) g
          (affineFrame Q c w₀) t u))) := fun i => by
    have hc : Continuous fun u : Fin d → ℝ =>
        anharmonicPotential (lam i) (alpha i) (gamma i) (u i) := by
      unfold anharmonicPotential; fun_prop
    exact integrable_localised_of_integrable (L := separableAnharmonic lam alpha gamma)
      (φ := fun u => anharmonicPotential (lam i) (alpha i) (gamma i) (u i)) hg _ ht
      (Continuous.aestronglyMeasurable (by fun_prop))
      (integrable_coord_energy_separableAnharmonic hlam hgamma hdisc ht i)
  rw [separableAnharmonic, localisedPotential_separable] at hcont hint
  rw [localisedRotatedAnharmonic_eq_rotated hQ, rotatedAnharmonic,
    gibbsExpectation_rotated_of_continuous hQ c hcont
      (continuous_separableAnharmonic lam alpha gamma) t]
  have hfun : separableAnharmonic lam alpha gamma =
      fun u => ∑ i, anharmonicPotential (lam i) (alpha i) (gamma i) (u i) := rfl
  rw [hfun, gibbsExpectation_finsetSum _ _ Finset.univ _ (fun i _ => hint i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gibbsExpectation_coord_separable _ t (fun k => (partitionFunction_localisedAnharmonic_pos
    (hlam k) (hgamma k) (hdisc k) hg ht).ne') i]
  rfl

/-- `tr(tH (tH + gI)⁻¹) = ∑ᵢ tλᵢ/(tλᵢ + g)` on E2's tensors. -/
theorem trace_smul_locS_rot (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) :
    (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace =
      ∑ i, t * lam i / (t * lam i + g) := by
  have h1 : t • (Q * diagonal lam * Qᵀ) = Q * diagonal (fun i => t * lam i) * Qᵀ := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    rfl
  rw [h1, locS_rot hQ hlam hg ht, conj_mul_conj hQ, diagonal_mul_diagonal, Matrix.trace_mul_cycle,
    hQ, Matrix.one_mul, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **E3's localised LLC on E2's exact localised measure**:
`|t⟨L∘A⟩_loc − ½ tr(tH(tH + gI)⁻¹)| ≤ K/t`. -/
theorem localisedRotatedAnharmonic_llc_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) -
        1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace| ≤
        K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div (fun _ : Fin d => (1 : ℝ))
    (fun i t => t * _root_.Laplace.gibbsExpectation
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
      (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 * (t * lam i / (t * lam i + g)))
    (fun i => localisedEnergy_rate (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) -
      1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace =
      ∑ i, 1 * (t * _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) -
          1 / 2 * (t * lam i / (t * lam i + g))) := by
    rw [localisedRotatedAnharmonic_energy_coord hQ c w₀ hlam hgamma hdisc hg ht0,
      trace_smul_locS_rot hQ hlam hg ht0, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  exact h ht

/-- The trace prediction's algebra: `½ tr(tH(tH + gI)⁻¹) = d/2 − ½∑ᵢ g/(tλᵢ + g)`. -/
theorem trace_smul_locS_rot_eq (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) :
    1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace =
      (d : ℝ) / 2 - 1 / 2 * ∑ i, g / (t * lam i + g) := by
  rw [trace_smul_locS_rot hQ hlam hg ht, Finset.mul_sum, Finset.mul_sum]
  have e : ∀ i, 1 / 2 * (t * lam i / (t * lam i + g)) = 1 / 2 - 1 / 2 * (g / (t * lam i + g)) := by
    intro i
    have := hlam i
    have hpos : 0 < t * lam i + g := by positivity
    field_simp
    ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Localisation lowers the trace prediction: `½ tr(tH(tH + gI)⁻¹) ≤ d/2`. -/
theorem trace_smul_locS_rot_le (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) :
    1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace ≤
      (d : ℝ) / 2 := by
  rw [trace_smul_locS_rot_eq hQ hlam hg ht]
  have : 0 ≤ ∑ i, g / (t * lam i + g) := Finset.sum_nonneg fun i _ => by
    have := hlam i; positivity
  linarith

/-- **The localised LLC at leading order**: `|t⟨L∘A⟩_loc − d/2| ≤ K/t`. -/
theorem localisedRotatedAnharmonic_llc_leading (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) - (d : ℝ) / 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedRotatedAnharmonic_llc_rate hQ c w₀ hlam hgamma hdisc hg
  have hsum : 0 ≤ ∑ i, g / lam i := Finset.sum_nonneg fun i _ => div_nonneg hg (hlam i).le
  refine ⟨K + 1 / 2 * ∑ i, g / lam i, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have hd : |1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace -
      (d : ℝ) / 2| ≤ (1 / 2 * ∑ i, g / lam i) / t := by
    have hs : 0 ≤ ∑ i, g / (t * lam i + g) := Finset.sum_nonneg fun i _ => by
      have := hlam i; positivity
    rw [trace_smul_locS_rot_eq hQ hlam hg ht0,
      show (d : ℝ) / 2 - 1 / 2 * ∑ i, g / (t * lam i + g) - (d : ℝ) / 2 =
        -(1 / 2 * ∑ i, g / (t * lam i + g)) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (by norm_num) hs)]
    have hterm : ∀ i, g / (t * lam i + g) ≤ g / lam i / t := fun i => by
      have := hlam i
      rw [div_div, mul_comm]
      exact div_le_div_of_nonneg_left hg (by positivity) (le_add_of_nonneg_right hg)
    calc 1 / 2 * ∑ i, g / (t * lam i + g) ≤ 1 / 2 * ∑ i, g / lam i / t :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by norm_num)
      _ = (1 / 2 * ∑ i, g / lam i) / t := by rw [← Finset.sum_div]; ring
  calc |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) - (d : ℝ) / 2|
      ≤ |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) -
          1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace| +
        |1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace -
          (d : ℝ) / 2| := abs_sub_le _ _ _
    _ ≤ K / t + (1 / 2 * ∑ i, g / lam i) / t := add_le_add (h ht) hd
    _ = (K + 1 / 2 * ∑ i, g / lam i) / t := by ring

end E2

end Laplace.Multi
