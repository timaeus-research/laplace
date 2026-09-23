/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedLaplaceCorrection

/-!
# The transform-level gap between the localised law and its Gaussian prediction is governed by `C₁`

E3 predicts the localised law by the Gaussian with precision `tH + gI`; under it the LLC statistic's
Laplace transform is exactly `∏ᵢ √((tλᵢ + g)/((1+s)tλᵢ + g))`
(`Laplace.Sampler.laplace_localisedGibbs`,
here written as the explicit product over the frame spectrum). This prediction carries its own
finite-temperature correction from the localiser,
`∏ᵢ √((tλᵢ + g)/((1+s)tλᵢ + g)) = (1+s)^{−d/2}(1 + s·g∑ᵢ1/(2λᵢ)/((1+s)t)) + O(t⁻²)`
(`gaussianTransform_rate2`, from the elementary two-sided bound `1 + x/2 − x²/2 ≤ √(1+x) ≤ 1 +
x/2`).
Combined with `LocalisedLaplaceCorrection`'s expansion of the exact anharmonic localised transform,
**`⟨e^{−st·L∘A}⟩_loc − ∏ᵢ√((tλᵢ + g)/((1+s)tλᵢ + g)) = −s·C₁/((1+s)^{d/2+1}t) + O(t⁻²)`**
(`localisedLaplace_gaussianGap`) with `C₁ = ∑ᵢ(e₁ᵢ + g/(2λᵢ))` — the same invariant coefficient
that governs the scaled energy gap `t⟨L∘A⟩_loc − tP = C₁/t` (`LocalisedEnergyInvariant`) and the
derivative gap `−∂ₜ⟨L∘A⟩_loc + P' = 2C₁/t³` (`LocalisedEnergyVarOrder2`). The prediction is the
*centred*
Gaussian with precision `tH + gI` (the anchored Gaussian would shift `C₁` by `−∑ᵢaᵢ²/(2λᵢ)`).
Pointwise
in `s > −1`; fixed `g, w₀` and quartic parameters; no differentiation of the remainder is claimed.
-/

open Matrix Filter Topology Laplace.OneD

namespace Laplace.Multi

/-! ### The square root near `1` -/

/-- The exact first-order remainder of the square root: for `x ≥ −1`,
`√(1+x) − 1 − x/2 = −(√(1+x) − 1)²/2`, hence `|√(1+x) − 1 − x/2| ≤ x²/2`. -/
theorem sqrt_one_add_sub_le {x : ℝ} (hx : -1 ≤ x) :
    |Real.sqrt (1 + x) - 1 - x / 2| ≤ x ^ 2 / 2 := by
  have hr : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have hr0 := Real.sqrt_nonneg (1 + x)
  have e : Real.sqrt (1 + x) - 1 - x / 2 = -((Real.sqrt (1 + x) - 1) ^ 2 / 2) := by
    linear_combination (1 / 2) * hr
  have hx2 : (Real.sqrt (1 + x) - 1) ^ 2 ≤ x ^ 2 := by
    have e2 : (Real.sqrt (1 + x) - 1) * (Real.sqrt (1 + x) + 1) = x := by linear_combination hr
    have h1 : (Real.sqrt (1 + x) - 1) ^ 2 * 1 ≤
        (Real.sqrt (1 + x) - 1) ^ 2 * (Real.sqrt (1 + x) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    rw [← mul_pow, e2] at h1
    linarith
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  linarith

/-! ### The Gaussian prediction's finite-temperature correction -/

/-- The single rational perturbation: `√(1+s)·√((tλ + g)/((1+s)tλ + g)) = √(1 + sg/((1+s)tλ + g))`.
-/
theorem sqrt_gaussianFactor_eq {lam g s t : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) (hs : -1 < s)
    (ht : 0 < t) :
    Real.sqrt (1 + s) * Real.sqrt ((t * lam + g) / ((1 + s) * t * lam + g)) =
      Real.sqrt (1 + s * g / ((1 + s) * t * lam + g)) := by
  have ha : 0 < 1 + s := by linarith
  have h1 : 0 < (1 + s) * t * lam + g := by positivity
  rw [← Real.sqrt_mul ha.le]
  congr 1
  field_simp
  ring

/-- **The per-direction Gaussian factor**:
`√(1+s)·√((tλ + g)/((1+s)tλ + g)) = 1 + (gs/(2λ(1+s)))/t + O(t⁻²)`, with the explicit constant
`g²(|s| + s²)/(2(1+s)²λ²)` and no smallness threshold. -/
theorem gaussianFactor_rate2 {lam g s : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) (hs : -1 < s) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |Real.sqrt (1 + s) * Real.sqrt ((t * lam + g) / ((1 + s) * t * lam + g)) - 1 -
        g * s / (2 * lam * (1 + s)) / t| ≤ K / t ^ 2 := by
  have ha : 0 < 1 + s := by linarith
  refine ⟨g ^ 2 * (|s| + s ^ 2) / (2 * (1 + s) ^ 2 * lam ^ 2), 1, by positivity, le_rfl,
    fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hden : 0 < (1 + s) * t * lam + g := by positivity
  have hl : lam ≠ 0 := hlam.ne'
  rw [sqrt_gaussianFactor_eq hlam hg hs ht0]
  set z := s * g / ((1 + s) * t * lam + g) with hz
  have hz1 : -1 ≤ z := by
    have e : 1 + z = (1 + s) * ((t * lam + g) / ((1 + s) * t * lam + g)) := by
      rw [hz]
      field_simp
      ring
    have : 0 < 1 + z := by
      rw [e]
      positivity
    linarith
  have h1 := sqrt_one_add_sub_le hz1
  have hzb : |z| ≤ |s| * g / ((1 + s) * t * lam) := by
    rw [hz, abs_div, abs_of_pos hden, abs_mul, abs_of_nonneg hg]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hdiff : z / 2 - g * s / (2 * lam * (1 + s)) / t =
      -(s * g ^ 2 / (2 * (1 + s) * t * lam * ((1 + s) * t * lam + g))) := by
    rw [hz]
    field_simp
    ring
  have hdiffb : |z / 2 - g * s / (2 * lam * (1 + s)) / t| ≤
      |s| * g ^ 2 / (2 * (1 + s) ^ 2 * lam ^ 2 * t ^ 2) := by
    have hD : 0 < 2 * (1 + s) * t * lam * ((1 + s) * t * lam + g) := by positivity
    rw [hdiff, abs_neg, abs_div, abs_mul, abs_of_nonneg (sq_nonneg g), abs_of_pos hD]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [mul_pos (mul_pos ha ht0) hlam]
  have hz2 : z ^ 2 / 2 ≤ s ^ 2 * g ^ 2 / (2 * (1 + s) ^ 2 * lam ^ 2 * t ^ 2) := by
    have h2 : z ^ 2 ≤ (|s| * g / ((1 + s) * t * lam)) ^ 2 := by
      rw [← sq_abs z]
      exact pow_le_pow_left₀ (abs_nonneg z) hzb 2
    have e : (|s| * g / ((1 + s) * t * lam)) ^ 2 =
        s ^ 2 * g ^ 2 / ((1 + s) ^ 2 * lam ^ 2 * t ^ 2) := by
      rw [div_pow, mul_pow, sq_abs]
      ring
    rw [e] at h2
    have e2 : s ^ 2 * g ^ 2 / ((1 + s) ^ 2 * lam ^ 2 * t ^ 2) / 2 =
        s ^ 2 * g ^ 2 / (2 * (1 + s) ^ 2 * lam ^ 2 * t ^ 2) := by
      rw [div_div]
      ring
    linarith
  have e : Real.sqrt (1 + z) - 1 - g * s / (2 * lam * (1 + s)) / t =
      (Real.sqrt (1 + z) - 1 - z / 2) + (z / 2 - g * s / (2 * lam * (1 + s)) / t) := by ring
  rw [e]
  calc _ ≤ |Real.sqrt (1 + z) - 1 - z / 2| + |z / 2 - g * s / (2 * lam * (1 + s)) / t| :=
        abs_add_le _ _
    _ ≤ s ^ 2 * g ^ 2 / (2 * (1 + s) ^ 2 * lam ^ 2 * t ^ 2) +
        |s| * g ^ 2 / (2 * (1 + s) ^ 2 * lam ^ 2 * t ^ 2) := add_le_add (h1.trans hz2) hdiffb
    _ = _ := by
        rw [← add_div, div_div]
        ring

/-- **The Gaussian prediction's own correction**: `∏ᵢ√((tλᵢ + g)/((1+s)tλᵢ + g)) =
(1+s)^{−d/2}(1 + s·g∑ᵢ1/(2λᵢ)/((1+s)t)) + O(t⁻²)` — purely from the localiser (it vanishes at `g =
0`). -/
theorem gaussianTransform_rate2 {d : ℕ} {lam : Fin d → ℝ} {g s : ℝ} (hlam : ∀ i, 0 < lam i)
    (hg : 0 ≤ g) (hs : -1 < s) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |(∏ i, Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) - (1 / Real.sqrt (1 + s)) ^ d
        * (1 + (∑ i, g * s / (2 * lam i * (1 + s))) / t)| ≤ K / t ^ 2 := by
  choose K T hK hT h using fun i => gaussianFactor_rate2 (hlam i) hg hs
  obtain ⟨C, T', hC, hT', hprod⟩ := prod_one_rate2 Finset.univ
    (fun i t => Real.sqrt (1 + s) * Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) (fun i
      => g * s / (2 * lam i * (1 + s))) K T hK hT (fun i {t} ht => h i ht)
  have ha : 0 < 1 + s := by linarith
  have hsa : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr ha
  refine ⟨(1 / Real.sqrt (1 + s)) ^ d * C, T', by positivity, hT', fun {t} ht => ?_⟩
  have e : (1 / Real.sqrt (1 + s)) ^ d * ∏ i, (Real.sqrt (1 + s) * Real.sqrt ((t * lam i + g) / ((1
      + s) * t * lam i + g))) = ∏ i, Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_assoc,
      ← mul_pow, one_div_mul_cancel hsa.ne', one_pow, one_mul]
  rw [← e, ← mul_sub, sub_add_eq_sub_sub, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (1 / Real.sqrt (1 + s)) ^ d)]
  calc _ ≤ (1 / Real.sqrt (1 + s)) ^ d * (C / t ^ 2) :=
        mul_le_mul_of_nonneg_left (hprod ht) (by positivity)
    _ = _ := by ring

/-! ### The gap -/

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The transform-level gap is governed by `C₁`**: for each fixed `s > −1`,
`⟨e^{−st·L∘A}⟩_loc − ∏ᵢ√((tλᵢ + g)/((1+s)tλᵢ + g)) = −(1+s)^{−d/2}·sC₁/(1+s)/t + O(t⁻²)`,
`C₁ = ∑ᵢ(e₁ᵢ + g/(2λᵢ))` — the coefficient of the scaled energy gap `t⟨L∘A⟩_loc − ½t·tr(H(tH +
gI)⁻¹) = C₁/t`
and of the derivative gap `2C₁/t³`; the prediction is the centred Gaussian. -/
theorem localisedLaplace_gaussianGap (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {s : ℝ}
    (hs : -1 < s) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => Real.exp
        (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) - (∏ i, Real.sqrt ((t * lam i + g) /
        ((1 + s) * t * lam i + g))) + (1 / Real.sqrt (1 + s)) ^ d * (s * (∑ i, (energyLocCoeff1 (lam
        i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i))) / (1 + s) / t)| ≤ K / t
        ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := localisedLaplace_rate2 hlam hgamma hdisc hQ c w₀ hg hs
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := gaussianTransform_rate2 hlam hg hs (s := s)
  have ha : 0 < 1 + s := by linarith
  refine ⟨K₁ + K₂, T₁ + T₂, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e₁ := h₁ (t := t) (by linarith)
  have e₂ := h₂ (t := t) (by linarith)
  have hX : (∑ i, -(energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) * s / (1 +
      s))) - ∑ i, g * s / (2 * lam i * (1 + s)) = -(s * (∑ i, (energyLocCoeff1 (lam i) (alpha i)
      (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i))) / (1 + s)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hlam i).ne'
    have := ha.ne'
    field_simp
    ring
  have e : gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w =>
      Real.exp (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) - (∏ i, Real.sqrt ((t * lam i +
      g) / ((1 + s) * t * lam i + g))) + (1 / Real.sqrt (1 + s)) ^ d * (s * (∑ i, (energyLocCoeff1
      (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i))) / (1 + s) / t) =
      (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => Real.exp
      (-(s * t * rotatedAnharmonic Q c lam alpha gamma w))) - (1 / Real.sqrt (1 + s)) ^ d * (1 + (∑
      i, -(energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) * s / (1 + s))) /
      t)) - ((∏ i, Real.sqrt ((t * lam i + g) / ((1 + s) * t * lam i + g))) - (1 / Real.sqrt (1 +
      s)) ^ d * (1 + (∑ i, g * s / (2 * lam i * (1 + s))) / t)) := by
    linear_combination ((1 / Real.sqrt (1 + s)) ^ d / t) * hX
  rw [e]
  calc _ ≤ |_| + |_| := abs_sub _ _
    _ ≤ K₁ / t ^ 2 + K₂ / t ^ 2 := add_le_add e₁ e₂
    _ = _ := by ring

end Multi

end Laplace.Multi
