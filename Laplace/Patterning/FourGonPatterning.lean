/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.FourGonSusceptibility

/-!
# Patterning the dead unit into a gap

The pipeline solves `χ ω = dμ` for a minimal-norm mean-zero reweighting `ω` and trains on the
reweighted loss. With the direction rows of the 4-gon susceptibility matrix
(`χ(dⱼ; hⱼ) = −c`, `χ(dⱼ; hⱼ₊₂) = +c`, zero otherwise) and the target `dμ = (+1, +1, −1, −1)` for
the gap between features `0` and `1`:

* the reweighting `ω* = (−1, −1, +1, +1, 0)/(2c)` solves `χ ω* = dμ`, has mean zero, and is the
  minimal-norm mean-zero solution (`omegaStar_solves`, `omegaStar_sum`, `omegaStar_minimal`):
  lower the two features flanking the target gap, raise the opposite two, leave the dead one
  (the note's `ω = (−0.48, −0.48, +0.49, +0.50, −0.03)`);
* under `h = h₀ + ε ω*` the stability coefficient of the ray at angle `θ` is
  `a(θ) = −(ε/6c)(cos θ |cos θ| + sin θ |sin θ|)`, which is negative exactly when
  `cos θ + sin θ > 0` (`stabilityCoeff_omegaStar`, `stabilityCoeff_omegaStar_neg_iff`): the
  dead unit is destabilised precisely in the target half-plane, and along every such ray the
  reweighted loss drops below the plateau (`weightedLoss_omegaStar_lt`).

This is the exact content behind the note's which-gap experiment (every grown seed in the target
half-plane; the non-growing seeds are the kicks into the opposite gap, where `a > 0`).
-/

namespace Laplace.Patterning

open Real

noncomputable section

/-- The pipeline's reweighting for the gap between features `0` and `1`, at direction coefficient
`c`: `ω* = (−1, −1, +1, +1, 0)/(2c)`. -/
def omegaStar (c : ℝ) : Fin 5 → ℝ := ![-(1 / (2 * c)), -(1 / (2 * c)), 1 / (2 * c), 1 / (2 * c), 0]

/-- The target `dμ = (+1, +1, −1, −1)` on the four directions. -/
def gapTarget : Fin 4 → ℝ := ![1, 1, -1, -1]

theorem omegaStar_sum (c : ℝ) : ∑ i, omegaStar c i = 0 := by
  simp [omegaStar, Fin.sum_univ_five]

/-- **`ω*` solves `χ ω* = dμ`**: `∑ᵢ χ(dⱼ; hᵢ) ω*ᵢ = dμⱼ` for each direction `j`. -/
theorem omegaStar_solves (t : ℝ) (ht : 0 < t) (j : Fin 4) :
    ∑ i, deadChi t (dirObs (featureAngle j)) i * omegaStar (dirCoeff t) i = gapTarget j := by
  have hc := (dirCoeff_pos t ht).ne'
  rw [Fin.sum_univ_five]
  have h0 := deadChi_dirObs_alive t (featureAngle j) 0
  have h1 := deadChi_dirObs_alive t (featureAngle j) 1
  have h2 := deadChi_dirObs_alive t (featureAngle j) 2
  have h3 := deadChi_dirObs_alive t (featureAngle j) 3
  simp only [Fin.castSucc_zero] at h0
  rw [show (1 : Fin 5) = Fin.castSucc (1 : Fin 4) from rfl, h1,
    show (2 : Fin 5) = Fin.castSucc (2 : Fin 4) from rfl, h2,
    show (3 : Fin 5) = Fin.castSucc (3 : Fin 4) from rfl, h3, h0, deadChi_dirObs_dead]
  fin_cases j <;>
    simp [omegaStar, gapTarget, featureAngle, cos_sub, cos_add, cos_pi_div_two, sin_pi_div_two,
      cos_pi, sin_pi] <;> field_simp <;> ring

/-- **Minimality.** Every mean-zero solution of the two independent equations
`c(ω₂ − ω₀) = 1`, `c(ω₃ − ω₁) = 1` has norm at least that of `ω*`. -/
theorem omegaStar_minimal {c : ℝ} (hc : c ≠ 0) (ω : Fin 5 → ℝ)
    (h0 : c * (ω 2 - ω 0) = 1) (h1 : c * (ω 3 - ω 1) = 1) :
    ∑ i, omegaStar c i ^ 2 ≤ ∑ i, ω i ^ 2 := by
  have hstar : ∑ i, omegaStar c i ^ 2 = 1 / c ^ 2 := by
    simp [Fin.sum_univ_five, omegaStar]
    field_simp
    try ring
  have hω : ∑ i, ω i ^ 2 = ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2 + ω 3 ^ 2 + ω 4 ^ 2 := Fin.sum_univ_five _
  rw [hstar, hω]
  have e0 : ω 2 - ω 0 = 1 / c := by field_simp; linarith
  have e1 : ω 3 - ω 1 = 1 / c := by field_simp; linarith
  have i0 : (ω 2 - ω 0) ^ 2 ≤ 2 * (ω 0 ^ 2 + ω 2 ^ 2) := by nlinarith [sq_nonneg (ω 0 + ω 2)]
  have i1 : (ω 3 - ω 1) ^ 2 ≤ 2 * (ω 1 ^ 2 + ω 3 ^ 2) := by nlinarith [sq_nonneg (ω 1 + ω 3)]
  rw [e0] at i0
  rw [e1] at i1
  have : (1 / c) ^ 2 = 1 / c ^ 2 := by field_simp
  rw [this] at i0 i1
  nlinarith [sq_nonneg (ω 4), i0, i1]

/-- `[−x]₊² − [x]₊² = −x|x|`. -/
theorem relu_neg_sq_sub_relu_sq (x : ℝ) : relu (-x) ^ 2 - relu x ^ 2 = -(x * |x|) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [relu_of_nonneg hx, relu_of_nonpos (by linarith), abs_of_nonneg hx]
    ring
  · rw [relu_of_nonpos hx.le, relu_of_nonneg (by linarith), abs_of_neg hx]
    ring

/-- **The stability coefficient of the pipeline's reweighting**:
`a(θ; h₀ + ε ω*) = −(ε/6c)(cos θ |cos θ| + sin θ |sin θ|)`. -/
theorem stabilityCoeff_omegaStar (c ε θ : ℝ) (hc : c ≠ 0) :
    stabilityCoeff (fun i => 1 / 5 + ε * omegaStar c i) θ
      = -(ε / (6 * c)) * (cos θ * |cos θ| + sin θ * |sin θ|) := by
  have hcos := relu_neg_sq_sub_relu_sq (cos θ)
  have hsin := relu_neg_sq_sub_relu_sq (sin θ)
  have hc' := relu_sq_add_relu_neg_sq (cos θ)
  have hs' := relu_sq_add_relu_neg_sq (sin θ)
  have hsc := sin_sq_add_cos_sq θ
  have e0 : omegaStar c 0 = -(1 / (2 * c)) := by simp [omegaStar]
  have e1 : omegaStar c 1 = -(1 / (2 * c)) := by simp [omegaStar]
  have e2 : omegaStar c 2 = 1 / (2 * c) := by simp [omegaStar]
  have e3 : omegaStar c 3 = 1 / (2 * c) := by simp [omegaStar]
  have e4 : omegaStar c 4 = 0 := by simp [omegaStar]
  rw [stabilityCoeff, e0, e1, e2, e3, e4,
    show relu (-cos θ) ^ 2 = cos θ ^ 2 - relu (cos θ) ^ 2 by linarith [hc'],
    show relu (-sin θ) ^ 2 = sin θ ^ 2 - relu (sin θ) ^ 2 by linarith [hs'],
    show cos θ * |cos θ| = 2 * relu (cos θ) ^ 2 - cos θ ^ 2 by linarith [hcos, hc'],
    show sin θ * |sin θ| = 2 * relu (sin θ) ^ 2 - sin θ ^ 2 by linarith [hsin, hs'],
    show cos θ ^ 2 = 1 - sin θ ^ 2 by linarith [hsc]]
  field_simp
  ring

/-- `x ↦ x|x|` is strictly increasing. -/
theorem mul_abs_strictMono : StrictMono fun x : ℝ => x * |x| := by
  intro a b hab
  simp only
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha, abs_of_nonneg (ha.trans hab.le)]
    nlinarith
  · rw [abs_of_neg ha]
    rcases le_or_gt 0 b with hb | hb
    · rw [abs_of_nonneg hb]
      nlinarith [mul_pos (neg_pos.mpr ha) (neg_pos.mpr ha), sq_nonneg b]
    · rw [abs_of_neg hb]
      nlinarith

/-- `x|x| + y|y| > 0 ↔ x + y > 0`. -/
theorem mul_abs_add_mul_abs_pos_iff (x y : ℝ) : 0 < x * |x| + y * |y| ↔ 0 < x + y := by
  have h : (-y) * |-y| = -(y * |y|) := by rw [abs_neg]; ring
  constructor
  · intro hpos
    have hlt : (-y) * |-y| < x * |x| := by rw [h]; linarith
    have := mul_abs_strictMono.lt_iff_lt.mp hlt
    linarith
  · intro hxy
    have hlt : -y < x := by linarith
    have := mul_abs_strictMono hlt
    simp only at this
    rw [h] at this
    linarith

/-- **The target half-plane.** For `ε, c > 0`, the pipeline's reweighting destabilises the dead
unit along the ray at angle `θ` exactly when `cos θ + sin θ > 0`. -/
theorem stabilityCoeff_omegaStar_neg_iff {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (θ : ℝ) :
    stabilityCoeff (fun i => 1 / 5 + ε * omegaStar c i) θ < 0 ↔ 0 < cos θ + sin θ := by
  rw [stabilityCoeff_omegaStar c ε θ hc.ne', ← mul_abs_add_mul_abs_pos_iff, neg_mul, neg_lt_zero]
  exact mul_pos_iff_of_pos_left (by positivity)

/-- Along a destabilised ray the reweighted loss drops below the plateau for small `r`. -/
theorem weightedLoss_omegaStar_lt {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {θ r : ℝ}
    (hθ : 0 < cos θ + sin θ) (hr : 0 < r)
    (hsmall : r ^ 2 < -15 * stabilityCoeff (fun i => 1 / 5 + ε * omegaStar c i) θ) :
    weightedLoss (fun i => 1 / 5 + ε * omegaStar c i) (fourGon (r * cos θ) (r * sin θ))
      < weightedLoss (fun i => 1 / 5 + ε * omegaStar c i) (fourGon 0 0) := by
  have ha := (stabilityCoeff_omegaStar_neg_iff hc hε θ).mpr hθ
  have h4 : omegaStar c 4 = 0 := by simp [omegaStar]
  have hray := weightedLoss_fourGon_ray (fun i => 1 / 5 + ε * omegaStar c i) r θ hr.le
  simp only [h4, mul_zero, add_zero] at hray
  have : stabilityCoeff (fun i => 1 / 5 + ε * omegaStar c i) θ * r ^ 2 + 1 / 5 / 3 * r ^ 4 < 0 := by
    have hr2 : 0 < r ^ 2 := by positivity
    nlinarith
  linarith

end

end Laplace.Patterning
