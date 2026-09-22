/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedDerivative

/-!
# eq:covK on the localised measure to second order

`LocalisedCovK` gave the leading order of `t²Cov_loc[ℓ, xⁿ]`; `LocalisedDerivative` the exact
Stein–covariance reduction
`t²Cov_loc[ℓ, xⁿ] = (n/2)t mₙ − (α/12)t²C_{3,n} − (γ/24)t²C_{4,n} − (g/2)tC_{2,n} + (a/2)tC_{1,n}`.
Feeding it the localised moments — `t m₁`, `t m₂` to second order (tides 72, 73), `t²m₃`, `t²m₄` to
second order (the fourth is new here), `t³m₅`, `t³m₆` at leading order (new) — gives

`t²Cov_loc[ℓ, x] = c + 2c'/t + O(t⁻²)`, `t²Cov_loc[ℓ, x²] = 1/λ + 2c₂'/t + O(t⁻²)`:

the derivative reading `Cov_loc = −∂ₜ⟨·⟩_loc` holds coefficientwise at second order under
localisation, with no differentiation of remainders.
-/

open Real MeasureTheory Filter Topology Laplace.OneD
open scoped Nat

namespace Laplace.Multi

/-! ### Pointwise envelopes for `x⁴φ` (exact to degree seven) and `x⁶φ` -/

section Weight

variable {g x₀ : ℝ}

/-- `|x⁴φ − (x⁴ + ax⁵ + p₃x⁶ + p₄x⁷)| ≤ H₆x⁸ + H₈x¹⁰ + H₁₀x¹²` (the shared expansion times `x²`, the
degree-six and -seven monomials kept exact). -/
theorem locQuartic_pointwise4 (hg : 0 ≤ g) (x : ℝ) :
    |x ^ 4 * locWeight g x₀ x -
        (x ^ 4 + g * x₀ * x ^ 5 + locP₃ g x₀ * x ^ 6 + locP₄ g x₀ * x ^ 7)| ≤
      locH₆ g x₀ * x ^ 8 + locH₈ g x₀ * x ^ 10 + locH₁₀ g x₀ * x ^ 12 := by
  have hS := locSquare_pointwise (x₀ := x₀) hg x
  have e : x ^ 4 * locWeight g x₀ x -
      (x ^ 4 + g * x₀ * x ^ 5 + locP₃ g x₀ * x ^ 6 + locP₄ g x₀ * x ^ 7) =
      x ^ 2 * (x ^ 2 * locWeight g x₀ x -
        (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)) := by ring
  have hx2 : (0 : ℝ) ≤ x ^ 2 := by positivity
  rw [e, abs_mul, abs_of_nonneg hx2]
  calc x ^ 2 * |x ^ 2 * locWeight g x₀ x -
        (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)|
      ≤ x ^ 2 * (locH₆ g x₀ * x ^ 6 + locH₈ g x₀ * x ^ 8 + locH₁₀ g x₀ * x ^ 10) :=
        mul_le_mul_of_nonneg_left hS hx2
    _ = _ := by ring

/-- The even envelope of the `x⁵φ` remainder beyond `x⁵ + ax⁶ + p₃x⁷ + p₄x⁸` (odd powers to
even). -/
noncomputable def locU₈ (g x₀ : ℝ) : ℝ := locH₆ g x₀ / 2
noncomputable def locU₁₀ (g x₀ : ℝ) : ℝ := locH₆ g x₀ / 2 + locH₈ g x₀ / 2
noncomputable def locU₁₂ (g x₀ : ℝ) : ℝ := locH₈ g x₀ / 2 + locH₁₀ g x₀ / 2
noncomputable def locU₁₄ (g x₀ : ℝ) : ℝ := locH₁₀ g x₀ / 2

theorem locU₈_nonneg (g x₀ : ℝ) : 0 ≤ locU₈ g x₀ := by
  unfold locU₈; have := locH₆_nonneg g x₀; positivity
theorem locU₁₀_nonneg (g x₀ : ℝ) : 0 ≤ locU₁₀ g x₀ := by
  unfold locU₁₀; have := locH₆_nonneg g x₀; have := locH₈_nonneg g x₀; positivity
theorem locU₁₂_nonneg (g x₀ : ℝ) : 0 ≤ locU₁₂ g x₀ := by
  unfold locU₁₂; have := locH₈_nonneg g x₀; have := locH₁₀_nonneg g x₀; positivity
theorem locU₁₄_nonneg (g x₀ : ℝ) : 0 ≤ locU₁₄ g x₀ := by
  unfold locU₁₄; have := locH₁₀_nonneg g x₀; positivity

/-- `|x⁵φ − (x⁵ + ax⁶ + p₃x⁷ + p₄x⁸)| ≤ U₈x⁸ + U₁₀x¹⁰ + U₁₂x¹² + U₁₄x¹⁴` (the shared expansion times
`x³`, all monomials to degree eight kept exact). -/
theorem locFifth_pointwise4 (hg : 0 ≤ g) (x : ℝ) :
    |x ^ 5 * locWeight g x₀ x -
        (x ^ 5 + g * x₀ * x ^ 6 + locP₃ g x₀ * x ^ 7 + locP₄ g x₀ * x ^ 8)| ≤
      locU₈ g x₀ * x ^ 8 + locU₁₀ g x₀ * x ^ 10 + locU₁₂ g x₀ * x ^ 12 + locU₁₄ g x₀ * x ^ 14 := by
  have hS := locSquare_pointwise (x₀ := x₀) hg x
  have e : x ^ 5 * locWeight g x₀ x -
      (x ^ 5 + g * x₀ * x ^ 6 + locP₃ g x₀ * x ^ 7 + locP₄ g x₀ * x ^ 8) =
      x ^ 3 * (x ^ 2 * locWeight g x₀ x -
        (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)) := by ring
  have hx6 : x ^ 6 = |x| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : x ^ 8 = |x| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx10 : x ^ 10 = |x| ^ 10 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx12 : x ^ 12 = |x| ^ 12 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx14 : x ^ 14 = |x| ^ 14 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h9 : |x| ^ 9 ≤ (|x| ^ 8 + |x| ^ 10) / 2 := by nlinarith [sq_nonneg (|x| ^ 4 - |x| ^ 5)]
  have h11 : |x| ^ 11 ≤ (|x| ^ 10 + |x| ^ 12) / 2 := by nlinarith [sq_nonneg (|x| ^ 5 - |x| ^ 6)]
  have h13 : |x| ^ 13 ≤ (|x| ^ 12 + |x| ^ 14) / 2 := by nlinarith [sq_nonneg (|x| ^ 6 - |x| ^ 7)]
  have hH₆ := locH₆_nonneg g x₀
  have hH₈ := locH₈_nonneg g x₀
  have hH₁₀ := locH₁₀_nonneg g x₀
  rw [e, abs_mul, abs_pow]
  calc |x| ^ 3 * |x ^ 2 * locWeight g x₀ x -
        (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)|
      ≤ |x| ^ 3 * (locH₆ g x₀ * x ^ 6 + locH₈ g x₀ * x ^ 8 + locH₁₀ g x₀ * x ^ 10) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = locH₆ g x₀ * |x| ^ 9 + locH₈ g x₀ * |x| ^ 11 + locH₁₀ g x₀ * |x| ^ 13 := by
        rw [hx6, hx8, hx10]; ring
    _ ≤ locH₆ g x₀ * ((|x| ^ 8 + |x| ^ 10) / 2) + locH₈ g x₀ * ((|x| ^ 10 + |x| ^ 12) / 2) +
        locH₁₀ g x₀ * ((|x| ^ 12 + |x| ^ 14) / 2) := by gcongr
    _ = locU₈ g x₀ * x ^ 8 + locU₁₀ g x₀ * x ^ 10 + locU₁₂ g x₀ * x ^ 12 +
        locU₁₄ g x₀ * x ^ 14 := by
        rw [hx8, hx10, hx12, hx14]
        unfold locU₈ locU₁₀ locU₁₂ locU₁₄
        ring

/-- The even envelope of the `x⁶φ` remainder beyond `x⁶ + ax⁷ − (g/2)x⁸`. -/
noncomputable def locS₈ (g x₀ : ℝ) : ℝ := 4 * (Real.exp (g * x₀ ^ 2 / 2) + 2) * |g * x₀| ^ 2
noncomputable def locS₁₀ (g x₀ : ℝ) : ℝ := 4 * (Real.exp (g * x₀ ^ 2 / 2) + 2) * |g / 2| ^ 2

theorem locS₈_nonneg (g x₀ : ℝ) : 0 ≤ locS₈ g x₀ := by unfold locS₈; positivity
theorem locS₁₀_nonneg (g x₀ : ℝ) : 0 ≤ locS₁₀ g x₀ := by unfold locS₁₀; positivity

/-- `|x⁶φ − (x⁶ + ax⁷ − (g/2)x⁸)| ≤ S₈x⁸ + S₁₀x¹⁰` (the signed `x⁷` kept exact). -/
theorem locSixth_pointwise (hg : 0 ≤ g) (x : ℝ) :
    |x ^ 6 * locWeight g x₀ x - (x ^ 6 + g * x₀ * x ^ 7 - g / 2 * x ^ 8)| ≤
      locS₈ g x₀ * x ^ 8 + locS₁₀ g x₀ * x ^ 10 := by
  set y := g * x₀ * x - g / 2 * x ^ 2 with hy
  set C := Real.exp (g * x₀ ^ 2 / 2) + 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hT : |locWeight g x₀ x - ∑ m ∈ Finset.range 2, y ^ m / (m.factorial : ℝ)| ≤ C * |y| ^ 2 := by
    have := locWeight_taylor_le (x₀ := x₀) hg (n := 2) (by norm_num) x
    simpa using this
  have hy2 : |y| ^ 2 ≤ 2 ^ 2 * (|g * x₀| ^ 2 * |x| ^ 2 + |g / 2| ^ 2 * (x ^ 2) ^ 2) :=
    abs_locExponent_pow_le (g * x₀) (g / 2) x 2
  have e : x ^ 6 * locWeight g x₀ x - (x ^ 6 + g * x₀ * x ^ 7 - g / 2 * x ^ 8) =
      x ^ 6 * (locWeight g x₀ x - ∑ m ∈ Finset.range 2, y ^ m / (m.factorial : ℝ)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    rw [hy]
    push_cast
    ring
  have hx6 : (0 : ℝ) ≤ x ^ 6 := by positivity
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [e, abs_mul, abs_of_nonneg hx6]
  calc x ^ 6 * |locWeight g x₀ x - ∑ m ∈ Finset.range 2, y ^ m / (m.factorial : ℝ)|
      ≤ x ^ 6 * (C * (2 ^ 2 * (|g * x₀| ^ 2 * |x| ^ 2 + |g / 2| ^ 2 * (x ^ 2) ^ 2))) :=
        mul_le_mul_of_nonneg_left (hT.trans (mul_le_mul_of_nonneg_left hy2 hC0)) hx6
    _ = locS₈ g x₀ * x ^ 8 + locS₁₀ g x₀ * x ^ 10 := by
        rw [hC]
        unfold locS₈ locS₁₀
        rw [← hx2]
        ring

end Weight

/-! ### Expectation-level expansions -/

section Expansions

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

theorem locQuartic_expansion4 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 4 * locWeight g x₀ x) -
      (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locP₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 7))| ≤
      locH₆ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) +
        locH₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 10) +
        locH₁₀ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 12) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 4
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht
  have hP : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 4 + g * x₀ * x ^ 5 + locP₃ g x₀ * x ^ 6 + locP₄ g x₀ * x ^ 7) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locP₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 7) := by
    have e : (fun x : ℝ => x ^ 4 + g * x₀ * x ^ 5 + locP₃ g x₀ * x ^ 6 + locP₄ g x₀ * x ^ 7) =
        fun x => 1 * x ^ 4 + g * x₀ * x ^ 5 + locP₃ g x₀ * x ^ 6 + locP₄ g x₀ * x ^ 7 := by
      funext x; ring
    rw [e, gibbs_lin4 (hp 4) (hp 5) (hp 6) (hp 7)]
    ring
  have hPint : Integrable (fun x => (x ^ 4 + g * x₀ * x ^ 5 + locP₃ g x₀ * x ^ 6 +
      locP₄ g x₀ * x ^ 7) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (((hp 4).add ((hp 5).const_mul (g * x₀))).add ((hp 6).const_mul (locP₃ g x₀))).add
      ((hp 7).const_mul (locP₄ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hF : Integrable (fun x => (x ^ 4 * locWeight g x₀ x - (x ^ 4 + g * x₀ * x ^ 5 +
      locP₃ g x₀ * x ^ 6 + locP₄ g x₀ * x ^ 7)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hf.sub hPint).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locH₆ g x₀ * x ^ 8 + locH₈ g x₀ * x ^ 10 +
      locH₁₀ g x₀ * x ^ 12) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (((hp 8).const_mul (locH₆ g x₀)).add ((hp 10).const_mul (locH₈ g x₀))).add
      ((hp 12).const_mul (locH₁₀ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← hP, ← gibbs_sub' hf hPint, ← gibbs_lin3 (hp 8) (hp 10) (hp 12)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x =>
      locQuartic_pointwise4 hg x)

theorem locFifth_expansion4 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 5 * locWeight g x₀ x) -
      (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 7) +
        locP₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8))| ≤
      locU₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) +
        locU₁₀ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 10) +
        locU₁₂ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 12) +
        locU₁₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 14) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 5
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht
  have hP : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 5 + g * x₀ * x ^ 6 + locP₃ g x₀ * x ^ 7 + locP₄ g x₀ * x ^ 8) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 7) +
        locP₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) := by
    have e : (fun x : ℝ => x ^ 5 + g * x₀ * x ^ 6 + locP₃ g x₀ * x ^ 7 + locP₄ g x₀ * x ^ 8) =
        fun x => 1 * x ^ 5 + g * x₀ * x ^ 6 + locP₃ g x₀ * x ^ 7 + locP₄ g x₀ * x ^ 8 := by
      funext x; ring
    rw [e, gibbs_lin4 (hp 5) (hp 6) (hp 7) (hp 8)]
    ring
  have hPint : Integrable (fun x => (x ^ 5 + g * x₀ * x ^ 6 + locP₃ g x₀ * x ^ 7 +
      locP₄ g x₀ * x ^ 8) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (((hp 5).add ((hp 6).const_mul (g * x₀))).add ((hp 7).const_mul (locP₃ g x₀))).add
      ((hp 8).const_mul (locP₄ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hF : Integrable (fun x => (x ^ 5 * locWeight g x₀ x - (x ^ 5 + g * x₀ * x ^ 6 +
      locP₃ g x₀ * x ^ 7 + locP₄ g x₀ * x ^ 8)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hf.sub hPint).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locU₈ g x₀ * x ^ 8 + locU₁₀ g x₀ * x ^ 10 +
      locU₁₂ g x₀ * x ^ 12 + locU₁₄ g x₀ * x ^ 14) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((((hp 8).const_mul (locU₈ g x₀)).add ((hp 10).const_mul (locU₁₀ g x₀))).add
      ((hp 12).const_mul (locU₁₂ g x₀))).add ((hp 14).const_mul (locU₁₄ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← hP, ← gibbs_sub' hf hPint, ← gibbs_lin4 (hp 8) (hp 10) (hp 12) (hp 14)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x =>
      locFifth_pointwise4 hg x)

theorem locSixth_expansion (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 6 * locWeight g x₀ x) -
      (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 6) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 7) -
        g / 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8))| ≤
      locS₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) +
        locS₁₀ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 10) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 6
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht
  have hP : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 6 + g * x₀ * x ^ 7 - g / 2 * x ^ 8) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 6) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 7) -
        g / 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) := by
    have e : (fun x : ℝ => x ^ 6 + g * x₀ * x ^ 7 - g / 2 * x ^ 8) =
        fun x => 1 * x ^ 6 + g * x₀ * x ^ 7 + (-(g / 2)) * x ^ 8 := by
      funext x; ring
    rw [e, gibbs_lin3 (hp 6) (hp 7) (hp 8)]
    ring
  have hPint : Integrable (fun x => (x ^ 6 + g * x₀ * x ^ 7 - g / 2 * x ^ 8) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((hp 6).add ((hp 7).const_mul (g * x₀))).sub ((hp 8).const_mul (g / 2))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hF : Integrable (fun x => (x ^ 6 * locWeight g x₀ x - (x ^ 6 + g * x₀ * x ^ 7 -
      g / 2 * x ^ 8)) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hf.sub hPint).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locS₈ g x₀ * x ^ 8 + locS₁₀ g x₀ * x ^ 10) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((hp 8).const_mul (locS₈ g x₀)).add ((hp 10).const_mul (locS₁₀ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← hP, ← gibbs_sub' hf hPint, ← gibbsExpectation_lin (hp 8) (hp 10)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x =>
      locSixth_pointwise hg x)

end Expansions

/-! ### Coefficients and abstract assemblies -/

section Coeffs

/-- `n₄ = C₄ + a c₅ + 15p₃/λ³`: the `1/t` coefficient of `t²⟨x⁴φ⟩`. -/
noncomputable def locN4 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) +
    g * x₀ * (-(35 * alpha / (2 * lam ^ 4))) + 15 * locP₃ g x₀ / lam ^ 3

/-- `c₄' = n₄ − 3d₁/λ²`: the `1/t` coefficient of `t²⟨x⁴⟩_loc`. -/
noncomputable def locFourthCoeff2 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  locN4 lam alpha gamma g x₀ - 3 * locD1 lam alpha g x₀ / lam ^ 2

theorem locFourthCoeff2_eq (lam alpha gamma g x₀ : ℝ) (hlam : 0 < lam) :
    locFourthCoeff2 lam alpha gamma g x₀ =
      (25 * alpha ^ 2 - 32 * g * x₀ * alpha * lam + 12 * (g * x₀) ^ 2 * lam ^ 2 - 12 * g * lam ^ 2 -
        8 * gamma * lam) / (2 * lam ^ 5) := by
  unfold locFourthCoeff2 locN4 locD1 locP₃
  field_simp
  ring

/-- The leading coefficient of `t³⟨x⁵⟩_loc`: `c₅ + 15a/λ³`. -/
noncomputable def locFifthCoeff (lam alpha g x₀ : ℝ) : ℝ :=
  -(35 * alpha / (2 * lam ^ 4)) + 15 * (g * x₀) / lam ^ 3

/-- The assembly of the weighted fourth moment (abstract reals). -/
theorem locQuartic4_assembly (lam alpha gamma g x₀ t N M₄ M₅ M₆ M₇ K₄ K₅ K₆ K₇' KR : ℝ)
    (hlam : 0 < lam) (ht1 : 1 ≤ t)
    (e₄ : |t ^ 2 * M₄ - 3 / lam ^ 2 - (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t| ≤
      K₄ / t ^ 2)
    (e₅ : |t ^ 3 * M₅ - -(35 * alpha / (2 * lam ^ 4))| ≤ K₅ / t)
    (e₆ : |t ^ 3 * M₆ - 15 / lam ^ 3| ≤ K₆ / t)
    (e₇ : |t ^ 4 * M₇| ≤ K₇')
    (hR : |N - (M₄ + g * x₀ * M₅ + locP₃ g x₀ * M₆ + locP₄ g x₀ * M₇)| ≤ KR / t ^ 4) :
    |t ^ 2 * N - 3 / lam ^ 2 - locN4 lam alpha gamma g x₀ / t| ≤
      (K₄ + |g * x₀| * K₅ + |locP₃ g x₀| * K₆ + |locP₄ g x₀| * K₇' + KR) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have key : t ^ 2 * N - 3 / lam ^ 2 - locN4 lam alpha gamma g x₀ / t =
      (t ^ 2 * M₄ - 3 / lam ^ 2 - (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t) +
        g * x₀ * ((t ^ 3 * M₅ - -(35 * alpha / (2 * lam ^ 4))) / t) +
        locP₃ g x₀ * ((t ^ 3 * M₆ - 15 / lam ^ 3) / t) +
        locP₄ g x₀ * (t ^ 4 * M₇ / t ^ 2) +
        t ^ 2 * (N - (M₄ + g * x₀ * M₅ + locP₃ g x₀ * M₆ + locP₄ g x₀ * M₇)) := by
    unfold locN4
    field_simp
    ring
  rw [key]
  have b₅ : |g * x₀ * ((t ^ 3 * M₅ - -(35 * alpha / (2 * lam ^ 4))) / t)| ≤
      |g * x₀| * (K₅ / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ K₅ / t / t := div_le_div_of_nonneg_right e₅ ht0.le
      _ = K₅ / t ^ 2 := by ring
  have b₆ : |locP₃ g x₀ * ((t ^ 3 * M₆ - 15 / lam ^ 3) / t)| ≤ |locP₃ g x₀| * (K₆ / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ K₆ / t / t := div_le_div_of_nonneg_right e₆ ht0.le
      _ = K₆ / t ^ 2 := by ring
  have b₇ : |locP₄ g x₀ * (t ^ 4 * M₇ / t ^ 2)| ≤ |locP₄ g x₀| * (K₇' / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₇ (by positivity)) (abs_nonneg _)
  have bR : |t ^ 2 * (N - (M₄ + g * x₀ * M₅ + locP₃ g x₀ * M₆ + locP₄ g x₀ * M₇))| ≤
      KR / t ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    calc t ^ 2 * |N - (M₄ + g * x₀ * M₅ + locP₃ g x₀ * M₆ + locP₄ g x₀ * M₇)|
        ≤ t ^ 2 * (KR / t ^ 4) := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = KR / t ^ 2 := by field_simp
  calc _ ≤ K₄ / t ^ 2 + |g * x₀| * (K₅ / t ^ 2) + |locP₃ g x₀| * (K₆ / t ^ 2) +
        |locP₄ g x₀| * (K₇' / t ^ 2) + KR / t ^ 2 := by
        refine (abs_add_le _ _).trans (add_le_add ?_ bR)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₇)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₆)
        exact (abs_add_le _ _).trans (add_le_add e₄ b₅)
    _ = _ := by ring

/-- The assembly of the weighted fifth moment at leading order (abstract reals). -/
theorem locFifth_lead_assembly (lam alpha g x₀ t N M₅ M₆ M₇ M₈ K₅ K₆ K₇' K₈' KR : ℝ) (ht1 : 1 ≤ t)
    (e₅ : |t ^ 3 * M₅ - -(35 * alpha / (2 * lam ^ 4))| ≤ K₅ / t)
    (e₆ : |t ^ 3 * M₆ - 15 / lam ^ 3| ≤ K₆ / t) (e₇ : |t ^ 4 * M₇| ≤ K₇') (e₈ : |t ^ 4 * M₈| ≤ K₈')
    (hR : |N - (M₅ + g * x₀ * M₆ + locP₃ g x₀ * M₇ + locP₄ g x₀ * M₈)| ≤ KR / t ^ 4) :
    |t ^ 3 * N - locFifthCoeff lam alpha g x₀| ≤
      (K₅ + |g * x₀| * K₆ + |locP₃ g x₀| * K₇' + |locP₄ g x₀| * K₈' + KR) / t := by
  have ht0 : 0 < t := by linarith
  have key : t ^ 3 * N - locFifthCoeff lam alpha g x₀ =
      (t ^ 3 * M₅ - -(35 * alpha / (2 * lam ^ 4))) + g * x₀ * (t ^ 3 * M₆ - 15 / lam ^ 3) +
        locP₃ g x₀ * (t ^ 3 * M₇) + locP₄ g x₀ * (t ^ 3 * M₈) +
        t ^ 3 * (N - (M₅ + g * x₀ * M₆ + locP₃ g x₀ * M₇ + locP₄ g x₀ * M₈)) := by
    unfold locFifthCoeff
    ring
  rw [key]
  have b₆ : |g * x₀ * (t ^ 3 * M₆ - 15 / lam ^ 3)| ≤ |g * x₀| * (K₆ / t) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e₆ (abs_nonneg _)
  have b₇ : |locP₃ g x₀ * (t ^ 3 * M₇)| ≤ |locP₃ g x₀| * (K₇' / t) := by
    have e : t ^ 3 * M₇ = t ^ 4 * M₇ / t := by
      rw [eq_div_iff ht0.ne']
      ring
    rw [e, abs_mul, abs_div, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₇ ht0.le) (abs_nonneg _)
  have b₈ : |locP₄ g x₀ * (t ^ 3 * M₈)| ≤ |locP₄ g x₀| * (K₈' / t) := by
    have e : t ^ 3 * M₈ = t ^ 4 * M₈ / t := by
      rw [eq_div_iff ht0.ne']
      ring
    rw [e, abs_mul, abs_div, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₈ ht0.le) (abs_nonneg _)
  have bR : |t ^ 3 * (N - (M₅ + g * x₀ * M₆ + locP₃ g x₀ * M₇ + locP₄ g x₀ * M₈))| ≤ KR / t := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 3)]
    calc t ^ 3 * |N - (M₅ + g * x₀ * M₆ + locP₃ g x₀ * M₇ + locP₄ g x₀ * M₈)| ≤
          t ^ 3 * (KR / t ^ 4) := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = KR / t := by field_simp
  calc _ ≤ K₅ / t + |g * x₀| * (K₆ / t) + |locP₃ g x₀| * (K₇' / t) + |locP₄ g x₀| * (K₈' / t) +
        KR / t := by
        refine (abs_add_le _ _).trans (add_le_add ?_ bR)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₈)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₇)
        exact (abs_add_le _ _).trans (add_le_add e₅ b₆)
    _ = _ := by ring

/-- The assembly of the weighted sixth moment at leading order (abstract reals). -/
theorem locSixth_lead_assembly (lam g x₀ t N M₆ M₇ M₈ K₆ K₇' K₈' KR : ℝ) (ht1 : 1 ≤ t)
    (e₆ : |t ^ 3 * M₆ - 15 / lam ^ 3| ≤ K₆ / t) (e₇ : |t ^ 4 * M₇| ≤ K₇') (e₈ : |t ^ 4 * M₈| ≤ K₈')
    (hR : |N - (M₆ + g * x₀ * M₇ - g / 2 * M₈)| ≤ KR / t ^ 4) :
    |t ^ 3 * N - 15 / lam ^ 3| ≤ (K₆ + |g * x₀| * K₇' + |g / 2| * K₈' + KR) / t := by
  have ht0 : 0 < t := by linarith
  have key : t ^ 3 * N - 15 / lam ^ 3 =
      (t ^ 3 * M₆ - 15 / lam ^ 3) + g * x₀ * (t ^ 4 * M₇ / t) - g / 2 * (t ^ 4 * M₈ / t) +
        t ^ 3 * (N - (M₆ + g * x₀ * M₇ - g / 2 * M₈)) := by
    field_simp
    ring
  rw [key]
  have b₇ : |g * x₀ * (t ^ 4 * M₇ / t)| ≤ |g * x₀| * (K₇' / t) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₇ ht0.le) (abs_nonneg _)
  have b₈ : |g / 2 * (t ^ 4 * M₈ / t)| ≤ |g / 2| * (K₈' / t) := by
    rw [abs_mul, abs_div (t ^ 4 * M₈), abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₈ ht0.le) (abs_nonneg _)
  have bR : |t ^ 3 * (N - (M₆ + g * x₀ * M₇ - g / 2 * M₈))| ≤ KR / t := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 3)]
    calc t ^ 3 * |N - (M₆ + g * x₀ * M₇ - g / 2 * M₈)| ≤ t ^ 3 * (KR / t ^ 4) :=
          mul_le_mul_of_nonneg_left hR (by positivity)
      _ = KR / t := by field_simp
  calc _ ≤ K₆ / t + |g * x₀| * (K₇' / t) + |g / 2| * (K₈' / t) + KR / t := by
        refine (abs_add_le _ _).trans (add_le_add ?_ bR)
        refine (abs_sub _ _).trans (add_le_add ?_ b₈)
        exact (abs_add_le _ _).trans (add_le_add e₆ b₇)
    _ = _ := by ring

/-- The `t²`-scaled cross-multiplied ratio identity (as `ratio_key`, one power of `t` up). -/
theorem ratio_key2 (t N D c c' d₁ n₁ : ℝ) (hn : n₁ = c' + c * d₁) (ht : t ≠ 0) (hD : D ≠ 0) :
    t ^ 2 * (N / D) - c - c' / t =
      ((t ^ 2 * N - c - n₁ / t) - c * (D - 1 - d₁ / t) - c' * d₁ / t ^ 2 -
        c' / t * (D - 1 - d₁ / t)) / D := by
  rw [hn]
  field_simp
  ring

/-- Dividing a `t³`-scaled leading rate by `D = 1 + O(1/t)`:
`t³(N/D) − c = ((t³N − c) − c(D − 1))/D`. -/
theorem ratio_lead3_key (t N D c : ℝ) (hD : D ≠ 0) :
    t ^ 3 * (N / D) - c = ((t ^ 3 * N - c) - c * (D - 1)) / D := by
  field_simp
  ring

end Coeffs

/-! ### The localised moments -/

section Rates

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `|t⁴⟨x⁷⟩| ≤ K` (the signed seventh moment is `O(t⁻⁴)`). -/
theorem seventhMoment_bound :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 7)| ≤ K := by
  obtain ⟨K, T, hK, hT, h⟩ := Laplace.OneD.oddMoment_anharmonic_rate hlam hgamma hdisc 3
  refine ⟨|alpha * ((9 : ℕ)‼ : ℝ) / (6 * lam ^ 5)| + K, T, by positivity, hT, fun {t} ht => ?_⟩
  have h' := h ht
  simp only [show (3 + 1 : ℕ) = 4 from rfl, show (2 * 3 + 1 : ℕ) = 7 from rfl,
    show (2 * 3 + 3 : ℕ) = 9 from rfl, show (3 + 2 : ℕ) = 5 from rfl] at h'
  have ht1 : 1 ≤ t := hT.trans ht
  have := Laplace.OneD.rate_bounded ht1 hK (by rw [sub_neg_eq_add]; exact h')
  rw [abs_neg] at this
  exact this

/-- `|t⁴⟨x⁸⟩| ≤ K`. -/
theorem eighthMoment_bound :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 8)| ≤ K := by
  obtain ⟨C, T, hC, hT, h⟩ := evenMoment_bound hlam hgamma hdisc 4
  simp only [show (2 * 4 : ℕ) = 8 from rfl] at h
  refine ⟨C, T, hC, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hZ := partition_pos' hlam hgamma hdisc ht0
  have hM0 : 0 ≤ _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 8) := by
    have := abs_gibbsExpectation_le' hZ (fun x : ℝ => x ^ 8)
    have e : (fun x : ℝ => |x ^ 8|) = fun x => x ^ 8 := by
      funext x
      exact abs_of_nonneg (by positivity)
    rw [e] at this
    exact (abs_nonneg _).trans this
  rw [abs_of_nonneg (by positivity)]
  calc t ^ 4 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 8) ≤ t ^ 4 * (C / t ^ 4) := by gcongr; exact h ht
    _ = C := by field_simp

/-- **The weighted fourth moment to second order**: `|t²⟨x⁴φ⟩ − 3/λ² − n₄/t| ≤ K/t²`. -/
theorem locQuartic_rate4 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4 * locWeight g x₀ x) - 3 / lam ^ 2 -
        locN4 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_order2_rate hlam hgamma hdisc
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := sixthMoment_lead hlam hgamma hdisc
  obtain ⟨K₇, T₇, hK₇, hT₇, h₇⟩ := seventhMoment_bound hlam hgamma hdisc
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  obtain ⟨C₁₀, T₁₀, hC₁₀, hT₁₀, h₁₀⟩ := evenMoment_bound hlam hgamma hdisc 5
  obtain ⟨C₁₂, T₁₂, hC₁₂, hT₁₂, h₁₂⟩ := evenMoment_bound hlam hgamma hdisc 6
  simp only [show (2 * 4 : ℕ) = 8 from rfl, show (2 * 5 : ℕ) = 10 from rfl,
    show (2 * 6 : ℕ) = 12 from rfl] at h₈ h₁₀ h₁₂
  have hH₆ := locH₆_nonneg g x₀
  have hH₈ := locH₈_nonneg g x₀
  have hH₁₀ := locH₁₀_nonneg g x₀
  have hKR0 : 0 ≤ locH₆ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂ := by positivity
  have h1T : (1 : ℝ) ≤ T₄ + T₅ + T₆ + T₇ + T₈ + T₁₀ + T₁₂ := by linarith
  refine ⟨K₄ + |g * x₀| * K₅ + |locP₃ g x₀| * K₆ + |locP₄ g x₀| * K₇ +
      (locH₆ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂),
    T₄ + T₅ + T₆ + T₇ + T₈ + T₁₀ + T₁₂, by positivity, h1T, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hR := (locQuartic_expansion4 hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h₈ (t := t) (by linarith)) hH₆)
      (mul_le_mul_of_nonneg_left (h₁₀ (t := t) (by linarith)) hH₈))
      (mul_le_mul_of_nonneg_left (h₁₂ (t := t) (by linarith)) hH₁₀))
  have hRt : locH₆ g x₀ * (C₈ / t ^ 4) + locH₈ g x₀ * (C₁₀ / t ^ 5) +
      locH₁₀ g x₀ * (C₁₂ / t ^ 6) ≤
      (locH₆ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂) / t ^ 4 := by
    have h10 : locH₈ g x₀ * (C₁₀ / t ^ 5) ≤ locH₈ g x₀ * (C₁₀ / t ^ 4) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₀ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hH₈
    have h12 : locH₁₀ g x₀ * (C₁₂ / t ^ 6) ≤ locH₁₀ g x₀ * (C₁₂ / t ^ 4) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₂ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hH₁₀
    have e : (locH₆ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂) / t ^ 4 =
        locH₆ g x₀ * (C₈ / t ^ 4) + locH₈ g x₀ * (C₁₀ / t ^ 4) + locH₁₀ g x₀ * (C₁₂ / t ^ 4) := by
      ring
    rw [e]
    linarith
  exact locQuartic4_assembly lam alpha gamma g x₀ t
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 4 * locWeight g x₀ x))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 6))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 7))
    K₄ K₅ K₆ K₇ (locH₆ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂) hlam ht1
    (h₄ (t := t) (by linarith)) (h₅ (t := t) (by linarith)) (h₆ (t := t) (by linarith))
    (h₇ (t := t) (by linarith)) (hR.trans hRt)

/-- **The weighted fifth moment at leading order**: `|t³⟨x⁵φ⟩ − (c₅ + 15a/λ³)| ≤ K/t`. -/
theorem locFifth_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5 * locWeight g x₀ x) - locFifthCoeff lam alpha g x₀| ≤ K / t := by
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := sixthMoment_lead hlam hgamma hdisc
  obtain ⟨K₇, T₇, hK₇, hT₇, h₇⟩ := seventhMoment_bound hlam hgamma hdisc
  obtain ⟨K₈, T₈, hK₈, hT₈, h₈⟩ := eighthMoment_bound hlam hgamma hdisc
  obtain ⟨C₈, T₈', hC₈, hT₈', h₈'⟩ := evenMoment_bound hlam hgamma hdisc 4
  obtain ⟨C₁₀, T₁₀, hC₁₀, hT₁₀, h₁₀⟩ := evenMoment_bound hlam hgamma hdisc 5
  obtain ⟨C₁₂, T₁₂, hC₁₂, hT₁₂, h₁₂⟩ := evenMoment_bound hlam hgamma hdisc 6
  obtain ⟨C₁₄, T₁₄, hC₁₄, hT₁₄, h₁₄⟩ := evenMoment_bound hlam hgamma hdisc 7
  simp only [show (2 * 4 : ℕ) = 8 from rfl, show (2 * 5 : ℕ) = 10 from rfl,
    show (2 * 6 : ℕ) = 12 from rfl, show (2 * 7 : ℕ) = 14 from rfl] at h₈' h₁₀ h₁₂ h₁₄
  have hU₈ := locU₈_nonneg g x₀
  have hU₁₀ := locU₁₀_nonneg g x₀
  have hU₁₂ := locU₁₂_nonneg g x₀
  have hU₁₄ := locU₁₄_nonneg g x₀
  have hKR0 : 0 ≤ locU₈ g x₀ * C₈ + locU₁₀ g x₀ * C₁₀ + locU₁₂ g x₀ * C₁₂ + locU₁₄ g x₀ * C₁₄ := by
    positivity
  have h1T : (1 : ℝ) ≤ T₅ + T₆ + T₇ + T₈ + T₈' + T₁₀ + T₁₂ + T₁₄ := by linarith
  refine ⟨K₅ + |g * x₀| * K₆ + |locP₃ g x₀| * K₇ + |locP₄ g x₀| * K₈ +
      (locU₈ g x₀ * C₈ + locU₁₀ g x₀ * C₁₀ + locU₁₂ g x₀ * C₁₂ + locU₁₄ g x₀ * C₁₄),
    T₅ + T₆ + T₇ + T₈ + T₈' + T₁₀ + T₁₂ + T₁₄, by positivity, h1T, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hR := (locFifth_expansion4 hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h₈' (t := t) (by linarith)) hU₈)
      (mul_le_mul_of_nonneg_left (h₁₀ (t := t) (by linarith)) hU₁₀))
      (mul_le_mul_of_nonneg_left (h₁₂ (t := t) (by linarith)) hU₁₂))
      (mul_le_mul_of_nonneg_left (h₁₄ (t := t) (by linarith)) hU₁₄))
  have hRt : locU₈ g x₀ * (C₈ / t ^ 4) + locU₁₀ g x₀ * (C₁₀ / t ^ 5) +
      locU₁₂ g x₀ * (C₁₂ / t ^ 6) + locU₁₄ g x₀ * (C₁₄ / t ^ 7) ≤
      (locU₈ g x₀ * C₈ + locU₁₀ g x₀ * C₁₀ + locU₁₂ g x₀ * C₁₂ + locU₁₄ g x₀ * C₁₄) / t ^ 4 := by
    have h10 : locU₁₀ g x₀ * (C₁₀ / t ^ 5) ≤ locU₁₀ g x₀ * (C₁₀ / t ^ 4) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₀ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hU₁₀
    have h12 : locU₁₂ g x₀ * (C₁₂ / t ^ 6) ≤ locU₁₂ g x₀ * (C₁₂ / t ^ 4) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₂ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hU₁₂
    have h14 : locU₁₄ g x₀ * (C₁₄ / t ^ 7) ≤ locU₁₄ g x₀ * (C₁₄ / t ^ 4) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₄ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hU₁₄
    have e : (locU₈ g x₀ * C₈ + locU₁₀ g x₀ * C₁₀ + locU₁₂ g x₀ * C₁₂ + locU₁₄ g x₀ * C₁₄) / t ^ 4 =
        locU₈ g x₀ * (C₈ / t ^ 4) + locU₁₀ g x₀ * (C₁₀ / t ^ 4) + locU₁₂ g x₀ * (C₁₂ / t ^ 4) +
          locU₁₄ g x₀ * (C₁₄ / t ^ 4) := by ring
    rw [e]
    linarith
  exact locFifth_lead_assembly lam alpha g x₀ t
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 5 * locWeight g x₀ x))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 6))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 7))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 8))
    K₅ K₆ K₇ K₈ (locU₈ g x₀ * C₈ + locU₁₀ g x₀ * C₁₀ + locU₁₂ g x₀ * C₁₂ + locU₁₄ g x₀ * C₁₄) ht1
    (h₅ (t := t) (by linarith)) (h₆ (t := t) (by linarith)) (h₇ (t := t) (by linarith))
    (h₈ (t := t) (by linarith)) (hR.trans hRt)

/-- **The weighted sixth moment at leading order**: `|t³⟨x⁶φ⟩ − 15/λ³| ≤ K/t`. -/
theorem locSixth_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6 * locWeight g x₀ x) - 15 / lam ^ 3| ≤ K / t := by
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := sixthMoment_lead hlam hgamma hdisc
  obtain ⟨K₇, T₇, hK₇, hT₇, h₇⟩ := seventhMoment_bound hlam hgamma hdisc
  obtain ⟨K₈, T₈, hK₈, hT₈, h₈⟩ := eighthMoment_bound hlam hgamma hdisc
  obtain ⟨C₈, T₈', hC₈, hT₈', h₈'⟩ := evenMoment_bound hlam hgamma hdisc 4
  obtain ⟨C₁₀, T₁₀, hC₁₀, hT₁₀, h₁₀⟩ := evenMoment_bound hlam hgamma hdisc 5
  simp only [show (2 * 4 : ℕ) = 8 from rfl, show (2 * 5 : ℕ) = 10 from rfl] at h₈' h₁₀
  have hS₈ := locS₈_nonneg g x₀
  have hS₁₀ := locS₁₀_nonneg g x₀
  have h1T : (1 : ℝ) ≤ T₆ + T₇ + T₈ + T₈' + T₁₀ := by linarith
  refine ⟨K₆ + |g * x₀| * K₇ + |g / 2| * K₈ + (locS₈ g x₀ * C₈ + locS₁₀ g x₀ * C₁₀),
    T₆ + T₇ + T₈ + T₈' + T₁₀, by positivity, h1T, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hR := (locSixth_expansion hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (mul_le_mul_of_nonneg_left (h₈' (t := t) (by linarith)) hS₈)
      (mul_le_mul_of_nonneg_left (h₁₀ (t := t) (by linarith)) hS₁₀))
  have hRt : locS₈ g x₀ * (C₈ / t ^ 4) + locS₁₀ g x₀ * (C₁₀ / t ^ 5) ≤
      (locS₈ g x₀ * C₈ + locS₁₀ g x₀ * C₁₀) / t ^ 4 := by
    have h10 : locS₁₀ g x₀ * (C₁₀ / t ^ 5) ≤ locS₁₀ g x₀ * (C₁₀ / t ^ 4) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₀ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hS₁₀
    have e : (locS₈ g x₀ * C₈ + locS₁₀ g x₀ * C₁₀) / t ^ 4 =
        locS₈ g x₀ * (C₈ / t ^ 4) + locS₁₀ g x₀ * (C₁₀ / t ^ 4) := by ring
    rw [e]
    linarith
  exact locSixth_lead_assembly lam g x₀ t
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 6 * locWeight g x₀ x))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 6))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 7))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 8))
    K₆ K₇ K₈ (locS₈ g x₀ * C₈ + locS₁₀ g x₀ * C₁₀) ht1 (h₆ (t := t) (by linarith))
    (h₇ (t := t) (by linarith)) (h₈ (t := t) (by linarith)) (hR.trans hRt)

/-- Dividing a `t³`-scaled leading rate by the denominator (`|D − 1| ≤ KD/t`, `D ≥ ½`). -/
theorem loc_ratio_lead3_rate (c : ℝ) (f : ℝ → ℝ) (hg : 0 ≤ g)
    (hN : ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => f x * locWeight g x₀ x) - c| ≤ K / t) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t f - c| ≤
        K / t := by
  obtain ⟨KN, TN, hKN, hTN, hN⟩ := hN
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨2 * (KN + |c| * KD), TN + TD + 2 * KD, by positivity, by linarith, fun {t} ht => ?_⟩
  have hTNt : TN ≤ t := by linarith
  have hTDt : TD ≤ t := by linarith
  have h2K : 2 * KD ≤ t := by linarith
  have ht1 : 1 ≤ t := hTN.trans hTNt
  have ht0 : 0 < t := by linarith
  rw [gibbsExpectation_locPotential1 hlam hgamma hdisc ht0]
  have eN := hN hTNt
  have eD := hD hTDt
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => f x * locWeight g x₀ x) with hNdef
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
  have hDhalf : 1 / 2 ≤ D := by
    have h1 : KD / t ≤ 1 / 2 := by rw [div_le_iff₀ ht0]; linarith
    have h2 := (abs_le.mp (eD.trans h1)).1
    linarith
  have hD0 : 0 < D := by linarith
  rw [ratio_lead3_key t N D c hD0.ne', abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  calc |(t ^ 3 * N - c) - c * (D - 1)| ≤ |t ^ 3 * N - c| + |c * (D - 1)| := abs_sub _ _
    _ ≤ KN / t + |c| * (KD / t) := by
        rw [abs_mul]
        gcongr
    _ = 2 * (KN + |c| * KD) / t * (1 / 2) := by ring
    _ ≤ 2 * (KN + |c| * KD) / t * D := by gcongr

/-- **The localised fourth moment to second order**: `|t²⟨x⁴⟩_loc − 3/λ² − c₄'/t| ≤ K/t²`. -/
theorem locFourthMoment_loc_rate4 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 4) - 3 / lam ^ 2 - locFourthCoeff2 lam alpha gamma g x₀ / t| ≤
        K / t ^ 2 := by
  obtain ⟨KN, TN, hKN, hTN, hN⟩ := locQuartic_rate4 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  have hn₁e : locN4 lam alpha gamma g x₀ =
      locFourthCoeff2 lam alpha gamma g x₀ + 3 / lam ^ 2 * locD1 lam alpha g x₀ := by
    unfold locFourthCoeff2
    ring
  have hd₁0 : 0 ≤ |locD1 lam alpha g x₀| := abs_nonneg _
  have hc0 : 0 ≤ |3 / lam ^ 2| := abs_nonneg _
  have hc'0 : 0 ≤ |locFourthCoeff2 lam alpha gamma g x₀| := abs_nonneg _
  have h1T : (1 : ℝ) ≤ TN + TD + 2 * (|locD1 lam alpha g x₀| + KD) := by linarith
  refine ⟨2 * (KN + |3 / lam ^ 2| * KD + |locFourthCoeff2 lam alpha gamma g x₀| *
      |locD1 lam alpha g x₀| + |locFourthCoeff2 lam alpha gamma g x₀| * KD),
    TN + TD + 2 * (|locD1 lam alpha g x₀| + KD), by positivity, h1T, fun {t} ht => ?_⟩
  have hTNt : TN ≤ t := by linarith
  have hTDt : TD ≤ t := by linarith
  have h2 : 2 * (|locD1 lam alpha g x₀| + KD) ≤ t := by linarith
  have ht1 : 1 ≤ t := hTN.trans hTNt
  have ht0 : 0 < t := by linarith
  rw [gibbsExpectation_locPotential1 hlam hgamma hdisc ht0]
  have eN := hN hTNt
  have eD := hD hTDt
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4 * locWeight g x₀ x) with hNdef
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
  set c : ℝ := 3 / lam ^ 2 with hc
  set c' := locFourthCoeff2 lam alpha gamma g x₀ with hc'
  set d₁ := locD1 lam alpha g x₀ with hd₁
  set n₁ := locN4 lam alpha gamma g x₀ with hn₁
  have hDhalf : 1 / 2 ≤ D := by
    have h1 : |D - 1| ≤ (|d₁| + KD) / t := by
      calc |D - 1| = |(D - 1 - d₁ / t) + d₁ / t| := by ring_nf
        _ ≤ |D - 1 - d₁ / t| + |d₁ / t| := abs_add_le _ _
        _ ≤ KD / t ^ 2 + |d₁| / t := by
            gcongr
            rw [abs_div, abs_of_pos ht0]
        _ ≤ KD / t + |d₁| / t := by
            gcongr
            nlinarith
        _ = (|d₁| + KD) / t := by ring
    have h3 : (|d₁| + KD) / t ≤ 1 / 2 := by
      rw [div_le_iff₀ ht0]
      linarith [h2]
    have h4 := (abs_le.mp (h1.trans h3)).1
    linarith
  have hD0 : 0 < D := by linarith
  rw [ratio_key2 t N D c c' d₁ n₁ hn₁e ht0.ne' hD0.ne', abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  have h3 : |c' * d₁ / t ^ 2| = |c'| * |d₁| / t ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  have h4 : |c' / t * (D - 1 - d₁ / t)| ≤ |c'| * KD / t ^ 2 := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    calc |c'| / t * |D - 1 - d₁ / t| ≤ |c'| / t * (KD / t ^ 2) := by gcongr
      _ = (|c'| * KD / t ^ 2) / t := by ring
      _ ≤ |c'| * KD / t ^ 2 := div_le_self (by positivity) ht1
  calc |(t ^ 2 * N - c - n₁ / t) - c * (D - 1 - d₁ / t) - c' * d₁ / t ^ 2 -
        c' / t * (D - 1 - d₁ / t)|
      ≤ |t ^ 2 * N - c - n₁ / t| + |c * (D - 1 - d₁ / t)| + |c' * d₁ / t ^ 2| +
        |c' / t * (D - 1 - d₁ / t)| := by
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          exact abs_sub _ _
    _ ≤ KN / t ^ 2 + |c| * (KD / t ^ 2) + |c'| * |d₁| / t ^ 2 + |c'| * KD / t ^ 2 := by
          rw [abs_mul c, h3]
          gcongr
    _ = (KN + |c| * KD + |c'| * |d₁| + |c'| * KD) / t ^ 2 := by ring
    _ = 2 * (KN + |c| * KD + |c'| * |d₁| + |c'| * KD) / t ^ 2 * (1 / 2) := by ring
    _ ≤ 2 * (KN + |c| * KD + |c'| * |d₁| + |c'| * KD) / t ^ 2 * D := by gcongr

/-- `|t³⟨x⁵⟩_loc − (c₅ + 15a/λ³)| ≤ K/t`. -/
theorem locFifthMoment_loc_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 5) - locFifthCoeff lam alpha g x₀| ≤ K / t :=
  loc_ratio_lead3_rate hlam hgamma hdisc _ (fun x => x ^ 5) hg
    (locFifth_rate hlam hgamma hdisc hg (x₀ := x₀))

/-- `|t³⟨x⁶⟩_loc − 15/λ³| ≤ K/t`. -/
theorem locSixthMoment_loc_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 6) - 15 / lam ^ 3| ≤ K / t :=
  loc_ratio_lead3_rate hlam hgamma hdisc _ (fun x => x ^ 6) hg
    (locSixth_rate hlam hgamma hdisc hg (x₀ := x₀))

end Rates

/-! ### eq:covK on the localised measure to second order -/

section CovKCoeffs

/-- The `1/t` coefficient of `t²Cov_loc[ℓ, x]` as the Stein–covariance reduction delivers it. -/
noncomputable def covKLocCoeff2Lin (lam alpha gamma g x₀ : ℝ) : ℝ :=
  meanLocCoeff2 lam alpha gamma g x₀ / 2 -
    alpha / 12 * (locFourthCoeff2 lam alpha gamma g x₀ -
      locThirdCoeff lam alpha g x₀ * (-alpha / (2 * lam ^ 2) + g * x₀ / lam)) -
    gamma / 24 * (locFifthCoeff lam alpha g x₀ - 3 / lam ^ 2 * (-alpha / (2 * lam ^ 2) + g *
      x₀ / lam)) -
    g / 2 * (locThirdCoeff lam alpha g x₀ - 1 / lam * (-alpha / (2 * lam ^ 2) + g * x₀ / lam)) +
    g * x₀ / 2 * (locSecondCoeff2 lam alpha gamma g x₀ - (-alpha / (2 * lam ^ 2) + g *
      x₀ / lam) ^ 2)

/-- The `1/t` coefficient of `t²Cov_loc[ℓ, x²]` as the reduction delivers it. -/
noncomputable def covKLocCoeff2Sq (lam alpha gamma g x₀ : ℝ) : ℝ :=
  locSecondCoeff2 lam alpha gamma g x₀ -
    alpha / 12 * (locFifthCoeff lam alpha g x₀ - locThirdCoeff lam alpha g x₀ * (1 / lam)) -
    gamma / 24 * (15 / lam ^ 3 - 3 / lam ^ 2 * (1 / lam)) -
    g / 2 * (3 / lam ^ 2 - (1 / lam) ^ 2) +
    g * x₀ / 2 * (locThirdCoeff lam alpha g x₀ - (-alpha / (2 * lam ^ 2) + g * x₀ / lam) *
      (1 / lam))

/-- **The derivative reading at second order, linear probe**: the reduction's coefficient is
`2c'`, twice the second-order coefficient of `t⟨x⟩_loc`. -/
theorem covKLocCoeff2Lin_eq (lam alpha gamma g x₀ : ℝ) (hlam : 0 < lam) :
    covKLocCoeff2Lin lam alpha gamma g x₀ = 2 * meanLocCoeff2 lam alpha gamma g x₀ := by
  unfold covKLocCoeff2Lin meanLocCoeff2 locFourthCoeff2 locSecondCoeff2 locThirdCoeff locFifthCoeff
    locN1 locN4 locN2 locD1 locP₃ locP₄ meanCoeff2
  field_simp
  ring

/-- **The derivative reading at second order, quadratic probe**: the reduction's coefficient is
`2c₂'`, twice the second-order coefficient of `t⟨x²⟩_loc`. -/
theorem covKLocCoeff2Sq_eq (lam alpha gamma g x₀ : ℝ) (hlam : 0 < lam) :
    covKLocCoeff2Sq lam alpha gamma g x₀ = 2 * locSecondCoeff2 lam alpha gamma g x₀ := by
  unfold covKLocCoeff2Sq locSecondCoeff2 locThirdCoeff locFifthCoeff locN2 locD1 locP₃
  field_simp
  ring

/-- The `n = 1` assembly on abstract reals: the reduction's right-hand side, with the moments
expanded, deviates from `c + K/t` by `O(t⁻²)`. -/
theorem covK_loc_lin_order2_assembly (lam alpha gamma g x₀ t m₁ m₂ m₃ m₄ m₅ c c' c₂' s q₄ v
    K₁ K₂ K₃ K₄ K₅ : ℝ) (hlam : 0 < lam) (hgamma : 0 < gamma) (hg : 0 ≤ g) (ht1 : 1 ≤ t)
    (hc : c = -alpha / (2 * lam ^ 2) + g * x₀ / lam)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄)
    (e₁ : |t * m₁ - c - c' / t| ≤ K₁ / t ^ 2) (e₂ : |t * m₂ - 1 / lam - c₂' / t| ≤ K₂ / t ^ 2)
    (e₃ : |t ^ 2 * m₃ - s| ≤ K₃ / t) (e₄ : |t ^ 2 * m₄ - 3 / lam ^ 2 - q₄ / t| ≤ K₄ / t ^ 2)
    (e₅ : |t ^ 3 * m₅ - v| ≤ K₅ / t) :
    |(1 / 2 * (t * m₁) - alpha / 12 * (t ^ 2 * (m₄ - m₃ * m₁)) -
        gamma / 24 * (t ^ 2 * (m₅ - m₄ * m₁)) - g / 2 * (t * (m₃ - m₂ * m₁)) +
        g * x₀ / 2 * (t * (m₂ - m₁ * m₁))) - c -
      (c' / 2 - alpha / 12 * (q₄ - s * c) - gamma / 24 * (v - 3 / lam ^ 2 * c) -
        g / 2 * (s - 1 / lam * c) + g * x₀ / 2 * (c₂' - c ^ 2)) / t| ≤
      (K₁ / 2 + |alpha| / 12 * (K₄ + (K₃ * (|c| + (|c'| + K₁)) + |s| * (|c'| + K₁))) +
        gamma / 24 * (K₅ + ((|q₄| + K₄) * (|c| + (|c'| + K₁)) + |3 / lam ^ 2| * (|c'| + K₁))) +
        g / 2 * (K₃ + ((|c₂'| + K₂) * (|c| + (|c'| + K₁)) + |1 / lam| * (|c'| + K₁))) +
        |g * x₀| / 2 * (K₂ + ((|c'| + K₁) * (|c| + (|c'| + K₁)) + |c| * (|c'| + K₁)))) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  -- leading-order rates from the second-order ones
  have f₁ : |t * m₁ - c| ≤ (|c'| + K₁) / t := order2_to_order1 ht1 hK₁ e₁
  have f₂ : |t * m₂ - 1 / lam| ≤ (|c₂'| + K₂) / t := order2_to_order1 ht1 hK₂ e₂
  have f₄ : |t ^ 2 * m₄ - 3 / lam ^ 2| ≤ (|q₄| + K₄) / t := order2_to_order1 ht1 hK₄ e₄
  have hK₁' : 0 ≤ |c'| + K₁ := by positivity
  -- the products
  have p₃₁ := prod_rate t (t ^ 2 * m₃) (t * m₁) s c K₃ (|c'| + K₁) ht1 hK₃ hK₁' e₃ f₁
  have p₄₁ := prod_rate t (t ^ 2 * m₄) (t * m₁) (3 / lam ^ 2) c (|q₄| + K₄) (|c'| + K₁) ht1
    (by positivity) hK₁' f₄ f₁
  have p₂₁ := prod_rate t (t * m₂) (t * m₁) (1 / lam) c (|c₂'| + K₂) (|c'| + K₁) ht1
    (by positivity) hK₁' f₂ f₁
  have p₁₁ := prod_rate t (t * m₁) (t * m₁) c c (|c'| + K₁) (|c'| + K₁) ht1 hK₁' hK₁' f₁ f₁
  -- the residual identity
  have key : (1 / 2 * (t * m₁) - alpha / 12 * (t ^ 2 * (m₄ - m₃ * m₁)) -
        gamma / 24 * (t ^ 2 * (m₅ - m₄ * m₁)) - g / 2 * (t * (m₃ - m₂ * m₁)) +
        g * x₀ / 2 * (t * (m₂ - m₁ * m₁))) - c -
      (c' / 2 - alpha / 12 * (q₄ - s * c) - gamma / 24 * (v - 3 / lam ^ 2 * c) -
        g / 2 * (s - 1 / lam * c) + g * x₀ / 2 * (c₂' - c ^ 2)) / t =
      1 / 2 * (t * m₁ - c - c' / t) -
        alpha / 12 * ((t ^ 2 * m₄ - 3 / lam ^ 2 - q₄ / t) -
          ((t ^ 2 * m₃) * (t * m₁) - s * c) / t) -
        gamma / 24 * (((t ^ 3 * m₅ - v) - ((t ^ 2 * m₄) * (t * m₁) - 3 / lam ^ 2 * c)) / t) -
        g / 2 * (((t ^ 2 * m₃ - s) - ((t * m₂) * (t * m₁) - 1 / lam * c)) / t) +
        g * x₀ / 2 * ((t * m₂ - 1 / lam - c₂' / t) - ((t * m₁) * (t * m₁) - c * c) / t) := by
    subst hc
    field_simp
    ring
  rw [key]
  -- the five brackets
  have b₁ : |1 / 2 * (t * m₁ - c - c' / t)| ≤ K₁ / 2 / t ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc 1 / 2 * |t * m₁ - c - c' / t| ≤ 1 / 2 * (K₁ / t ^ 2) := by gcongr
      _ = K₁ / 2 / t ^ 2 := by ring
  have b₂ : |alpha / 12 * ((t ^ 2 * m₄ - 3 / lam ^ 2 - q₄ / t) -
      ((t ^ 2 * m₃) * (t * m₁) - s * c) / t)| ≤
      |alpha| / 12 * (K₄ + (K₃ * (|c| + (|c'| + K₁)) + |s| * (|c'| + K₁))) / t ^ 2 := by
    rw [abs_mul, abs_div alpha, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    have h : |(t ^ 2 * m₄ - 3 / lam ^ 2 - q₄ / t) - ((t ^ 2 * m₃) * (t * m₁) - s * c) / t| ≤
        (K₄ + (K₃ * (|c| + (|c'| + K₁)) + |s| * (|c'| + K₁))) / t ^ 2 := by
      calc _ ≤ |t ^ 2 * m₄ - 3 / lam ^ 2 - q₄ / t| + |((t ^ 2 * m₃) * (t * m₁) - s * c) / t| :=
            abs_sub _ _
        _ ≤ K₄ / t ^ 2 + (K₃ * (|c| + (|c'| + K₁)) + |s| * (|c'| + K₁)) / t / t := by
            gcongr
            rw [abs_div, abs_of_pos ht0]
            exact div_le_div_of_nonneg_right p₃₁ ht0.le
        _ = _ := by ring
    calc _ ≤ |alpha| / 12 * ((K₄ + (K₃ * (|c| + (|c'| + K₁)) + |s| * (|c'| + K₁))) / t ^ 2) := by
          gcongr
      _ = _ := by ring
  have b₃ : |gamma / 24 * (((t ^ 3 * m₅ - v) - ((t ^ 2 * m₄) * (t * m₁) - 3 / lam ^ 2 * c)) / t)| ≤
      gamma / 24 * (K₅ + ((|q₄| + K₄) * (|c| + (|c'| + K₁)) + |3 / lam ^ 2| * (|c'| + K₁))) /
        t ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 24), abs_div, abs_of_pos ht0]
    have h : |(t ^ 3 * m₅ - v) - ((t ^ 2 * m₄) * (t * m₁) - 3 / lam ^ 2 * c)| ≤
        (K₅ + ((|q₄| + K₄) * (|c| + (|c'| + K₁)) + |3 / lam ^ 2| * (|c'| + K₁))) / t := by
      calc _ ≤ |t ^ 3 * m₅ - v| + |(t ^ 2 * m₄) * (t * m₁) - 3 / lam ^ 2 * c| := abs_sub _ _
        _ ≤ K₅ / t + ((|q₄| + K₄) * (|c| + (|c'| + K₁)) + |3 / lam ^ 2| * (|c'| + K₁)) / t :=
            add_le_add e₅ p₄₁
        _ = _ := by ring
    calc gamma / 24 * (|(t ^ 3 * m₅ - v) - ((t ^ 2 * m₄) * (t * m₁) - 3 / lam ^ 2 * c)| / t)
        ≤ gamma / 24 * ((K₅ + ((|q₄| + K₄) * (|c| + (|c'| + K₁)) +
            |3 / lam ^ 2| * (|c'| + K₁))) / t / t) := by gcongr
      _ = _ := by ring
  have b₄ : |g / 2 * (((t ^ 2 * m₃ - s) - ((t * m₂) * (t * m₁) - 1 / lam * c)) / t)| ≤
      g / 2 * (K₃ + ((|c₂'| + K₂) * (|c| + (|c'| + K₁)) + |1 / lam| * (|c'| + K₁))) / t ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g / 2), abs_div, abs_of_pos ht0]
    have h : |(t ^ 2 * m₃ - s) - ((t * m₂) * (t * m₁) - 1 / lam * c)| ≤
        (K₃ + ((|c₂'| + K₂) * (|c| + (|c'| + K₁)) + |1 / lam| * (|c'| + K₁))) / t := by
      calc _ ≤ |t ^ 2 * m₃ - s| + |(t * m₂) * (t * m₁) - 1 / lam * c| := abs_sub _ _
        _ ≤ K₃ / t + ((|c₂'| + K₂) * (|c| + (|c'| + K₁)) + |1 / lam| * (|c'| + K₁)) / t :=
            add_le_add e₃ p₂₁
        _ = _ := by ring
    calc g / 2 * (|(t ^ 2 * m₃ - s) - ((t * m₂) * (t * m₁) - 1 / lam * c)| / t)
        ≤ g / 2 * ((K₃ + ((|c₂'| + K₂) * (|c| + (|c'| + K₁)) + |1 / lam| * (|c'| +
          K₁))) / t / t) := by
          gcongr
      _ = _ := by ring
  have b₅ : |g * x₀ / 2 * ((t * m₂ - 1 / lam - c₂' / t) - ((t * m₁) * (t * m₁) - c * c) / t)| ≤
      |g * x₀| / 2 * (K₂ + ((|c'| + K₁) * (|c| + (|c'| + K₁)) + |c| * (|c'| + K₁))) / t ^ 2 := by
    rw [abs_mul, abs_div (g * x₀), abs_two]
    have h : |(t * m₂ - 1 / lam - c₂' / t) - ((t * m₁) * (t * m₁) - c * c) / t| ≤
        (K₂ + ((|c'| + K₁) * (|c| + (|c'| + K₁)) + |c| * (|c'| + K₁))) / t ^ 2 := by
      calc _ ≤ |t * m₂ - 1 / lam - c₂' / t| + |((t * m₁) * (t * m₁) - c * c) / t| := abs_sub _ _
        _ ≤ K₂ / t ^ 2 + ((|c'| + K₁) * (|c| + (|c'| + K₁)) + |c| * (|c'| + K₁)) / t / t := by
            gcongr
            rw [abs_div, abs_of_pos ht0]
            exact div_le_div_of_nonneg_right p₁₁ ht0.le
        _ = _ := by ring
    calc _ ≤ |g * x₀| / 2 * ((K₂ + ((|c'| + K₁) * (|c| + (|c'| + K₁)) + |c| * (|c'| + K₁))) /
          t ^ 2) := by gcongr
      _ = _ := by ring
  calc _ ≤ |1 / 2 * (t * m₁ - c - c' / t)| +
        |alpha / 12 * ((t ^ 2 * m₄ - 3 / lam ^ 2 - q₄ / t) -
          ((t ^ 2 * m₃) * (t * m₁) - s * c) / t)| +
        |gamma / 24 * (((t ^ 3 * m₅ - v) - ((t ^ 2 * m₄) * (t * m₁) - 3 / lam ^ 2 * c)) / t)| +
        |g / 2 * (((t ^ 2 * m₃ - s) - ((t * m₂) * (t * m₁) - 1 / lam * c)) / t)| +
        |g * x₀ / 2 * ((t * m₂ - 1 / lam - c₂' / t) - ((t * m₁) * (t * m₁) - c * c) / t)| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          exact abs_sub _ _
    _ ≤ K₁ / 2 / t ^ 2 +
        |alpha| / 12 * (K₄ + (K₃ * (|c| + (|c'| + K₁)) + |s| * (|c'| + K₁))) / t ^ 2 +
        gamma / 24 * (K₅ + ((|q₄| + K₄) * (|c| + (|c'| + K₁)) + |3 / lam ^ 2| * (|c'| + K₁))) /
          t ^ 2 +
        g / 2 * (K₃ + ((|c₂'| + K₂) * (|c| + (|c'| + K₁)) + |1 / lam| * (|c'| + K₁))) / t ^ 2 +
        |g * x₀| / 2 * (K₂ + ((|c'| + K₁) * (|c| + (|c'| + K₁)) + |c| * (|c'| + K₁))) / t ^ 2 :=
        add_le_add (add_le_add (add_le_add (add_le_add b₁ b₂) b₃) b₄) b₅
    _ = _ := by ring

/-- The `n = 2` assembly on abstract reals. -/
theorem covK_loc_sq_order2_assembly (lam alpha gamma g x₀ t m₁ m₂ m₃ m₄ m₅ m₆ c c₂' s v
    K₁ K₂ K₃ K₄ K₅ K₆ : ℝ) (hlam : 0 < lam) (hgamma : 0 < gamma) (hg : 0 ≤ g) (ht1 : 1 ≤ t)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄)
    (f₁ : |t * m₁ - c| ≤ K₁ / t) (e₂ : |t * m₂ - 1 / lam - c₂' / t| ≤ K₂ / t ^ 2)
    (e₃ : |t ^ 2 * m₃ - s| ≤ K₃ / t) (f₄ : |t ^ 2 * m₄ - 3 / lam ^ 2| ≤ K₄ / t)
    (e₅ : |t ^ 3 * m₅ - v| ≤ K₅ / t) (e₆ : |t ^ 3 * m₆ - 15 / lam ^ 3| ≤ K₆ / t) :
    |(t * m₂ - alpha / 12 * (t ^ 2 * (m₅ - m₃ * m₂)) - gamma / 24 * (t ^ 2 * (m₆ - m₄ * m₂)) -
        g / 2 * (t * (m₄ - m₂ * m₂)) + g * x₀ / 2 * (t * (m₃ - m₁ * m₂))) - 1 / lam -
      (c₂' - alpha / 12 * (v - s * (1 / lam)) - gamma / 24 * (15 / lam ^ 3 - 3 / lam ^ 2 *
        (1 / lam)) -
        g / 2 * (3 / lam ^ 2 - (1 / lam) ^ 2) + g * x₀ / 2 * (s - c * (1 / lam))) / t| ≤
      (K₂ + |alpha| / 12 * (K₅ + (K₃ * (|1 / lam| + (|c₂'| + K₂)) + |s| * (|c₂'| + K₂))) +
        gamma / 24 * (K₆ + (K₄ * (|1 / lam| + (|c₂'| + K₂)) + |3 / lam ^ 2| * (|c₂'| + K₂))) +
        g / 2 * (K₄ + ((|c₂'| + K₂) * (|1 / lam| + (|c₂'| + K₂)) + |1 / lam| * (|c₂'| + K₂))) +
        |g * x₀| / 2 * (K₃ + (K₁ * (|1 / lam| + (|c₂'| + K₂)) + |c| * (|c₂'| + K₂)))) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have f₂ : |t * m₂ - 1 / lam| ≤ (|c₂'| + K₂) / t := order2_to_order1 ht1 hK₂ e₂
  have hK₂' : 0 ≤ |c₂'| + K₂ := by positivity
  have p₃₂ := prod_rate t (t ^ 2 * m₃) (t * m₂) s (1 / lam) K₃ (|c₂'| + K₂) ht1 hK₃ hK₂' e₃ f₂
  have p₄₂ := prod_rate t (t ^ 2 * m₄) (t * m₂) (3 / lam ^ 2) (1 / lam) K₄ (|c₂'| + K₂) ht1 hK₄
    hK₂' f₄ f₂
  have p₂₂ := prod_rate t (t * m₂) (t * m₂) (1 / lam) (1 / lam) (|c₂'| + K₂) (|c₂'| + K₂) ht1 hK₂'
    hK₂' f₂ f₂
  have p₁₂ := prod_rate t (t * m₁) (t * m₂) c (1 / lam) K₁ (|c₂'| + K₂) ht1 hK₁ hK₂' f₁ f₂
  have key : (t * m₂ - alpha / 12 * (t ^ 2 * (m₅ - m₃ * m₂)) -
        gamma / 24 * (t ^ 2 * (m₆ - m₄ * m₂)) - g / 2 * (t * (m₄ - m₂ * m₂)) +
        g * x₀ / 2 * (t * (m₃ - m₁ * m₂))) - 1 / lam -
      (c₂' - alpha / 12 * (v - s * (1 / lam)) - gamma / 24 * (15 / lam ^ 3 - 3 / lam ^ 2 *
        (1 / lam)) -
        g / 2 * (3 / lam ^ 2 - (1 / lam) ^ 2) + g * x₀ / 2 * (s - c * (1 / lam))) / t =
      (t * m₂ - 1 / lam - c₂' / t) -
        alpha / 12 * (((t ^ 3 * m₅ - v) - ((t ^ 2 * m₃) * (t * m₂) - s * (1 / lam))) / t) -
        gamma / 24 * (((t ^ 3 * m₆ - 15 / lam ^ 3) -
          ((t ^ 2 * m₄) * (t * m₂) - 3 / lam ^ 2 * (1 / lam))) / t) -
        g / 2 * (((t ^ 2 * m₄ - 3 / lam ^ 2) - ((t * m₂) * (t * m₂) - 1 / lam * (1 / lam))) / t) +
        g * x₀ / 2 * (((t ^ 2 * m₃ - s) - ((t * m₁) * (t * m₂) - c * (1 / lam))) / t) := by
    field_simp
    ring
  rw [key]
  have b₂ : |alpha / 12 * (((t ^ 3 * m₅ - v) - ((t ^ 2 * m₃) * (t * m₂) - s * (1 / lam))) / t)| ≤
      |alpha| / 12 * (K₅ + (K₃ * (|1 / lam| + (|c₂'| + K₂)) + |s| * (|c₂'| + K₂))) / t ^ 2 := by
    rw [abs_mul, abs_div alpha, abs_of_pos (by norm_num : (0 : ℝ) < 12),
      abs_div ((t ^ 3 * m₅ - v) - _), abs_of_pos ht0]
    have h : |(t ^ 3 * m₅ - v) - ((t ^ 2 * m₃) * (t * m₂) - s * (1 / lam))| ≤
        (K₅ + (K₃ * (|1 / lam| + (|c₂'| + K₂)) + |s| * (|c₂'| + K₂))) / t := by
      calc _ ≤ |t ^ 3 * m₅ - v| + |(t ^ 2 * m₃) * (t * m₂) - s * (1 / lam)| := abs_sub _ _
        _ ≤ K₅ / t + (K₃ * (|1 / lam| + (|c₂'| + K₂)) + |s| * (|c₂'| + K₂)) / t :=
            add_le_add e₅ p₃₂
        _ = _ := by ring
    calc |alpha| / 12 * (|(t ^ 3 * m₅ - v) - ((t ^ 2 * m₃) * (t * m₂) - s * (1 / lam))| / t)
        ≤ |alpha| / 12 * ((K₅ + (K₃ * (|1 / lam| + (|c₂'| + K₂)) + |s| * (|c₂'| +
          K₂))) / t / t) := by
          gcongr
      _ = _ := by ring
  have b₃ : |gamma / 24 * (((t ^ 3 * m₆ - 15 / lam ^ 3) -
      ((t ^ 2 * m₄) * (t * m₂) - 3 / lam ^ 2 * (1 / lam))) / t)| ≤
      gamma / 24 * (K₆ + (K₄ * (|1 / lam| + (|c₂'| + K₂)) + |3 / lam ^ 2| * (|c₂'| + K₂))) /
        t ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 24), abs_div, abs_of_pos ht0]
    have h : |(t ^ 3 * m₆ - 15 / lam ^ 3) - ((t ^ 2 * m₄) * (t * m₂) - 3 / lam ^ 2 * (1 / lam))| ≤
        (K₆ + (K₄ * (|1 / lam| + (|c₂'| + K₂)) + |3 / lam ^ 2| * (|c₂'| + K₂))) / t := by
      calc _ ≤ |t ^ 3 * m₆ - 15 / lam ^ 3| + |(t ^ 2 * m₄) * (t * m₂) - 3 / lam ^ 2 * (1 / lam)| :=
            abs_sub _ _
        _ ≤ K₆ / t + (K₄ * (|1 / lam| + (|c₂'| + K₂)) + |3 / lam ^ 2| * (|c₂'| + K₂)) / t :=
            add_le_add e₆ p₄₂
        _ = _ := by ring
    calc gamma / 24 * (|(t ^ 3 * m₆ - 15 / lam ^ 3) -
          ((t ^ 2 * m₄) * (t * m₂) - 3 / lam ^ 2 * (1 / lam))| / t)
        ≤ gamma / 24 * ((K₆ + (K₄ * (|1 / lam| + (|c₂'| + K₂)) + |3 / lam ^ 2| * (|c₂'| + K₂))) /
            t / t) := by gcongr
      _ = _ := by ring
  have b₄ : |g / 2 * (((t ^ 2 * m₄ - 3 / lam ^ 2) - ((t * m₂) * (t * m₂) - 1 / lam * (1 / lam))) /
      t)| ≤
      g / 2 * (K₄ + ((|c₂'| + K₂) * (|1 / lam| + (|c₂'| + K₂)) + |1 / lam| * (|c₂'| + K₂))) /
        t ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g / 2), abs_div, abs_of_pos ht0]
    have h : |(t ^ 2 * m₄ - 3 / lam ^ 2) - ((t * m₂) * (t * m₂) - 1 / lam * (1 / lam))| ≤
        (K₄ + ((|c₂'| + K₂) * (|1 / lam| + (|c₂'| + K₂)) + |1 / lam| * (|c₂'| + K₂))) / t := by
      calc _ ≤ |t ^ 2 * m₄ - 3 / lam ^ 2| + |(t * m₂) * (t * m₂) - 1 / lam * (1 / lam)| :=
            abs_sub _ _
        _ ≤ K₄ / t + ((|c₂'| + K₂) * (|1 / lam| + (|c₂'| + K₂)) + |1 / lam| * (|c₂'| + K₂)) / t :=
            add_le_add f₄ p₂₂
        _ = _ := by ring
    calc g / 2 * (|(t ^ 2 * m₄ - 3 / lam ^ 2) - ((t * m₂) * (t * m₂) - 1 / lam * (1 / lam))| / t)
        ≤ g / 2 * ((K₄ + ((|c₂'| + K₂) * (|1 / lam| + (|c₂'| + K₂)) + |1 / lam| * (|c₂'| + K₂))) /
            t / t) := by gcongr
      _ = _ := by ring
  have b₅ : |g * x₀ / 2 * (((t ^ 2 * m₃ - s) - ((t * m₁) * (t * m₂) - c * (1 / lam))) / t)| ≤
      |g * x₀| / 2 * (K₃ + (K₁ * (|1 / lam| + (|c₂'| + K₂)) + |c| * (|c₂'| + K₂))) / t ^ 2 := by
    rw [abs_mul, abs_div (g * x₀), abs_two, abs_div ((t ^ 2 * m₃ - s) - _), abs_of_pos ht0]
    have h : |(t ^ 2 * m₃ - s) - ((t * m₁) * (t * m₂) - c * (1 / lam))| ≤
        (K₃ + (K₁ * (|1 / lam| + (|c₂'| + K₂)) + |c| * (|c₂'| + K₂))) / t := by
      calc _ ≤ |t ^ 2 * m₃ - s| + |(t * m₁) * (t * m₂) - c * (1 / lam)| := abs_sub _ _
        _ ≤ K₃ / t + (K₁ * (|1 / lam| + (|c₂'| + K₂)) + |c| * (|c₂'| + K₂)) / t :=
            add_le_add e₃ p₁₂
        _ = _ := by ring
    calc |g * x₀| / 2 * (|(t ^ 2 * m₃ - s) - ((t * m₁) * (t * m₂) - c * (1 / lam))| / t)
        ≤ |g * x₀| / 2 * ((K₃ + (K₁ * (|1 / lam| + (|c₂'| + K₂)) + |c| * (|c₂'| +
          K₂))) / t / t) := by
          gcongr
      _ = _ := by ring
  calc _ ≤ |t * m₂ - 1 / lam - c₂' / t| +
        |alpha / 12 * (((t ^ 3 * m₅ - v) - ((t ^ 2 * m₃) * (t * m₂) - s * (1 / lam))) / t)| +
        |gamma / 24 * (((t ^ 3 * m₆ - 15 / lam ^ 3) -
          ((t ^ 2 * m₄) * (t * m₂) - 3 / lam ^ 2 * (1 / lam))) / t)| +
        |g / 2 * (((t ^ 2 * m₄ - 3 / lam ^ 2) - ((t * m₂) * (t * m₂) - 1 / lam * (1 / lam))) / t)| +
        |g * x₀ / 2 * (((t ^ 2 * m₃ - s) - ((t * m₁) * (t * m₂) - c * (1 / lam))) / t)| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          exact abs_sub _ _
    _ ≤ K₂ / t ^ 2 +
        |alpha| / 12 * (K₅ + (K₃ * (|1 / lam| + (|c₂'| + K₂)) + |s| * (|c₂'| + K₂))) / t ^ 2 +
        gamma / 24 * (K₆ + (K₄ * (|1 / lam| + (|c₂'| + K₂)) + |3 / lam ^ 2| * (|c₂'| + K₂))) /
          t ^ 2 +
        g / 2 * (K₄ + ((|c₂'| + K₂) * (|1 / lam| + (|c₂'| + K₂)) + |1 / lam| * (|c₂'| + K₂))) /
          t ^ 2 +
        |g * x₀| / 2 * (K₃ + (K₁ * (|1 / lam| + (|c₂'| + K₂)) + |c| * (|c₂'| + K₂))) / t ^ 2 :=
        add_le_add (add_le_add (add_le_add (add_le_add e₂ b₂) b₃) b₄) b₅
    _ = _ := by ring

end CovKCoeffs

section CovKRates

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- The reduction at `n = 1`, with the covariances written in the localised moments. -/
theorem stein_loc_cov_reduction_lin (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x) =
      1 / 2 * (t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x)) -
      alpha / 12 * (t ^ 2 * (_root_.Laplace.gibbsExpectation
        (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 4) -
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 3) *
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x))) -
      gamma / 24 * (t ^ 2 * (_root_.Laplace.gibbsExpectation
        (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 5) -
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 4) *
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x))) -
      g / 2 * (t * (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 3) -
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2) *
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x))) +
      g * x₀ / 2 * (t * (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 2) -
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x) *
        _root_.Laplace.gibbsExpectation
          (locPotential1 lam alpha gamma g x₀ t) t (fun x => x))) := by
  have h := stein_loc_cov_reduction hlam hgamma hdisc hg ht (x₀ := x₀) 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h]
  unfold _root_.Laplace.gibbsCov
  have e3 : (fun x : ℝ => x ^ 3 * x) = fun x => x ^ 4 := by funext x; ring
  have e4 : (fun x : ℝ => x ^ 4 * x) = fun x => x ^ 5 := by funext x; ring
  have e2 : (fun x : ℝ => x ^ 2 * x) = fun x => x ^ 3 := by funext x; ring
  have e1 : (fun x : ℝ => x * x) = fun x => x ^ 2 := by funext x; ring
  rw [e3, e4, e2, e1]

/-- The reduction at `n = 2`, with the covariances written in the localised moments. -/
theorem stein_loc_cov_reduction_sq (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) =
      t * _root_.Laplace.gibbsExpectation
        (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2) -
      alpha / 12 * (t ^ 2 * (_root_.Laplace.gibbsExpectation
        (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 5) -
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 3) *
        _root_.Laplace.gibbsExpectation
          (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2))) -
      gamma / 24 * (t ^ 2 * (_root_.Laplace.gibbsExpectation
        (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 6) -
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 4) *
        _root_.Laplace.gibbsExpectation
          (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2))) -
      g / 2 * (t * (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 4) -
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2) *
        _root_.Laplace.gibbsExpectation
          (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2))) +
      g * x₀ / 2 * (t * (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (fun x => x ^ 3) -
        _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x) *
        _root_.Laplace.gibbsExpectation
          (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2))) := by
  have h := stein_loc_cov_reduction hlam hgamma hdisc hg ht (x₀ := x₀) 2
  rw [h]
  unfold _root_.Laplace.gibbsCov
  have e3 : (fun x : ℝ => x ^ 3 * x ^ 2) = fun x => x ^ 5 := by funext x; ring
  have e4 : (fun x : ℝ => x ^ 4 * x ^ 2) = fun x => x ^ 6 := by funext x; ring
  have e2 : (fun x : ℝ => x ^ 2 * x ^ 2) = fun x => x ^ 4 := by funext x; ring
  have e1 : (fun x : ℝ => x * x ^ 2) = fun x => x ^ 3 := by funext x; ring
  rw [e3, e4, e2, e1]
  push_cast
  ring

/-- `|t⟨x⟩_loc − c − c'/t| ≤ K/t²` in the `gibbsExpectation (locPotential1 …)` form. -/
theorem locMean_loc_order2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x) -
        (-alpha / (2 * lam ^ 2) + g * x₀ / lam) - meanLocCoeff2 lam alpha gamma g x₀ / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedMean_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [gibbsExpectation_locPotential1_id ht0]
  exact h ht

/-- **eq:covK on the localised measure to second order, linear probe**:
`|t²Cov_loc[ℓ, x] − c − 2c'/t| ≤ K/t²`, `c' = meanLocCoeff2` — the derivative reading
`Cov_loc = −∂ₜ⟨·⟩_loc` holds coefficientwise at second order. -/
theorem localisedCovK_lin_order2_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x) -
        (-alpha / (2 * lam ^ 2) + g * x₀ / lam) -
        2 * meanLocCoeff2 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := locMean_loc_order2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locSecondMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locThirdMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_rate4 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := locFifthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  set c := -alpha / (2 * lam ^ 2) + g * x₀ / lam with hc
  set c' := meanLocCoeff2 lam alpha gamma g x₀ with hc'
  set c₂' := locSecondCoeff2 lam alpha gamma g x₀ with hc₂'
  set s := locThirdCoeff lam alpha g x₀ with hs
  set q₄ := locFourthCoeff2 lam alpha gamma g x₀ with hq₄
  set v := locFifthCoeff lam alpha g x₀ with hv
  refine ⟨K₁ / 2 + |alpha| / 12 * (K₄ + (K₃ * (|c| + (|c'| + K₁)) + |s| * (|c'| + K₁))) +
      gamma / 24 * (K₅ + ((|q₄| + K₄) * (|c| + (|c'| + K₁)) + |3 / lam ^ 2| * (|c'| + K₁))) +
      g / 2 * (K₃ + ((|c₂'| + K₂) * (|c| + (|c'| + K₁)) + |1 / lam| * (|c'| + K₁))) +
      |g * x₀| / 2 * (K₂ + ((|c'| + K₁) * (|c| + (|c'| + K₁)) + |c| * (|c'| + K₁))),
    T₁ + T₂ + T₃ + T₄ + T₅, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [stein_loc_cov_reduction_lin hlam hgamma hdisc hg ht0,
    ← covKLocCoeff2Lin_eq lam alpha gamma g x₀ hlam]
  have key := covK_loc_lin_order2_assembly lam alpha gamma g x₀ t
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x))
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2))
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 3))
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 4))
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 5))
    c c' c₂' s q₄ v K₁ K₂ K₃ K₄ K₅ hlam hgamma hg ht1 hc hK₁ hK₂ hK₃ hK₄
    (h₁ (t := t) (by linarith)) (h₂ (t := t) (by linarith)) (h₃ (t := t) (by linarith))
    (h₄ (t := t) (by linarith)) (h₅ (t := t) (by linarith))
  unfold covKLocCoeff2Lin
  exact key

/-- **eq:covK on the localised measure to second order, quadratic probe**:
`|t²Cov_loc[ℓ, x²] − 1/λ − 2c₂'/t| ≤ K/t²`, `c₂' = locSecondCoeff2`. -/
theorem localisedCovK_sq_order2_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) - 1 / lam -
        2 * locSecondCoeff2 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := locMean_loc_leading hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locSecondMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locThirdMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := locFifthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := locSixthMoment_loc_rate hlam hgamma hdisc hg (x₀ := x₀)
  set c := -alpha / (2 * lam ^ 2) + g * x₀ / lam with hc
  set c₂' := locSecondCoeff2 lam alpha gamma g x₀ with hc₂'
  set s := locThirdCoeff lam alpha g x₀ with hs
  set v := locFifthCoeff lam alpha g x₀ with hv
  refine ⟨K₂ + |alpha| / 12 * (K₅ + (K₃ * (|1 / lam| + (|c₂'| + K₂)) + |s| * (|c₂'| + K₂))) +
      gamma / 24 * (K₆ + (K₄ * (|1 / lam| + (|c₂'| + K₂)) + |3 / lam ^ 2| * (|c₂'| + K₂))) +
      g / 2 * (K₄ + ((|c₂'| + K₂) * (|1 / lam| + (|c₂'| + K₂)) + |1 / lam| * (|c₂'| + K₂))) +
      |g * x₀| / 2 * (K₃ + (K₁ * (|1 / lam| + (|c₂'| + K₂)) + |c| * (|c₂'| + K₂))),
    T₁ + T₂ + T₃ + T₄ + T₅ + T₆, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [stein_loc_cov_reduction_sq hlam hgamma hdisc hg ht0,
    ← covKLocCoeff2Sq_eq lam alpha gamma g x₀ hlam]
  have key := covK_loc_sq_order2_assembly lam alpha gamma g x₀ t
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x))
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 2))
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 3))
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 4))
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 5))
    (_root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t (fun x => x ^ 6))
    c c₂' s v K₁ K₂ K₃ K₄ K₅ K₆ hlam hgamma hg ht1 hK₁ hK₂ hK₃ hK₄
    (h₁ (t := t) (by linarith)) (h₂ (t := t) (by linarith)) (h₃ (t := t) (by linarith))
    (h₄ (t := t) (by linarith)) (h₅ (t := t) (by linarith)) (h₆ (t := t) (by linarith))
  unfold covKLocCoeff2Sq
  exact key

end CovKRates

end Laplace.Multi
