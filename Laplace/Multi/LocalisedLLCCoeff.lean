/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedMeanCoeff

/-!
# The localised anharmonic energy to second order

Tide 69 certified E3's localised LLC to first order, `|t⟨ℓ⟩_loc − ½·tλ/(tλ + g)| ≤ K/t`, without
identifying the `1/t` coefficient. This file identifies it: with `a = g x₀`,
`t⟨ℓ⟩_loc = ½ + e₁/t + O(t⁻²)`, `e₁ = (a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³) = e₀ + d₁`
(`e₀` the unlocalised first correction, `d₁` the `1/t` coefficient of `⟨φ⟩`), then E2's rotated
form and the residual against the trace prediction.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

/-! ### The weight times `x²`, `x³`, `x⁴`, with even remainders -/

section Weight

variable {g x₀ : ℝ}

/-- `x²·P₃(y) = x² + ax³ + p₃x⁴ + p₄x⁵ + (r₄x⁶ + r₅x⁷ + r₆x⁸)`. -/
theorem mul_sq_P3_eq (g x₀ x : ℝ) :
    x ^ 2 * ∑ m ∈ Finset.range 4, (g * x₀ * x - g / 2 * x ^ 2) ^ m / (m.factorial : ℝ) =
      x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5 +
        (locR₄' g x₀ * x ^ 6 + locR₅' g x₀ * x ^ 7 + locR₆' g * x ^ 8) := by
  rw [P3_eq]
  unfold locP₄ locR₃'
  ring

/-- The even envelope of the `x²φ` remainder. -/
noncomputable def locH₆ (g x₀ : ℝ) : ℝ :=
  |locR₄' g x₀| + |locR₅' g x₀| / 2 + 16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g * x₀| ^ 4
noncomputable def locH₈ (g x₀ : ℝ) : ℝ := |locR₅' g x₀| / 2 + |locR₆' g|
noncomputable def locH₁₀ (g x₀ : ℝ) : ℝ := 16 * (Real.exp (g * x₀ ^ 2 / 2) + 4) * |g / 2| ^ 4

theorem locH₆_nonneg (g x₀ : ℝ) : 0 ≤ locH₆ g x₀ := by unfold locH₆; positivity
theorem locH₈_nonneg (g x₀ : ℝ) : 0 ≤ locH₈ g x₀ := by unfold locH₈; positivity
theorem locH₁₀_nonneg (g x₀ : ℝ) : 0 ≤ locH₁₀ g x₀ := by unfold locH₁₀; positivity

/-- **The shared expansion**: `|x²φ − (x² + ax³ + p₃x⁴ + p₄x⁵)| ≤ H₆x⁶ + H₈x⁸ + H₁₀x¹⁰`. -/
theorem locSquare_pointwise (hg : 0 ≤ g) (x : ℝ) :
    |x ^ 2 * locWeight g x₀ x -
        (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)| ≤
      locH₆ g x₀ * x ^ 6 + locH₈ g x₀ * x ^ 8 + locH₁₀ g x₀ * x ^ 10 := by
  set y := g * x₀ * x - g / 2 * x ^ 2 with hy
  set C := Real.exp (g * x₀ ^ 2 / 2) + 4 with hC
  have hC0 : 0 ≤ C := by positivity
  have hT : |locWeight g x₀ x - ∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)| ≤ C * |y| ^ 4 := by
    have := locWeight_taylor_le (x₀ := x₀) hg (n := 4) (by norm_num) x
    simpa using this
  have hy4 : |y| ^ 4 ≤ 2 ^ 4 * (|g * x₀| ^ 4 * |x| ^ 4 + |g / 2| ^ 4 * (x ^ 2) ^ 4) :=
    abs_locExponent_pow_le (g * x₀) (g / 2) x 4
  have e : x ^ 2 * locWeight g x₀ x -
      (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5) =
      x ^ 2 * (locWeight g x₀ x - ∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)) +
        (locR₄' g x₀ * x ^ 6 + locR₅' g x₀ * x ^ 7 + locR₆' g * x ^ 8) := by
    have := mul_sq_P3_eq g x₀ x
    rw [← hy] at this
    linear_combination this
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hx6 : x ^ 6 = |x| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : x ^ 8 = |x| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx10 : x ^ 10 = |x| ^ 10 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h7 : |x| ^ 7 ≤ (|x| ^ 6 + |x| ^ 8) / 2 := by nlinarith [sq_nonneg (|x| ^ 3 - |x| ^ 4)]
  have hmain : |x ^ 2 * (locWeight g x₀ x - ∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)) +
        (locR₄' g x₀ * x ^ 6 + locR₅' g x₀ * x ^ 7 + locR₆' g * x ^ 8)|
      ≤ x ^ 2 * (C * (2 ^ 4 * (|g * x₀| ^ 4 * |x| ^ 4 + |g / 2| ^ 4 * (x ^ 2) ^ 4))) +
        (|locR₄' g x₀| * |x| ^ 6 + |locR₅' g x₀| * |x| ^ 7 + |locR₆' g| * |x| ^ 8) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (x ^ 2), abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
    gcongr
    · exact hT.trans (mul_le_mul_of_nonneg_left hy4 hC0)
    · calc |locR₄' g x₀ * x ^ 6 + locR₅' g x₀ * x ^ 7 + locR₆' g * x ^ 8|
          ≤ |locR₄' g x₀ * x ^ 6| + |locR₅' g x₀ * x ^ 7| + |locR₆' g * x ^ 8| :=
            abs_add_three _ _ _
        _ = |locR₄' g x₀| * |x| ^ 6 + |locR₅' g x₀| * |x| ^ 7 + |locR₆' g| * |x| ^ 8 := by
            simp only [abs_mul, abs_pow]
  rw [e]
  refine hmain.trans ?_
  rw [hx2, hx6, hx8, hx10]
  have hgx : 0 ≤ |g * x₀| ^ 4 := by positivity
  have hgb : 0 ≤ |g / 2| ^ 4 := by positivity
  calc _ = 16 * C * |g * x₀| ^ 4 * |x| ^ 6 + 16 * C * |g / 2| ^ 4 * |x| ^ 10 +
        (|locR₄' g x₀| * |x| ^ 6 + |locR₅' g x₀| * |x| ^ 7 + |locR₆' g| * |x| ^ 8) := by ring
    _ ≤ 16 * C * |g * x₀| ^ 4 * |x| ^ 6 + 16 * C * |g / 2| ^ 4 * |x| ^ 10 +
        (|locR₄' g x₀| * |x| ^ 6 + |locR₅' g x₀| * ((|x| ^ 6 + |x| ^ 8) / 2) +
          |locR₆' g| * |x| ^ 8) := by gcongr
    _ = locH₆ g x₀ * |x| ^ 6 + locH₈ g x₀ * |x| ^ 8 + locH₁₀ g x₀ * |x| ^ 10 := by
        rw [hC]
        unfold locH₆ locH₈ locH₁₀
        ring

/-- The even envelope of the `x³φ` remainder (from the shared expansion times `x`). -/
noncomputable def locJ₆ (g x₀ : ℝ) : ℝ := |locP₄ g x₀| + locH₆ g x₀ / 2
noncomputable def locJ₈ (g x₀ : ℝ) : ℝ := locH₆ g x₀ / 2 + locH₈ g x₀ / 2
noncomputable def locJ₁₀ (g x₀ : ℝ) : ℝ := locH₈ g x₀ / 2 + locH₁₀ g x₀ / 2
noncomputable def locJ₁₂ (g x₀ : ℝ) : ℝ := locH₁₀ g x₀ / 2

theorem locJ₆_nonneg (g x₀ : ℝ) : 0 ≤ locJ₆ g x₀ := by
  unfold locJ₆; have := locH₆_nonneg g x₀; positivity
theorem locJ₈_nonneg (g x₀ : ℝ) : 0 ≤ locJ₈ g x₀ := by
  unfold locJ₈; have := locH₆_nonneg g x₀; have := locH₈_nonneg g x₀; positivity
theorem locJ₁₀_nonneg (g x₀ : ℝ) : 0 ≤ locJ₁₀ g x₀ := by
  unfold locJ₁₀; have := locH₈_nonneg g x₀; have := locH₁₀_nonneg g x₀; positivity
theorem locJ₁₂_nonneg (g x₀ : ℝ) : 0 ≤ locJ₁₂ g x₀ := by
  unfold locJ₁₂; have := locH₁₀_nonneg g x₀; positivity

/-- `|x³φ − (x³ + ax⁴ + p₃x⁵)| ≤ J₆x⁶ + J₈x⁸ + J₁₀x¹⁰ + J₁₂x¹²` (the signed `x⁵` kept exact). -/
theorem locCubic_pointwise2 (hg : 0 ≤ g) (x : ℝ) :
    |x ^ 3 * locWeight g x₀ x - (x ^ 3 + g * x₀ * x ^ 4 + locP₃ g x₀ * x ^ 5)| ≤
      locJ₆ g x₀ * x ^ 6 + locJ₈ g x₀ * x ^ 8 + locJ₁₀ g x₀ * x ^ 10 + locJ₁₂ g x₀ * x ^ 12 := by
  have hS := locSquare_pointwise (x₀ := x₀) hg x
  have e : x ^ 3 * locWeight g x₀ x - (x ^ 3 + g * x₀ * x ^ 4 + locP₃ g x₀ * x ^ 5) =
      x * (x ^ 2 * locWeight g x₀ x -
        (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)) +
        locP₄ g x₀ * x ^ 6 := by ring
  have hx6 : x ^ 6 = |x| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : x ^ 8 = |x| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx10 : x ^ 10 = |x| ^ 10 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx12 : x ^ 12 = |x| ^ 12 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h7 : |x| ^ 7 ≤ (|x| ^ 6 + |x| ^ 8) / 2 := by nlinarith [sq_nonneg (|x| ^ 3 - |x| ^ 4)]
  have h9 : |x| ^ 9 ≤ (|x| ^ 8 + |x| ^ 10) / 2 := by nlinarith [sq_nonneg (|x| ^ 4 - |x| ^ 5)]
  have h11 : |x| ^ 11 ≤ (|x| ^ 10 + |x| ^ 12) / 2 := by nlinarith [sq_nonneg (|x| ^ 5 - |x| ^ 6)]
  have hH₆ := locH₆_nonneg g x₀
  have hH₈ := locH₈_nonneg g x₀
  have hH₁₀ := locH₁₀_nonneg g x₀
  rw [e]
  calc |x * (x ^ 2 * locWeight g x₀ x -
          (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)) +
          locP₄ g x₀ * x ^ 6|
      ≤ |x| * (locH₆ g x₀ * x ^ 6 + locH₈ g x₀ * x ^ 8 + locH₁₀ g x₀ * x ^ 10) +
          |locP₄ g x₀| * |x| ^ 6 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_pow]
        gcongr
    _ = locH₆ g x₀ * |x| ^ 7 + locH₈ g x₀ * |x| ^ 9 + locH₁₀ g x₀ * |x| ^ 11 +
          |locP₄ g x₀| * |x| ^ 6 := by rw [hx6, hx8, hx10]; ring
    _ ≤ locH₆ g x₀ * ((|x| ^ 6 + |x| ^ 8) / 2) + locH₈ g x₀ * ((|x| ^ 8 + |x| ^ 10) / 2) +
          locH₁₀ g x₀ * ((|x| ^ 10 + |x| ^ 12) / 2) + |locP₄ g x₀| * |x| ^ 6 := by gcongr
    _ = locJ₆ g x₀ * x ^ 6 + locJ₈ g x₀ * x ^ 8 + locJ₁₀ g x₀ * x ^ 10 + locJ₁₂ g x₀ * x ^ 12 := by
        rw [hx6, hx8, hx10, hx12]
        unfold locJ₆ locJ₈ locJ₁₀ locJ₁₂
        ring

/-- The even envelope of the `x⁴φ` remainder (from the shared expansion times `x²`). -/
noncomputable def locM₆ (g x₀ : ℝ) : ℝ := |locP₃ g x₀| + |locP₄ g x₀| / 2
noncomputable def locM₈ (g x₀ : ℝ) : ℝ := |locP₄ g x₀| / 2 + locH₆ g x₀

theorem locM₆_nonneg (g x₀ : ℝ) : 0 ≤ locM₆ g x₀ := by unfold locM₆; positivity
theorem locM₈_nonneg (g x₀ : ℝ) : 0 ≤ locM₈ g x₀ := by
  unfold locM₈; have := locH₆_nonneg g x₀; positivity

/-- `|x⁴φ − (x⁴ + ax⁵)| ≤ M₆x⁶ + M₈x⁸ + H₈x¹⁰ + H₁₀x¹²` (the signed `x⁵` kept exact). -/
theorem locQuartic_pointwise2 (hg : 0 ≤ g) (x : ℝ) :
    |x ^ 4 * locWeight g x₀ x - (x ^ 4 + g * x₀ * x ^ 5)| ≤
      locM₆ g x₀ * x ^ 6 + locM₈ g x₀ * x ^ 8 + locH₈ g x₀ * x ^ 10 + locH₁₀ g x₀ * x ^ 12 := by
  have hS := locSquare_pointwise (x₀ := x₀) hg x
  have e : x ^ 4 * locWeight g x₀ x - (x ^ 4 + g * x₀ * x ^ 5) =
      x ^ 2 * (x ^ 2 * locWeight g x₀ x -
        (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)) +
        (locP₃ g x₀ * x ^ 6 + locP₄ g x₀ * x ^ 7) := by ring
  have hx6 : x ^ 6 = |x| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hx8 : x ^ 8 = |x| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h7 : |x| ^ 7 ≤ (|x| ^ 6 + |x| ^ 8) / 2 := by nlinarith [sq_nonneg (|x| ^ 3 - |x| ^ 4)]
  have hH₆ := locH₆_nonneg g x₀
  have hH₈ := locH₈_nonneg g x₀
  have hH₁₀ := locH₁₀_nonneg g x₀
  have hx2 : (0 : ℝ) ≤ x ^ 2 := by positivity
  rw [e]
  calc |x ^ 2 * (x ^ 2 * locWeight g x₀ x -
          (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)) +
          (locP₃ g x₀ * x ^ 6 + locP₄ g x₀ * x ^ 7)|
      ≤ x ^ 2 * (locH₆ g x₀ * x ^ 6 + locH₈ g x₀ * x ^ 8 + locH₁₀ g x₀ * x ^ 10) +
          (|locP₃ g x₀| * |x| ^ 6 + |locP₄ g x₀| * |x| ^ 7) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hx2]
        gcongr
        calc |locP₃ g x₀ * x ^ 6 + locP₄ g x₀ * x ^ 7|
            ≤ |locP₃ g x₀ * x ^ 6| + |locP₄ g x₀ * x ^ 7| := abs_add_le _ _
          _ = |locP₃ g x₀| * |x| ^ 6 + |locP₄ g x₀| * |x| ^ 7 := by simp only [abs_mul, abs_pow]
    _ ≤ x ^ 2 * (locH₆ g x₀ * x ^ 6 + locH₈ g x₀ * x ^ 8 + locH₁₀ g x₀ * x ^ 10) +
          (|locP₃ g x₀| * |x| ^ 6 + |locP₄ g x₀| * ((|x| ^ 6 + |x| ^ 8) / 2)) := by gcongr
    _ = locM₆ g x₀ * x ^ 6 + locM₈ g x₀ * x ^ 8 + locH₈ g x₀ * x ^ 10 + locH₁₀ g x₀ * x ^ 12 := by
        rw [← hx6, ← hx8]
        unfold locM₆ locM₈
        ring

end Weight

/-! ### The expansions at the level of expectations -/

section Expansions

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `|⟨x²φ⟩ − (⟨x²⟩ + a⟨x³⟩ + p₃⟨x⁴⟩ + p₄⟨x⁵⟩)| ≤ H₆⟨x⁶⟩ + H₈⟨x⁸⟩ + H₁₀⟨x¹⁰⟩`. -/
theorem locSquare_expansion (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2 * locWeight g x₀ x) -
      (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locP₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5))| ≤
      locH₆ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locH₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) +
        locH₁₀ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 10) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 2
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht
  have hP : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locP₄ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) := by
    have e : (fun x : ℝ => x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5) =
        fun x => 1 * x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5 := by
      funext x; ring
    rw [e, gibbs_lin4 (hp 2) (hp 3) (hp 4) (hp 5)]
    ring
  have hPint : Integrable (fun x => (x ^ 2 + g * x₀ * x ^ 3 + locP₃ g x₀ * x ^ 4 +
      locP₄ g x₀ * x ^ 5) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (((hp 2).add ((hp 3).const_mul (g * x₀))).add ((hp 4).const_mul (locP₃ g x₀))).add
      ((hp 5).const_mul (locP₄ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hF : Integrable (fun x => (x ^ 2 * locWeight g x₀ x - (x ^ 2 + g * x₀ * x ^ 3 +
      locP₃ g x₀ * x ^ 4 + locP₄ g x₀ * x ^ 5)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hf.sub hPint).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locH₆ g x₀ * x ^ 6 + locH₈ g x₀ * x ^ 8 +
      locH₁₀ g x₀ * x ^ 10) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (((hp 6).const_mul (locH₆ g x₀)).add ((hp 8).const_mul (locH₈ g x₀))).add
      ((hp 10).const_mul (locH₁₀ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← hP, ← gibbs_sub' hf hPint, ← gibbs_lin3 (hp 6) (hp 8) (hp 10)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x =>
      locSquare_pointwise hg x)

/-- `|⟨x³φ⟩ − (⟨x³⟩ + a⟨x⁴⟩ + p₃⟨x⁵⟩)| ≤ J₆⟨x⁶⟩ + J₈⟨x⁸⟩ + J₁₀⟨x¹⁰⟩ + J₁₂⟨x¹²⟩`. -/
theorem locCubic_expansion2 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 3 * locWeight g x₀ x) -
      (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5))| ≤
      locJ₆ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locJ₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 8) +
        locJ₁₀ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 10) +
        locJ₁₂ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 12) := by
  have hZ := partition_pos' hlam hgamma hdisc ht
  have hf := integrable_pow_locWeight hlam hgamma hdisc hg ht (x₀ := x₀) 3
  have hp : ∀ k, Integrable (fun x : ℝ => x ^ k *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
    integrable_pow_exp' hlam hgamma hdisc ht
  have hP : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 3 + g * x₀ * x ^ 4 + locP₃ g x₀ * x ^ 5) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        locP₃ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) := by
    have e : (fun x : ℝ => x ^ 3 + g * x₀ * x ^ 4 + locP₃ g x₀ * x ^ 5) =
        fun x => 1 * x ^ 3 + g * x₀ * x ^ 4 + locP₃ g x₀ * x ^ 5 := by
      funext x; ring
    rw [e, gibbs_lin3 (hp 3) (hp 4) (hp 5)]
    ring
  have hPint : Integrable (fun x => (x ^ 3 + g * x₀ * x ^ 4 + locP₃ g x₀ * x ^ 5) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((hp 3).add ((hp 4).const_mul (g * x₀))).add ((hp 5).const_mul (locP₃ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hF : Integrable (fun x => (x ^ 3 * locWeight g x₀ x - (x ^ 3 + g * x₀ * x ^ 4 +
      locP₃ g x₀ * x ^ 5)) * Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hf.sub hPint).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locJ₆ g x₀ * x ^ 6 + locJ₈ g x₀ * x ^ 8 +
      locJ₁₀ g x₀ * x ^ 10 + locJ₁₂ g x₀ * x ^ 12) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((((hp 6).const_mul (locJ₆ g x₀)).add ((hp 8).const_mul (locJ₈ g x₀))).add
      ((hp 10).const_mul (locJ₁₀ g x₀))).add ((hp 12).const_mul (locJ₁₂ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← hP, ← gibbs_sub' hf hPint, ← gibbs_lin4 (hp 6) (hp 8) (hp 10) (hp 12)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x =>
      locCubic_pointwise2 hg x)

/-- `|⟨x⁴φ⟩ − (⟨x⁴⟩ + a⟨x⁵⟩)| ≤ M₆⟨x⁶⟩ + M₈⟨x⁸⟩ + H₈⟨x¹⁰⟩ + H₁₀⟨x¹²⟩`. -/
theorem locQuartic_expansion2 (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    |_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 4 * locWeight g x₀ x) -
      (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5))| ≤
      locM₆ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) +
        locM₈ g x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
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
      (fun x => x ^ 4 + g * x₀ * x ^ 5) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4) +
        g * x₀ * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) := by
    have h5 : Integrable (fun x => (g * x₀ * x ^ 5) *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
      ((hp 5).const_mul (g * x₀)).congr (Eventually.of_forall fun x => by dsimp only; ring)
    rw [gibbs_add' (hp 4) h5, gibbsExpectation_const_mul₁]
  have hPint : Integrable (fun x => (x ^ 4 + g * x₀ * x ^ 5) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := (hp 4).add ((hp 5).const_mul (g * x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hF : Integrable (fun x => (x ^ 4 * locWeight g x₀ x - (x ^ 4 + g * x₀ * x ^ 5)) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    refine (hf.sub hPint).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hG : Integrable (fun x => (locM₆ g x₀ * x ^ 6 + locM₈ g x₀ * x ^ 8 +
      locH₈ g x₀ * x ^ 10 + locH₁₀ g x₀ * x ^ 12) *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    have := ((((hp 6).const_mul (locM₆ g x₀)).add ((hp 8).const_mul (locM₈ g x₀))).add
      ((hp 10).const_mul (locH₈ g x₀))).add ((hp 12).const_mul (locH₁₀ g x₀))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  rw [← hP, ← gibbs_sub' hf hPint, ← gibbs_lin4 (hp 6) (hp 8) (hp 10) (hp 12)]
  exact (abs_gibbsExpectation_le' hZ _).trans
    (gibbsExpectation_mono' hZ (integrable_abs_weighted hF) hG fun x =>
      locQuartic_pointwise2 hg x)

end Expansions

/-! ### Coefficients and abstract assembly lemmas -/

section Coeffs

/-- `n₂ = B₂ + a c₃ + 3p₃/λ²`: the `1/t` coefficient of `t⟨x²φ⟩`. -/
noncomputable def locN2 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / lam +
    g * x₀ * (-(5 * alpha / (2 * lam ^ 3))) + 3 * locP₃ g x₀ / lam ^ 2

/-- `c₂' = n₂ − d₁/λ`: the `1/t` coefficient of `t⟨x²⟩_loc`. -/
noncomputable def locSecondCoeff2 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  locN2 lam alpha gamma g x₀ - locD1 lam alpha g x₀ / lam

/-- `c₃ + 3a/λ²`: the leading coefficient of `t²⟨x³⟩_loc`. -/
noncomputable def locThirdCoeff (lam alpha g x₀ : ℝ) : ℝ :=
  -(5 * alpha / (2 * lam ^ 3)) + 3 * (g * x₀) / lam ^ 2

/-- The unlocalised first energy correction `e₀ = 5α²/(24λ³) − γ/(8λ²)`. -/
noncomputable def energyCoeff1 (lam alpha gamma : ℝ) : ℝ :=
  5 * alpha ^ 2 / (24 * lam ^ 3) - gamma / (8 * lam ^ 2)

/-- The localised first energy correction `e₁ = (λ/2)c₂' + (α/6)(c₃ + 3a/λ²) + (γ/24)(3/λ²)`. -/
noncomputable def energyLocCoeff1 (lam alpha gamma g x₀ : ℝ) : ℝ :=
  lam / 2 * locSecondCoeff2 lam alpha gamma g x₀ + alpha / 6 * locThirdCoeff lam alpha g x₀ +
    gamma / 24 * (3 / lam ^ 2)

theorem locD1_eq (lam alpha g x₀ : ℝ) (hlam : 0 < lam) :
    locD1 lam alpha g x₀ = ((g * x₀) ^ 2 - g) / (2 * lam) - g * x₀ * alpha / (2 * lam ^ 2) := by
  unfold locD1 locP₃
  field_simp
  ring

/-- The closed form `e₁ = (a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)`. -/
theorem energyLocCoeff1_eq (lam alpha gamma g x₀ : ℝ) (hlam : 0 < lam) :
    energyLocCoeff1 lam alpha gamma g x₀ =
      ((g * x₀) ^ 2 - g) / (2 * lam) - g * x₀ * alpha / (2 * lam ^ 2) - gamma / (8 * lam ^ 2) +
        5 * alpha ^ 2 / (24 * lam ^ 3) := by
  unfold energyLocCoeff1 locSecondCoeff2 locN2 locThirdCoeff locD1 locP₃
  field_simp
  ring

/-- **`e₁ = e₀ + d₁`**: the localiser shifts the first energy correction by the `1/t` coefficient
of `⟨φ⟩` (the energy being the negative logarithmic `t`-derivative of the partition function). -/
theorem energyLocCoeff1_eq_add (lam alpha gamma g x₀ : ℝ) (hlam : 0 < lam) :
    energyLocCoeff1 lam alpha gamma g x₀ =
      energyCoeff1 lam alpha gamma + locD1 lam alpha g x₀ := by
  rw [energyLocCoeff1_eq lam alpha gamma g x₀ hlam, locD1_eq lam alpha g x₀ hlam]
  unfold energyCoeff1
  ring

/-- At the anchor at the minimum, `d₁ = −g/(2λ)`: the localiser lowers the first correction. -/
theorem locD1_anchor_zero (lam alpha g : ℝ) (hlam : 0 < lam) :
    locD1 lam alpha g 0 = -(g / (2 * lam)) := by
  rw [locD1_eq lam alpha g 0 hlam]
  ring

/-- The residual against the trace prediction: `e₁ + g/(2λ) = e₀ + a²/(2λ) − aα/(2λ²)`. -/
theorem energyLocCoeff1_add_eq (lam alpha gamma g x₀ : ℝ) (hlam : 0 < lam) :
    energyLocCoeff1 lam alpha gamma g x₀ + g / (2 * lam) =
      energyCoeff1 lam alpha gamma + (g * x₀) ^ 2 / (2 * lam) -
        g * x₀ * alpha / (2 * lam ^ 2) := by
  rw [energyLocCoeff1_eq lam alpha gamma g x₀ hlam]
  unfold energyCoeff1
  field_simp
  ring

/-- The unlocalised assembly identity: `(λ/2)B₂ + (α/6)c₃ + (γ/24)(3/λ²) = e₀`. -/
theorem energyCoeff1_eq (lam alpha gamma : ℝ) (hlam : 0 < lam) :
    lam / 2 * ((5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / lam) +
        alpha / 6 * (-(5 * alpha / (2 * lam ^ 3))) + gamma / 24 * (3 / lam ^ 2) =
      energyCoeff1 lam alpha gamma := by
  unfold energyCoeff1
  field_simp
  ring

/-- The trace prediction's scalar remainder: `½tλ/(tλ + g) − ½ + g/(2λt) = g²/(2λt(tλ + g))`. -/
theorem trace_scalar_remainder (lam g t : ℝ) (hlam : 0 < lam) (hg : 0 ≤ g) (ht : 0 < t) :
    |1 / 2 * (t * lam / (t * lam + g)) - 1 / 2 + g / (2 * lam) / t| ≤
      g ^ 2 / (2 * lam ^ 2) / t ^ 2 := by
  have hpos : 0 < t * lam + g := by positivity
  have e : 1 / 2 * (t * lam / (t * lam + g)) - 1 / 2 + g / (2 * lam) / t =
      g ^ 2 / (2 * lam * t * (t * lam + g)) := by
    field_simp
    ring
  rw [e, abs_of_nonneg (by positivity), div_div]
  apply div_le_div_of_nonneg_left (sq_nonneg g) (by positivity)
  nlinarith [mul_nonneg (mul_nonneg hlam.le ht.le) hg]

/-- The second moment's key identity (abstract reals). -/
theorem locSquare_key (lam alpha gamma g x₀ t N M₂ M₃ M₄ M₅ : ℝ) (hlam : lam ≠ 0) (ht : t ≠ 0) :
    t * N - 1 / lam - locN2 lam alpha gamma g x₀ / t =
      (t * M₂ - 1 / lam - (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)) +
        g * x₀ * ((t ^ 2 * M₃ - -(5 * alpha / (2 * lam ^ 3))) / t) +
        locP₃ g x₀ * ((t ^ 2 * M₄ - 3 / lam ^ 2) / t) +
        locP₄ g x₀ * (t ^ 3 * M₅ / t ^ 2) +
        t * (N - (M₂ + g * x₀ * M₃ + locP₃ g x₀ * M₄ + locP₄ g x₀ * M₅)) := by
  unfold locN2
  field_simp
  ring

/-- The second moment's assembly (abstract reals). -/
theorem locSquare_assembly (lam alpha gamma g x₀ t N M₂ M₃ M₄ M₅ K₂ K₃ K₄ K₅' KR : ℝ)
    (hlam : 0 < lam) (ht1 : 1 ≤ t)
    (e₂ : |t * M₂ - 1 / lam - (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)|
      ≤ K₂ / t ^ 2)
    (e₃ : |t ^ 2 * M₃ - -(5 * alpha / (2 * lam ^ 3))| ≤ K₃ / t)
    (e₄ : |t ^ 2 * M₄ - 3 / lam ^ 2| ≤ K₄ / t)
    (e₅ : |t ^ 3 * M₅| ≤ K₅')
    (hR : |N - (M₂ + g * x₀ * M₃ + locP₃ g x₀ * M₄ + locP₄ g x₀ * M₅)| ≤ KR / t ^ 3) :
    |t * N - 1 / lam - locN2 lam alpha gamma g x₀ / t| ≤
      (K₂ + |g * x₀| * K₃ + |locP₃ g x₀| * K₄ + |locP₄ g x₀| * K₅' + KR) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  rw [locSquare_key lam alpha gamma g x₀ t N M₂ M₃ M₄ M₅ hlam.ne' ht0.ne']
  have b₃ : |g * x₀ * ((t ^ 2 * M₃ - -(5 * alpha / (2 * lam ^ 3))) / t)| ≤
      |g * x₀| * (K₃ / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ K₃ / t / t := div_le_div_of_nonneg_right e₃ ht0.le
      _ = K₃ / t ^ 2 := by ring
  have b₄ : |locP₃ g x₀ * ((t ^ 2 * M₄ - 3 / lam ^ 2) / t)| ≤ |locP₃ g x₀| * (K₄ / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ K₄ / t / t := div_le_div_of_nonneg_right e₄ ht0.le
      _ = K₄ / t ^ 2 := by ring
  have b₅ : |locP₄ g x₀ * (t ^ 3 * M₅ / t ^ 2)| ≤ |locP₄ g x₀| * (K₅' / t ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₅ (by positivity)) (abs_nonneg _)
  have bR : |t * (N - (M₂ + g * x₀ * M₃ + locP₃ g x₀ * M₄ + locP₄ g x₀ * M₅))| ≤ KR / t ^ 2 := by
    rw [abs_mul, abs_of_pos ht0]
    calc t * |N - (M₂ + g * x₀ * M₃ + locP₃ g x₀ * M₄ + locP₄ g x₀ * M₅)|
        ≤ t * (KR / t ^ 3) := mul_le_mul_of_nonneg_left hR ht0.le
      _ = KR / t ^ 2 := by field_simp
  calc _ ≤ K₂ / t ^ 2 + |g * x₀| * (K₃ / t ^ 2) + |locP₃ g x₀| * (K₄ / t ^ 2) +
        |locP₄ g x₀| * (K₅' / t ^ 2) + KR / t ^ 2 := by
        refine (abs_add_le _ _).trans (add_le_add ?_ bR)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₅)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₄)
        exact (abs_add_le _ _).trans (add_le_add e₂ b₃)
    _ = _ := by ring

/-- The third moment's assembly (abstract reals): `|t²N − (c₃ + 3a/λ²)| ≤ K/t`. -/
theorem locCubic_assembly (lam alpha g x₀ t N M₃ M₄ M₅ K₃ K₄ K₅' KR : ℝ) (hlam : 0 < lam)
    (ht1 : 1 ≤ t)
    (e₃ : |t ^ 2 * M₃ - -(5 * alpha / (2 * lam ^ 3))| ≤ K₃ / t)
    (e₄ : |t ^ 2 * M₄ - 3 / lam ^ 2| ≤ K₄ / t)
    (e₅ : |t ^ 3 * M₅| ≤ K₅')
    (hR : |N - (M₃ + g * x₀ * M₄ + locP₃ g x₀ * M₅)| ≤ KR / t ^ 3) :
    |t ^ 2 * N - locThirdCoeff lam alpha g x₀| ≤
      (K₃ + |g * x₀| * K₄ + |locP₃ g x₀| * K₅' + KR) / t := by
  have ht0 : 0 < t := by linarith
  have key : t ^ 2 * N - locThirdCoeff lam alpha g x₀ =
      (t ^ 2 * M₃ - -(5 * alpha / (2 * lam ^ 3))) + g * x₀ * (t ^ 2 * M₄ - 3 / lam ^ 2) +
        locP₃ g x₀ * (t ^ 3 * M₅ / t) +
        t ^ 2 * (N - (M₃ + g * x₀ * M₄ + locP₃ g x₀ * M₅)) := by
    unfold locThirdCoeff
    field_simp
    ring
  rw [key]
  have b₄ : |g * x₀ * (t ^ 2 * M₄ - 3 / lam ^ 2)| ≤ |g * x₀| * (K₄ / t) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e₄ (abs_nonneg _)
  have b₅ : |locP₃ g x₀ * (t ^ 3 * M₅ / t)| ≤ |locP₃ g x₀| * (K₅' / t) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₅ ht0.le) (abs_nonneg _)
  have bR : |t ^ 2 * (N - (M₃ + g * x₀ * M₄ + locP₃ g x₀ * M₅))| ≤ KR / t := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    calc t ^ 2 * |N - (M₃ + g * x₀ * M₄ + locP₃ g x₀ * M₅)| ≤ t ^ 2 * (KR / t ^ 3) :=
          mul_le_mul_of_nonneg_left hR (by positivity)
      _ = KR / t := by field_simp
  calc _ ≤ K₃ / t + |g * x₀| * (K₄ / t) + |locP₃ g x₀| * (K₅' / t) + KR / t := by
        refine (abs_add_le _ _).trans (add_le_add ?_ bR)
        refine (abs_add_le _ _).trans (add_le_add ?_ b₅)
        exact (abs_add_le _ _).trans (add_le_add e₃ b₄)
    _ = _ := by ring

/-- The fourth moment's assembly (abstract reals): `|t²N − 3/λ²| ≤ K/t`. -/
theorem locQuartic_assembly (lam g x₀ t N M₄ M₅ K₄ K₅' KR : ℝ) (ht1 : 1 ≤ t)
    (e₄ : |t ^ 2 * M₄ - 3 / lam ^ 2| ≤ K₄ / t)
    (e₅ : |t ^ 3 * M₅| ≤ K₅')
    (hR : |N - (M₄ + g * x₀ * M₅)| ≤ KR / t ^ 3) :
    |t ^ 2 * N - 3 / lam ^ 2| ≤ (K₄ + |g * x₀| * K₅' + KR) / t := by
  have ht0 : 0 < t := by linarith
  have key : t ^ 2 * N - 3 / lam ^ 2 =
      (t ^ 2 * M₄ - 3 / lam ^ 2) + g * x₀ * (t ^ 3 * M₅ / t) +
        t ^ 2 * (N - (M₄ + g * x₀ * M₅)) := by
    field_simp
    ring
  rw [key]
  have b₅ : |g * x₀ * (t ^ 3 * M₅ / t)| ≤ |g * x₀| * (K₅' / t) := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e₅ ht0.le) (abs_nonneg _)
  have bR : |t ^ 2 * (N - (M₄ + g * x₀ * M₅))| ≤ KR / t := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    calc t ^ 2 * |N - (M₄ + g * x₀ * M₅)| ≤ t ^ 2 * (KR / t ^ 3) :=
          mul_le_mul_of_nonneg_left hR (by positivity)
      _ = KR / t := by field_simp
  calc _ ≤ K₄ / t + |g * x₀| * (K₅' / t) + KR / t := by
        refine (abs_add_le _ _).trans (add_le_add ?_ bR)
        exact (abs_add_le _ _).trans (add_le_add e₄ b₅)
    _ = _ := by ring

/-- Dividing a leading-order rate by `D = 1 + O(1/t)`: `t²(N/D) − c = ((t²N − c) − c(D − 1))/D`. -/
theorem ratio_lead_key (t N D c : ℝ) (hD : D ≠ 0) :
    t ^ 2 * (N / D) - c = ((t ^ 2 * N - c) - c * (D - 1)) / D := by
  field_simp
  ring

/-- The energy's assembly (abstract reals), shared by the localised and unlocalised energies. -/
theorem energy_assembly (lam alpha gamma t M₂ M₃ M₄ c₂' c₃' K₂ K₃ K₄ : ℝ) (hlam : 0 < lam)
    (hgamma : 0 < gamma) (ht1 : 1 ≤ t)
    (e₂ : |t * M₂ - 1 / lam - c₂' / t| ≤ K₂ / t ^ 2)
    (e₃ : |t ^ 2 * M₃ - c₃'| ≤ K₃ / t)
    (e₄ : |t ^ 2 * M₄ - 3 / lam ^ 2| ≤ K₄ / t) :
    |t * (lam / 2 * M₂ + alpha / 6 * M₃ + gamma / 24 * M₄) - 1 / 2 -
        (lam / 2 * c₂' + alpha / 6 * c₃' + gamma / 24 * (3 / lam ^ 2)) / t| ≤
      (lam / 2 * K₂ + |alpha| / 6 * K₃ + gamma / 24 * K₄) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have key : t * (lam / 2 * M₂ + alpha / 6 * M₃ + gamma / 24 * M₄) - 1 / 2 -
      (lam / 2 * c₂' + alpha / 6 * c₃' + gamma / 24 * (3 / lam ^ 2)) / t =
      lam / 2 * (t * M₂ - 1 / lam - c₂' / t) + alpha / 6 * ((t ^ 2 * M₃ - c₃') / t) +
        gamma / 24 * ((t ^ 2 * M₄ - 3 / lam ^ 2) / t) := by
    field_simp
    ring
  rw [key]
  have b₃ : |alpha / 6 * ((t ^ 2 * M₃ - c₃') / t)| ≤ |alpha| / 6 * (K₃ / t ^ 2) := by
    rw [abs_mul, abs_div alpha, abs_of_pos (by norm_num : (0 : ℝ) < 6),
      abs_div (t ^ 2 * M₃ - c₃'), abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ K₃ / t / t := div_le_div_of_nonneg_right e₃ ht0.le
      _ = K₃ / t ^ 2 := by ring
  have b₄ : |gamma / 24 * ((t ^ 2 * M₄ - 3 / lam ^ 2) / t)| ≤ gamma / 24 * (K₄ / t ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 24),
      abs_div (t ^ 2 * M₄ - 3 / lam ^ 2), abs_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ K₄ / t / t := div_le_div_of_nonneg_right e₄ ht0.le
      _ = K₄ / t ^ 2 := by ring
  have b₂ : |lam / 2 * (t * M₂ - 1 / lam - c₂' / t)| ≤ lam / 2 * (K₂ / t ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam / 2)]
    exact mul_le_mul_of_nonneg_left e₂ (by positivity)
  calc _ ≤ lam / 2 * (K₂ / t ^ 2) + |alpha| / 6 * (K₃ / t ^ 2) + gamma / 24 * (K₄ / t ^ 2) :=
        (abs_add_three _ _ _).trans (add_le_add (add_le_add b₂ b₃) b₄)
    _ = _ := by ring

end Coeffs

/-! ### The rates -/

section Rates

variable {lam alpha gamma g x₀ : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- **The weighted second moment to second order**: `|t⟨x²φ⟩ − 1/λ − n₂/t| ≤ K/t²`. -/
theorem locSquare_rate2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2 * locWeight g x₀ x) - 1 / lam -
        locN2 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ :=
    Laplace.OneD.secondMoment_anharmonic_order3_rate hlam hgamma hdisc
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := thirdMoment_lead hlam hgamma hdisc
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_lead hlam hgamma hdisc
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  obtain ⟨C₁₀, T₁₀, hC₁₀, hT₁₀, h₁₀⟩ := evenMoment_bound hlam hgamma hdisc 5
  simp only [show (2 * 3 : ℕ) = 6 from rfl, show (2 * 4 : ℕ) = 8 from rfl,
    show (2 * 5 : ℕ) = 10 from rfl] at h₆ h₈ h₁₀
  have hH₆ := locH₆_nonneg g x₀
  have hH₈ := locH₈_nonneg g x₀
  have hH₁₀ := locH₁₀_nonneg g x₀
  have hKR0 : 0 ≤ locH₆ g x₀ * C₆ + locH₈ g x₀ * C₈ + locH₁₀ g x₀ * C₁₀ := by positivity
  have hK₅'0 : 0 ≤ |-(35 * alpha / (2 * lam ^ 4))| + K₅ := by positivity
  have h1T : (1 : ℝ) ≤ T₂ + T₃ + T₄ + T₅ + T₆ + T₈ + T₁₀ := by linarith
  refine ⟨K₂ + |g * x₀| * K₃ + |locP₃ g x₀| * K₄ +
      |locP₄ g x₀| * (|-(35 * alpha / (2 * lam ^ 4))| + K₅) +
      (locH₆ g x₀ * C₆ + locH₈ g x₀ * C₈ + locH₁₀ g x₀ * C₁₀),
    T₂ + T₃ + T₄ + T₅ + T₆ + T₈ + T₁₀, by positivity, h1T, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have e₂ := h₂ (t := t) (by linarith)
  rw [secondMoment_coeff_eq hlam] at e₂
  have hR := (locSquare_expansion hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h₆ (t := t) (by linarith)) hH₆)
      (mul_le_mul_of_nonneg_left (h₈ (t := t) (by linarith)) hH₈))
      (mul_le_mul_of_nonneg_left (h₁₀ (t := t) (by linarith)) hH₁₀))
  have hRt : locH₆ g x₀ * (C₆ / t ^ 3) + locH₈ g x₀ * (C₈ / t ^ 4) +
      locH₁₀ g x₀ * (C₁₀ / t ^ 5) ≤
      (locH₆ g x₀ * C₆ + locH₈ g x₀ * C₈ + locH₁₀ g x₀ * C₁₀) / t ^ 3 := by
    have h8 : locH₈ g x₀ * (C₈ / t ^ 4) ≤ locH₈ g x₀ * (C₈ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₈ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hH₈
    have h10 : locH₁₀ g x₀ * (C₁₀ / t ^ 5) ≤ locH₁₀ g x₀ * (C₁₀ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₀ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hH₁₀
    have e : (locH₆ g x₀ * C₆ + locH₈ g x₀ * C₈ + locH₁₀ g x₀ * C₁₀) / t ^ 3 =
        locH₆ g x₀ * (C₆ / t ^ 3) + locH₈ g x₀ * (C₈ / t ^ 3) + locH₁₀ g x₀ * (C₁₀ / t ^ 3) := by
      ring
    rw [e]
    linarith
  exact locSquare_assembly lam alpha gamma g x₀ t
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 2 * locWeight g x₀ x))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 2))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5))
    K₂ K₃ K₄ (|-(35 * alpha / (2 * lam ^ 4))| + K₅)
    (locH₆ g x₀ * C₆ + locH₈ g x₀ * C₈ + locH₁₀ g x₀ * C₁₀) hlam ht1
    e₂ (h₃ (t := t) (by linarith)) (h₄ (t := t) (by linarith))
    (Laplace.OneD.rate_bounded ht1 hK₅ (h₅ (t := t) (by linarith))) (hR.trans hRt)

/-- **The weighted third moment at leading order**: `|t²⟨x³φ⟩ − (c₃ + 3a/λ²)| ≤ K/t`. -/
theorem locCubic_rate2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3 * locWeight g x₀ x) - locThirdCoeff lam alpha g x₀| ≤ K / t := by
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := thirdMoment_lead hlam hgamma hdisc
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_lead hlam hgamma hdisc
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  obtain ⟨C₁₀, T₁₀, hC₁₀, hT₁₀, h₁₀⟩ := evenMoment_bound hlam hgamma hdisc 5
  obtain ⟨C₁₂, T₁₂, hC₁₂, hT₁₂, h₁₂⟩ := evenMoment_bound hlam hgamma hdisc 6
  simp only [show (2 * 3 : ℕ) = 6 from rfl, show (2 * 4 : ℕ) = 8 from rfl,
    show (2 * 5 : ℕ) = 10 from rfl, show (2 * 6 : ℕ) = 12 from rfl] at h₆ h₈ h₁₀ h₁₂
  have hJ₆ := locJ₆_nonneg g x₀
  have hJ₈ := locJ₈_nonneg g x₀
  have hJ₁₀ := locJ₁₀_nonneg g x₀
  have hJ₁₂ := locJ₁₂_nonneg g x₀
  have hKR0 : 0 ≤ locJ₆ g x₀ * C₆ + locJ₈ g x₀ * C₈ + locJ₁₀ g x₀ * C₁₀ + locJ₁₂ g x₀ * C₁₂ := by
    positivity
  have hK₅'0 : 0 ≤ |-(35 * alpha / (2 * lam ^ 4))| + K₅ := by positivity
  have h1T : (1 : ℝ) ≤ T₃ + T₄ + T₅ + T₆ + T₈ + T₁₀ + T₁₂ := by linarith
  refine ⟨K₃ + |g * x₀| * K₄ + |locP₃ g x₀| * (|-(35 * alpha / (2 * lam ^ 4))| + K₅) +
      (locJ₆ g x₀ * C₆ + locJ₈ g x₀ * C₈ + locJ₁₀ g x₀ * C₁₀ + locJ₁₂ g x₀ * C₁₂),
    T₃ + T₄ + T₅ + T₆ + T₈ + T₁₀ + T₁₂, by positivity, h1T, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hR := (locCubic_expansion2 hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h₆ (t := t) (by linarith)) hJ₆)
      (mul_le_mul_of_nonneg_left (h₈ (t := t) (by linarith)) hJ₈))
      (mul_le_mul_of_nonneg_left (h₁₀ (t := t) (by linarith)) hJ₁₀))
      (mul_le_mul_of_nonneg_left (h₁₂ (t := t) (by linarith)) hJ₁₂))
  have hRt : locJ₆ g x₀ * (C₆ / t ^ 3) + locJ₈ g x₀ * (C₈ / t ^ 4) +
      locJ₁₀ g x₀ * (C₁₀ / t ^ 5) + locJ₁₂ g x₀ * (C₁₂ / t ^ 6) ≤
      (locJ₆ g x₀ * C₆ + locJ₈ g x₀ * C₈ + locJ₁₀ g x₀ * C₁₀ + locJ₁₂ g x₀ * C₁₂) / t ^ 3 := by
    have h8 : locJ₈ g x₀ * (C₈ / t ^ 4) ≤ locJ₈ g x₀ * (C₈ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₈ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hJ₈
    have h10 : locJ₁₀ g x₀ * (C₁₀ / t ^ 5) ≤ locJ₁₀ g x₀ * (C₁₀ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₀ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hJ₁₀
    have h12 : locJ₁₂ g x₀ * (C₁₂ / t ^ 6) ≤ locJ₁₂ g x₀ * (C₁₂ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₂ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hJ₁₂
    have e : (locJ₆ g x₀ * C₆ + locJ₈ g x₀ * C₈ + locJ₁₀ g x₀ * C₁₀ + locJ₁₂ g x₀ * C₁₂) / t ^ 3 =
        locJ₆ g x₀ * (C₆ / t ^ 3) + locJ₈ g x₀ * (C₈ / t ^ 3) + locJ₁₀ g x₀ * (C₁₀ / t ^ 3) +
          locJ₁₂ g x₀ * (C₁₂ / t ^ 3) := by ring
    rw [e]
    linarith
  exact locCubic_assembly lam alpha g x₀ t
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 3 * locWeight g x₀ x))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 3))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5))
    K₃ K₄ (|-(35 * alpha / (2 * lam ^ 4))| + K₅)
    (locJ₆ g x₀ * C₆ + locJ₈ g x₀ * C₈ + locJ₁₀ g x₀ * C₁₀ + locJ₁₂ g x₀ * C₁₂) hlam ht1
    (h₃ (t := t) (by linarith)) (h₄ (t := t) (by linarith))
    (Laplace.OneD.rate_bounded ht1 hK₅ (h₅ (t := t) (by linarith))) (hR.trans hRt)

/-- **The weighted fourth moment at leading order**: `|t²⟨x⁴φ⟩ − 3/λ²| ≤ K/t`. -/
theorem locQuartic_rate2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4 * locWeight g x₀ x) - 3 / lam ^ 2| ≤ K / t := by
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_lead hlam hgamma hdisc
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨C₆, T₆, hC₆, hT₆, h₆⟩ := evenMoment_bound hlam hgamma hdisc 3
  obtain ⟨C₈, T₈, hC₈, hT₈, h₈⟩ := evenMoment_bound hlam hgamma hdisc 4
  obtain ⟨C₁₀, T₁₀, hC₁₀, hT₁₀, h₁₀⟩ := evenMoment_bound hlam hgamma hdisc 5
  obtain ⟨C₁₂, T₁₂, hC₁₂, hT₁₂, h₁₂⟩ := evenMoment_bound hlam hgamma hdisc 6
  simp only [show (2 * 3 : ℕ) = 6 from rfl, show (2 * 4 : ℕ) = 8 from rfl,
    show (2 * 5 : ℕ) = 10 from rfl, show (2 * 6 : ℕ) = 12 from rfl] at h₆ h₈ h₁₀ h₁₂
  have hM₆ := locM₆_nonneg g x₀
  have hM₈ := locM₈_nonneg g x₀
  have hH₈ := locH₈_nonneg g x₀
  have hH₁₀ := locH₁₀_nonneg g x₀
  have hKR0 : 0 ≤ locM₆ g x₀ * C₆ + locM₈ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂ := by
    positivity
  have hK₅'0 : 0 ≤ |-(35 * alpha / (2 * lam ^ 4))| + K₅ := by positivity
  have h1T : (1 : ℝ) ≤ T₄ + T₅ + T₆ + T₈ + T₁₀ + T₁₂ := by linarith
  refine ⟨K₄ + |g * x₀| * (|-(35 * alpha / (2 * lam ^ 4))| + K₅) +
      (locM₆ g x₀ * C₆ + locM₈ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂),
    T₄ + T₅ + T₆ + T₈ + T₁₀ + T₁₂, by positivity, h1T, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hR := (locQuartic_expansion2 hlam hgamma hdisc hg ht0 (x₀ := x₀)).trans
    (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h₆ (t := t) (by linarith)) hM₆)
      (mul_le_mul_of_nonneg_left (h₈ (t := t) (by linarith)) hM₈))
      (mul_le_mul_of_nonneg_left (h₁₀ (t := t) (by linarith)) hH₈))
      (mul_le_mul_of_nonneg_left (h₁₂ (t := t) (by linarith)) hH₁₀))
  have hRt : locM₆ g x₀ * (C₆ / t ^ 3) + locM₈ g x₀ * (C₈ / t ^ 4) +
      locH₈ g x₀ * (C₁₀ / t ^ 5) + locH₁₀ g x₀ * (C₁₂ / t ^ 6) ≤
      (locM₆ g x₀ * C₆ + locM₈ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂) / t ^ 3 := by
    have h8 : locM₈ g x₀ * (C₈ / t ^ 4) ≤ locM₈ g x₀ * (C₈ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₈ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hM₈
    have h10 : locH₈ g x₀ * (C₁₀ / t ^ 5) ≤ locH₈ g x₀ * (C₁₀ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₀ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hH₈
    have h12 : locH₁₀ g x₀ * (C₁₂ / t ^ 6) ≤ locH₁₀ g x₀ * (C₁₂ / t ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC₁₂ (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num))) hH₁₀
    have e : (locM₆ g x₀ * C₆ + locM₈ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂) / t ^ 3 =
        locM₆ g x₀ * (C₆ / t ^ 3) + locM₈ g x₀ * (C₈ / t ^ 3) + locH₈ g x₀ * (C₁₀ / t ^ 3) +
          locH₁₀ g x₀ * (C₁₂ / t ^ 3) := by ring
    rw [e]
    linarith
  exact locQuartic_assembly lam g x₀ t
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x ^ 4 * locWeight g x₀ x))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 4))
    (_root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5))
    K₄ (|-(35 * alpha / (2 * lam ^ 4))| + K₅)
    (locM₆ g x₀ * C₆ + locM₈ g x₀ * C₈ + locH₈ g x₀ * C₁₀ + locH₁₀ g x₀ * C₁₂) ht1
    (h₄ (t := t) (by linarith))
    (Laplace.OneD.rate_bounded ht1 hK₅ (h₅ (t := t) (by linarith))) (hR.trans hRt)

/-- **The localised second moment to second order**: `|t⟨x²⟩_loc − 1/λ − c₂'/t| ≤ K/t²`. -/
theorem locSecondMoment_loc_rate2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 2) - 1 / lam - locSecondCoeff2 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨KN, TN, hKN, hTN, hN⟩ := locSquare_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨KD, TD, hKD, hTD, hD⟩ := locDenominator_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  set c : ℝ := 1 / lam with hc
  set c' := locSecondCoeff2 lam alpha gamma g x₀ with hc'
  set d₁ := locD1 lam alpha g x₀ with hd₁
  set n₁ := locN2 lam alpha gamma g x₀ with hn₁
  have hn₁e : n₁ = c' + c * d₁ := by
    rw [hc', locSecondCoeff2, hc]
    ring
  have hd₁0 : 0 ≤ |d₁| := abs_nonneg d₁
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hc'0 : 0 ≤ |c'| := abs_nonneg c'
  have hTD0 : 0 ≤ TD := by linarith
  have hTN0 : 0 ≤ TN := by linarith
  have h1T : (1 : ℝ) ≤ TN + TD + 2 * (|d₁| + KD) := by linarith
  refine ⟨2 * (KN + |c| * KD + |c'| * |d₁| + |c'| * KD), TN + TD + 2 * (|d₁| + KD),
    by positivity, h1T, fun {t} ht => ?_⟩
  have hTNt : TN ≤ t := by linarith
  have hTDt : TD ≤ t := by linarith
  have h2 : 2 * (|d₁| + KD) ≤ t := by linarith
  have ht1 : 1 ≤ t := hTN.trans hTNt
  have ht0 : 0 < t := by linarith
  rw [gibbsExpectation_locPotential1 hlam hgamma hdisc ht0]
  have eN := hN hTNt
  have eD := hD hTDt
  set N := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2 * locWeight g x₀ x) with hNdef
  set D := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (locWeight g x₀) with hDdef
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
  rw [ratio_key t N D c c' d₁ n₁ hn₁e ht0.ne' hD0.ne', abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  have h3 : |c' * d₁ / t ^ 2| = |c'| * |d₁| / t ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  have h4 : |c' / t * (D - 1 - d₁ / t)| ≤ |c'| * KD / t ^ 2 := by
    rw [abs_mul, abs_div, abs_of_pos ht0]
    calc |c'| / t * |D - 1 - d₁ / t| ≤ |c'| / t * (KD / t ^ 2) := by gcongr
      _ = (|c'| * KD / t ^ 2) / t := by ring
      _ ≤ |c'| * KD / t ^ 2 := div_le_self (by positivity) ht1
  calc |(t * N - c - n₁ / t) - c * (D - 1 - d₁ / t) - c' * d₁ / t ^ 2 -
        c' / t * (D - 1 - d₁ / t)|
      ≤ |t * N - c - n₁ / t| + |c * (D - 1 - d₁ / t)| + |c' * d₁ / t ^ 2| +
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

/-- Dividing a weighted leading-order rate by the denominator (`|D − 1| ≤ KD/t`, `D ≥ ½`). -/
theorem loc_ratio_lead_rate (c : ℝ) (f : ℝ → ℝ) (hg : 0 ≤ g)
    (hN : ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => f x * locWeight g x₀ x) - c| ≤ K / t) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t f - c| ≤
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
  rw [ratio_lead_key t N D c hD0.ne', abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  calc |(t ^ 2 * N - c) - c * (D - 1)| ≤ |t ^ 2 * N - c| + |c * (D - 1)| := abs_sub _ _
    _ ≤ KN / t + |c| * (KD / t) := by
        rw [abs_mul]
        gcongr
    _ = 2 * (KN + |c| * KD) / t * (1 / 2) := by ring
    _ ≤ 2 * (KN + |c| * KD) / t * D := by gcongr

/-- **The localised third moment at leading order**: `|t²⟨x³⟩_loc − (c₃ + 3a/λ²)| ≤ K/t`. -/
theorem locThirdMoment_loc_rate2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 3) - locThirdCoeff lam alpha g x₀| ≤ K / t :=
  loc_ratio_lead_rate hlam hgamma hdisc _ (fun x => x ^ 3) hg
    (locCubic_rate2 hlam hgamma hdisc hg (x₀ := x₀))

/-- **The localised fourth moment at leading order**: `|t²⟨x⁴⟩_loc − 3/λ²| ≤ K/t`. -/
theorem locFourthMoment_loc_rate2 (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (fun x => x ^ 4) - 3 / lam ^ 2| ≤ K / t :=
  loc_ratio_lead_rate hlam hgamma hdisc _ (fun x => x ^ 4) hg
    (locQuartic_rate2 hlam hgamma hdisc hg (x₀ := x₀))

/-- **The localised energy to second order (A)**: `|t⟨ℓ⟩_loc − ½ − e₁/t| ≤ K/t²`. -/
theorem localisedEnergy_order2_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) - 1 / 2 -
        energyLocCoeff1 lam alpha gamma g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := locSecondMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := locThirdMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := locFourthMoment_loc_rate2 hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨lam / 2 * K₂ + |alpha| / 6 * K₃ + gamma / 24 * K₄, T₂ + T₃ + T₄, by positivity,
    by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  rw [locEnergy_eq hlam hgamma hdisc hg ht0]
  exact energy_assembly lam alpha gamma t _ _ _ _ _ K₂ K₃ K₄ hlam hgamma ht1
    (h₂ (t := t) (by linarith)) (h₃ (t := t) (by linarith)) (h₄ (t := t) (by linarith))

/-- The seabed's sharp unlocalised energy rate, `|t⟨ℓ⟩ − ½ − e₀/t| ≤ K/t²`
(`energy_anharmonic_order1_rate_sharp`), with the coefficient named. -/
theorem energy_anharmonic_coeff1_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (anharmonicPotential lam alpha gamma) - 1 / 2 -
        energyCoeff1 lam alpha gamma / t| ≤ K / t ^ 2 := by
  unfold energyCoeff1
  exact energy_anharmonic_order1_rate_sharp hlam hgamma hdisc

/-- **The localiser's effect on the energy (C)**: `|t⟨ℓ⟩_loc − t⟨ℓ⟩ − d₁/t| ≤ K/t²`,
`d₁ = (a² − g)/(2λ) − aα/(2λ²)`; at `x₀ = 0` this is `−g/(2λ)`. -/
theorem localisedEnergy_sub_energy_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) -
        t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (anharmonicPotential lam alpha gamma) -
        locD1 lam alpha g x₀ / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := localisedEnergy_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  obtain ⟨K₀, T₀, hK₀, hT₀, h₀⟩ := energy_anharmonic_coeff1_rate hlam hgamma hdisc
  refine ⟨K₁ + K₀, T₁ + T₀, by positivity, by linarith, fun {t} ht => ?_⟩
  have e₁ := h₁ (t := t) (by linarith)
  have e₀ := h₀ (t := t) (by linarith)
  have key : t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) -
      t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) - locD1 lam alpha g x₀ / t =
      (t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) - 1 / 2 - energyLocCoeff1 lam alpha gamma g x₀ / t) -
      (t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) - 1 / 2 - energyCoeff1 lam alpha gamma / t) := by
    rw [energyLocCoeff1_eq_add lam alpha gamma g x₀ hlam]
    ring
  rw [key]
  calc _ ≤ _ + _ := abs_sub _ _
    _ ≤ K₁ / t ^ 2 + K₀ / t ^ 2 := add_le_add e₁ e₀
    _ = _ := by ring

/-- **The residual against E3's trace prediction**:
`|t⟨ℓ⟩_loc − ½·tλ/(tλ + g) − (e₁ + g/(2λ))/t| ≤ K/t²`, with
`e₁ + g/(2λ) = e₀ + a²/(2λ) − aα/(2λ²)`. -/
theorem localisedEnergy_sub_trace_rate (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
          (anharmonicPotential lam alpha gamma) - 1 / 2 * (t * lam / (t * lam + g)) -
        (energyLocCoeff1 lam alpha gamma g x₀ + g / (2 * lam)) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := localisedEnergy_order2_rate hlam hgamma hdisc hg (x₀ := x₀)
  refine ⟨K₁ + g ^ 2 / (2 * lam ^ 2), T₁, by positivity, hT₁, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e₁ := h₁ ht
  have e₂ := trace_scalar_remainder lam g t hlam hg ht0
  have key : t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) - 1 / 2 * (t * lam / (t * lam + g)) -
      (energyLocCoeff1 lam alpha gamma g x₀ + g / (2 * lam)) / t =
      (t * _root_.Laplace.gibbsExpectation (locPotential1 lam alpha gamma g x₀ t) t
        (anharmonicPotential lam alpha gamma) - 1 / 2 - energyLocCoeff1 lam alpha gamma g x₀ / t) -
      (1 / 2 * (t * lam / (t * lam + g)) - 1 / 2 + g / (2 * lam) / t) := by ring
  rw [key]
  calc _ ≤ _ + _ := abs_sub _ _
    _ ≤ K₁ / t ^ 2 + g ^ 2 / (2 * lam ^ 2) / t ^ 2 := add_le_add e₁ e₂
    _ = _ := by ring

end Rates

/-! ### E2: the rotated separable oscillator with the isotropic localiser (B) -/

section Multi

open Matrix

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- **The localised LLC to second order on E2's exact localised measure**:
`|t⟨L∘A⟩_loc − d/2 − (∑ᵢ e₁,ᵢ)/t| ≤ K/t²`, `e₁,ᵢ` the coefficient of the `i`-th frame oscillator
with anchor `u₀ᵢ = (Qᵀ(w₀ − c))ᵢ`. -/
theorem localisedRotatedAnharmonic_llc_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) - (d : ℝ) / 2 -
        (∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sq (fun _ : Fin d => (1 : ℝ))
    (fun i t => t * _root_.Laplace.gibbsExpectation
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
      (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 -
        energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t)
    (fun i => localisedEnergy_order2_rate (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) - (d : ℝ) / 2 -
      (∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t =
      ∑ i, 1 * (t * _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 -
          energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t) := by
    rw [localisedRotatedAnharmonic_energy_coord hQ c w₀ hlam hgamma hdisc hg ht0, Finset.mul_sum,
      Finset.sum_div]
    simp only [one_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [key]
  exact h ht

/-- **The residual against E3's trace prediction on E2**:
`|t⟨L∘A⟩_loc − ½tr(tH(tH + gI)⁻¹) − (∑ᵢ (e₁,ᵢ + g/(2λᵢ)))/t| ≤ K/t²`. -/
theorem localisedRotatedAnharmonic_llc_sub_trace_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) -
        1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace -
        (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
          g / (2 * lam i))) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sq (fun _ : Fin d => (1 : ℝ))
    (fun i t => t * _root_.Laplace.gibbsExpectation
      (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
      (anharmonicPotential (lam i) (alpha i) (gamma i)) - 1 / 2 * (t * lam i / (t * lam i + g)) -
        (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
          g / (2 * lam i)) / t)
    (fun i => localisedEnergy_sub_trace_rate (hlam i) (hgamma i) (hdisc i) hg)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have key : t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) -
      1 / 2 * (t • (Q * diagonal lam * Qᵀ) * locS g (Q * diagonal lam * Qᵀ) t).trace -
      (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
        g / (2 * lam i))) / t =
      ∑ i, 1 * (t * _root_.Laplace.gibbsExpectation
        (locPotential1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) -
          1 / 2 * (t * lam i / (t * lam i + g)) -
          (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
            g / (2 * lam i)) / t) := by
    rw [localisedRotatedAnharmonic_energy_coord hQ c w₀ hlam hgamma hdisc hg ht0,
      trace_smul_locS_rot hQ hlam hg ht0, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  exact h ht

end Multi

end Laplace.Multi
