/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Anchoring
import Laplace.Decay

/-!
# One-point anchoring (germbij Proposition 7.6)

The Laplace-side completion of the anchoring programme. A continuous
compactly supported observable has moments bounded uniformly in the
temperature (`laplace_moment_bounded`); an observable supported where
the two losses agree has exactly equal moments
(`anchor_moment_eq`); and the composition
(`one_point_anchoring_contradiction`): under the analytic package of
the merged pencil--sector theorem, a normalized proportionality
between the two Laplace families that is anchored at one such
observable is contradictory. In the note's reading: if ratio
recovery at a single point of the zero locus shows the losses agree
on a neighborhood, then the common gauge `C(t)` is one, the
unnormalized families agree beyond all orders, and the singular
identifiability theorem forbids the germs from differing.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- Integrability of a damped observable: continuity, compact
support, and a nonnegative exponent make the Boltzmann-weighted
observable integrable at every `t ≥ 0`. -/
theorem integrable_mul_exp_neg_of_compactSupport
    {φ L : (ι → ℝ) → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hLc : Continuous L) (t : ℝ) :
    Integrable fun w : ι → ℝ ↦ φ w * Real.exp (-(t * L w)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hφc.mul (Real.continuous_exp.comp
      ((continuous_const.mul hLc).neg))
  · exact hφs.mul_right

/-- **Moment boundedness**: for `0 ≤ L` the moments of a continuous
compactly supported observable are bounded uniformly for `t ≥ 0`. -/
theorem laplace_moment_bounded {φ L : (ι → ℝ) → ℝ}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hLc : Continuous L) (hL : ∀ w, 0 ≤ L w) :
    (fun t : ℝ ↦ ∫ w : ι → ℝ, φ w * Real.exp (-(t * L w)))
      =O[atTop] fun _ : ℝ ↦ (1 : ℝ) := by
  rw [isBigO_iff]
  refine ⟨∫ w : ι → ℝ, |φ w|, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_one, mul_one, Real.norm_eq_abs]
  calc |∫ w : ι → ℝ, φ w * Real.exp (-(t * L w))|
      ≤ ∫ w : ι → ℝ, |φ w * Real.exp (-(t * L w))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w : ι → ℝ, |φ w| := by
        refine integral_mono ?_ ?_ fun w ↦ ?_
        · exact (integrable_mul_exp_neg_of_compactSupport hφc hφs
            hLc t).abs
        · exact (hφc.integrable_of_hasCompactSupport hφs).abs
        · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          calc |φ w| * Real.exp (-(t * L w))
              ≤ |φ w| * 1 := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                rw [Real.exp_le_one_iff]
                have := mul_nonneg ht (hL w)
                linarith
            _ = |φ w| := mul_one _

/-- **The anchor**: an observable supported where the two losses
agree has exactly equal moments, at every temperature. -/
theorem anchor_moment_eq {φ₀ L₁ L₂ : (ι → ℝ) → ℝ}
    {V : Set (ι → ℝ)} (hEq : Set.EqOn L₁ L₂ V)
    (hsupp : tsupport φ₀ ⊆ V) (t : ℝ) :
    ∫ w : ι → ℝ, φ₀ w * Real.exp (-(t * L₂ w)) =
      ∫ w : ι → ℝ, φ₀ w * Real.exp (-(t * L₁ w)) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only []
  by_cases hw : w ∈ tsupport φ₀
  · rw [hEq (hsupp hw)]
  · rw [image_eq_zero_of_notMem_tsupport hw, zero_mul, zero_mul]

/-- **One-point anchoring** (germbij Proposition 7.6, contradiction
form): under the analytic package of the pencil--sector theorem, a
common-gauge proportionality of the two normalized Laplace families
that is anchored at one observable supported where the losses agree
(with a positive polynomial lower bound on its reference moment) is
impossible. Normalized agreement anchored at one point of the zero
locus is incompatible with the germs differing. -/
theorem one_point_anchoring_contradiction
    (L₁ L₂ ψ : (ι → ℝ) → ℝ)
    {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} {r : ℝ≥0∞} (m : ℕ)
    (hg : HasFPowerSeriesOnBall (fun w ↦ L₂ w - L₁ w) p 0 r)
    (hlow : ∀ k, k < m → ∀ x : ι → ℝ, (p k) (fun _ ↦ x) = 0)
    {x₀ : ι → ℝ} (hx₀ : (p m) (fun _ ↦ x₀) ≠ 0) (hx₀n : ‖x₀‖ = 3 / 2)
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hsum : ∀ w : ι → ℝ, ‖w‖ ≤ R → L₁ w + L₂ w ≤ C0 * ‖w‖ ^ 2)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ R → ψ w = 1)
    {C : ℝ → ℝ} {φ₀ : (ι → ℝ) → ℝ} {V : Set (ι → ℝ)}
    (hEq : Set.EqOn L₁ L₂ V) (hsupp : tsupport φ₀ ⊆ V)
    {κ : ℝ} {n : ℕ} (hκ : 0 < κ)
    (hanchor_low : ∀ᶠ t in atTop, κ * t ^ (-(n : ℝ)) ≤
      ∫ w : ι → ℝ, φ₀ w * Real.exp (-(t * L₁ w)))
    (hprop₀ : SuperPoly fun t : ℝ ↦
      (∫ w : ι → ℝ, φ₀ w * Real.exp (-(t * L₂ w))) -
        C t * ∫ w : ι → ℝ, φ₀ w * Real.exp (-(t * L₁ w)))
    (hprop : SuperPoly fun t : ℝ ↦
      (∫ w : ι → ℝ, ((L₂ w - L₁ w) * ψ w) *
          Real.exp (-(t * L₂ w))) -
        C t * ∫ w : ι → ℝ, ((L₂ w - L₁ w) * ψ w) *
          Real.exp (-(t * L₁ w))) :
    False := by
  have hφc : Continuous fun w : ι → ℝ ↦ (L₂ w - L₁ w) * ψ w :=
    (hL2c.sub hL1c).mul hψc
  have hφs : HasCompactSupport
      fun w : ι → ℝ ↦ (L₂ w - L₁ w) * ψ w := hψs.mul_left
  have hbounded : (fun t : ℝ ↦ ∫ w : ι → ℝ,
      ((L₂ w - L₁ w) * ψ w) * Real.exp (-(t * L₁ w)))
      =O[atTop] fun _ : ℝ ↦ (1 : ℝ) :=
    laplace_moment_bounded hφc hφs hL1c hL1
  have hgauge := anchored_proportionality_remove_scalar hκ
    hanchor_low
    (Filter.Eventually.of_forall fun t ↦
      anchor_moment_eq hEq hsupp t)
    hprop₀ hprop hbounded
  refine analytic_pencil_difference_not_superpolynomial L₁ L₂ ψ m
    hg hlow hx₀ hx₀n hL1c hL2c hL1 hL2 hC0 hR hsum hψc hψs hψ0 hψ1
    fun N ↦ ?_
  have hN := (hgauge N).neg_left
  refine hN.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h₁ := integrable_mul_exp_neg_of_compactSupport hφc hφs hL1c t
  have h₂ := integrable_mul_exp_neg_of_compactSupport hφc hφs hL2c t
  have hsub : ∫ w : ι → ℝ, ((L₂ w - L₁ w) * ψ w) *
      (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) =
      (∫ w : ι → ℝ, ((L₂ w - L₁ w) * ψ w) *
          Real.exp (-(t * L₁ w))) -
        ∫ w : ι → ℝ, ((L₂ w - L₁ w) * ψ w) *
          Real.exp (-(t * L₂ w)) := by
    rw [← integral_sub h₁ h₂]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
    ring
  linarith [hsub]

end Laplace
