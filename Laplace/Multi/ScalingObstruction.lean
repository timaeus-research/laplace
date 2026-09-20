/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NormalizedSingular

/-!
# Rescaled losses are never projectively equivalent

The germbij note offers a scaling heuristic for its proportionality question:
for `L₂ = μ L₁` with `μ ≠ 1` the Laplace families are related by `t ↦ μ t`,
which twists the coefficient of each exponent `t^{-λ}` by `μ^{-λ}` and so
should not be of the form `C(t) ×`; the note records that it has no general
proof. The normalized singular identifiability theorem supplies one, in any
dimension and with no hypothesis beyond analyticity at a zero: projective
equivalence of the families of `L` and `μ L` forces `L = μ L` near the zero,
hence `L = 0` there. So the only rescaling that is projectively invisible is
the trivial one, unless `L` vanishes identically near the zero.

* `not_projective_of_scaling`: the projective (arbitrary scalar `C(t)`) form.
* `not_normalized_agreement_of_scaling`: the form with the `1/Z` incorporated
  (normalized expectations against a common window).
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- **No projective equivalence under rescaling.** If `L ≥ 0` is smooth,
analytic at a zero `p`, and not identically zero near `p`, then for `μ ≥ 0`,
`μ ≠ 1`, no scalar `C(t)` makes `∫ φ e^{-tμL} - C(t) ∫ φ e^{-tL}` beyond all
orders for every smooth compactly supported `φ`. -/
theorem not_projective_of_scaling {L : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hL : ContDiff ℝ ∞ L) (hL0 : ∀ w, 0 ≤ L w) (hA : AnalyticAt ℝ L p) (hp : L p = 0)
    (hne : ¬ ∀ᶠ w in 𝓝 p, L w = 0) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≠ 1) (C : ℝ → ℝ) :
    ¬ ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * (μ * L w))))
        - C t * ∫ w, φ w * Real.exp (-(t * L w)) := by
  intro hfam
  have h2 : ContDiff ℝ ∞ fun w ↦ μ * L w := contDiff_const.mul hL
  have hL2 : ∀ w, 0 ≤ μ * L w := fun w ↦ mul_nonneg hμ0 (hL0 w)
  have hA2 : AnalyticAt ℝ (fun w ↦ μ * L w) p := analyticAt_const.mul hA
  have hp2 : μ * L p = 0 := by rw [hp, mul_zero]
  have heq := normalized_families_force_germ_eq_at hL h2 hL0 hL2 hA hA2 hp hp2 hfam
  refine hne ?_
  filter_upwards [heq] with w hw
  have h : (1 - μ) * L w = 0 := by linarith
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hμ1))

/-- **No agreement of normalized expectations under rescaling.** With a common
continuous compactly supported nonnegative window `χ` whose Boltzmann integrals
are positive for both `L` and `μ L`, the normalized expectations of `L` and
`μ L` cannot agree beyond all orders on every smooth compactly supported `φ`
unless `μ = 1` or `L` vanishes identically near the zero `p`. -/
theorem not_normalized_agreement_of_scaling {L χ : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hL : ContDiff ℝ ∞ L) (hL0 : ∀ w, 0 ≤ L w) (hA : AnalyticAt ℝ L p) (hp : L p = 0)
    (hne : ¬ ∀ᶠ w in 𝓝 p, L w = 0) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≠ 1)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * (μ * L w)))) :
    ¬ ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦
        (∫ w, φ w * Real.exp (-(t * (μ * L w)))) / (∫ w, χ w * Real.exp (-(t * (μ * L w))))
        - (∫ w, φ w * Real.exp (-(t * L w))) / (∫ w, χ w * Real.exp (-(t * L w))) := by
  intro hfam
  have h2 : ContDiff ℝ ∞ fun w ↦ μ * L w := contDiff_const.mul hL
  have hL2 : ∀ w, 0 ≤ μ * L w := fun w ↦ mul_nonneg hμ0 (hL0 w)
  have hA2 : ∀ q ∈ ({p} : Set (ι → ℝ)), AnalyticAt ℝ (fun w ↦ μ * L w) q := by
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact analyticAt_const.mul hA
  have hA1 : ∀ q ∈ ({p} : Set (ι → ℝ)), AnalyticAt ℝ L q := by
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hA
  have hz1 : ∀ q ∈ ({p} : Set (ι → ℝ)), L q = 0 := by
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hp
  have hz2 : ∀ q ∈ ({p} : Set (ι → ℝ)), μ * L q = 0 := by
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    rw [hp, mul_zero]
  obtain ⟨U, hUo, hpU, hU⟩ := normalized_expectations_force_eq_near hL h2 hL0 hL2 hA1 hA2
    hz1 hz2 hχc hχs hχ0 hZ1 hZ2 hfam
  refine hne ?_
  filter_upwards [hUo.mem_nhds (hpU rfl)] with w hw
  have h : (1 - μ) * L w = 0 := by linarith [hU w hw]
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hμ1))

end Laplace
