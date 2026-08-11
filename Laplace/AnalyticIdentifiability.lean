/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Analytic
import Laplace.Identifiability

/-!
# The identifiability lower bound under analytic hypotheses

The composition of the analytic-germ instantiation
(`analytic_growth_lower_bound`) with the quantitative identifiability bound
(`pencil_difference_lower_bound`): for nonnegative potentials analytic at
`0` whose germs differ (finite `analyticOrderAt` of the difference),
dominated by `C0 w²` near `0`, there are constants `m, c, r0` such that for
every sufficiently large `t` the observable `(L₂ - L₁) ψ` witnesses the
polynomial lower bound `c · t^(1 - m - 1/2)` on the difference of Boltzmann
integrals. This is the 1D germbij Theorem 7.3 chain with analyticity as the
hypothesis, closing the loop the note describes: the two families cannot
agree to all polynomial orders, so distinct analytic germs are
distinguished by a single observable.
-/

open MeasureTheory

namespace Laplace

/-- **Analytic identifiability lower bound** (germbij Theorem 7.3, 1D,
analytic hypotheses). Constants first, then all sufficiently large `t`;
the integrability premises are per-`t`. -/
theorem analytic_pencil_difference_lower_bound
    (L₁ L₂ ψ : ℝ → ℝ)
    (hL1a : AnalyticAt ℝ L₁ 0) (hL2a : AnalyticAt ℝ L₂ 0)
    (hne : analyticOrderAt (fun w ↦ L₂ w - L₁ w) 0 ≠ ⊤)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hsum : ∀ w ∈ Set.Icc (0 : ℝ) R, L₁ w + L₂ w ≤ C0 * w ^ 2)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w ∈ Set.Icc (0 : ℝ) R, ψ w = 1) :
    ∃ (m : ℕ) (c r0 : ℝ), 0 < c ∧ 0 < r0 ∧ r0 ≤ R ∧
      ∀ t : ℝ, 4 ≤ r0 ^ 2 * t →
        Integrable (fun w ↦
          (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w)))) →
        Integrable (Function.uncurry fun s w ↦
          ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
          ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, Integrable fun w ↦
          ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))))) →
        c * (t * t ^ (-(m : ℝ) - 1 / 2))
          ≤ ∫ w, ((L₂ w - L₁ w) * ψ w) *
              (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := by
  -- The difference is analytic at `0`; instantiate the growth bound.
  have hga : AnalyticAt ℝ (fun w ↦ L₂ w - L₁ w) 0 := hL2a.sub hL1a
  obtain ⟨m, c₀, r₁, hc₀, hr₁, _hord, hgrow⟩ :=
    analytic_growth_lower_bound _ hga hne
  -- Both potentials are analytic, hence continuous, on a ball around `0`.
  have hev : ∀ᶠ w in nhds (0 : ℝ), AnalyticAt ℝ L₁ w ∧ AnalyticAt ℝ L₂ w :=
    hL1a.eventually_analyticAt.and hL2a.eventually_analyticAt
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ρ, hρ, hball⟩ := hev
  set r0 : ℝ := min (min r₁ R) (ρ / 2) with hr0_def
  have hr0 : 0 < r0 := lt_min (lt_min hr₁ hR) (by positivity)
  have hr0R : r0 ≤ R := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr0r₁ : r0 ≤ r₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr0ρ : r0 < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨m, c₀ ^ 2 * Real.exp (-(4 * C0)), r0, by positivity, hr0, hr0R, ?_⟩
  intro t hrt hmin hint hslice
  -- The Laplace window sits inside `[0, r0] ⊆ ball 0 ρ`, where the
  -- integrand is continuous.
  have ht : 0 < t := by
    by_contra h
    have h' : t ≤ 0 := not_lt.mp h
    nlinarith [sq_nonneg r0, mul_nonneg (sq_nonneg r0) (neg_nonneg.mpr h')]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h2 : (2 : ℝ) ≤ r0 * Real.sqrt t := by
    have hb : (0 : ℝ) ≤ r0 * Real.sqrt t := by positivity
    nlinarith [Real.sq_sqrt ht.le, sq_nonneg (r0 * Real.sqrt t - 2)]
  have hur : 2 * (Real.sqrt t)⁻¹ ≤ r0 := by
    have heq : 2 * (Real.sqrt t)⁻¹ = 2 / Real.sqrt t := by ring
    rw [heq, div_le_iff₀ hst]
    linarith
  have hcontW : ContinuousOn
      (fun w ↦ (L₂ w - L₁ w) ^ 2 * Real.exp (-(t * (L₁ w + L₂ w))))
      (Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹)) := by
    intro w hw
    have hw0 : 0 ≤ w := le_trans (by positivity) hw.1
    have hwρ : dist w 0 < ρ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hw0]
      calc w ≤ 2 * (Real.sqrt t)⁻¹ := hw.2
        _ ≤ r0 := hur
        _ < ρ := hr0ρ
    obtain ⟨h1a, h2a⟩ := hball hwρ
    have h1 : ContinuousAt L₁ w := h1a.continuousAt
    have h2c : ContinuousAt L₂ w := h2a.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  exact pencil_difference_lower_bound L₁ L₂ ψ m hc₀.le hC0
    hr0 hrt hL1 hL2
    (fun w hw ↦ hsum w ⟨hw.1, le_trans hw.2 hr0R⟩)
    (fun w hw ↦ hgrow w ⟨hw.1, le_trans hw.2 hr0r₁⟩)
    hψ0 (fun w hw ↦ hψ1 w ⟨hw.1, le_trans hw.2 hr0R⟩)
    hmin hint hslice hcontW

end Laplace
