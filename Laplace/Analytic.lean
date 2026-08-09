/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The analytic-germ instantiation

The germbij identifiability chain (Pencil, Sector, Identifiability, and
their multivariate forms) carries its analytic input as the factored
hypothesis `c * w ^ m ≤ |a w|` on `[0, r0]`. This file discharges that
hypothesis from analyticity: a real analytic function with nonzero germ at
`0` (finite `analyticOrderAt`) factors as `w ^ m · g w` with `g` analytic
and nonvanishing at `0` (`AnalyticAt.analyticOrderAt_eq_natCast`), and
continuity of `g` gives the lower bound with `c = |g 0| / 2` on a small
interval. This is the precise sense in which, in the germbij note's phrase,
"analyticity enters only through finite vanishing order".
-/

open Filter

namespace Laplace

/-- **Analytic growth lower bound.** A real analytic function with nonzero
germ at `0` dominates `c · w ^ m` on some `[0, r0]`, where `m` is its order
of vanishing. This discharges the factored hypothesis of
`sector_lower_bound` and the identifiability bounds from an analytic
hypothesis. -/
theorem analytic_growth_lower_bound (a : ℝ → ℝ) (ha : AnalyticAt ℝ a 0)
    (hne : analyticOrderAt a 0 ≠ ⊤) :
    ∃ (m : ℕ) (c r0 : ℝ), 0 < c ∧ 0 < r0 ∧
      analyticOrderAt a 0 = m ∧
      ∀ w ∈ Set.Icc (0 : ℝ) r0, c * w ^ m ≤ |a w| := by
  set m : ℕ := analyticOrderNatAt a 0 with hm_def
  have hord : analyticOrderAt a 0 = m := (ENat.coe_toNat hne).symm
  obtain ⟨g, hg, hg0, heq⟩ := (ha.analyticOrderAt_eq_natCast).mp hord
  -- `|g|` stays above `|g 0| / 2` near `0`, by continuity.
  have hgpos : 0 < |g 0| := abs_pos.mpr hg0
  have hlt : |g 0| / 2 < |g 0| := by linarith
  have habs : ContinuousAt (fun w ↦ |g w|) 0 := hg.continuousAt.abs
  have hgev : ∀ᶠ w in nhds (0 : ℝ), |g 0| / 2 < |g w| :=
    habs.eventually (eventually_gt_nhds hlt)
  -- Extract a common radius for the factorisation and the lower bound.
  have hboth := heq.and hgev
  rw [Metric.eventually_nhds_iff] at hboth
  obtain ⟨r, hr, hball⟩ := hboth
  refine ⟨m, |g 0| / 2, r / 2, by positivity, by positivity, hord, ?_⟩
  intro w hw
  have hwball : dist w 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hw.1]
    linarith [hw.2, hr]
  obtain ⟨hfac, hglb⟩ := hball hwball
  rw [hfac, sub_zero, smul_eq_mul, abs_mul, abs_pow, abs_of_nonneg hw.1]
  calc |g 0| / 2 * w ^ m = w ^ m * (|g 0| / 2) := by ring
    _ ≤ w ^ m * |g w| :=
        mul_le_mul_of_nonneg_left hglb.le (pow_nonneg hw.1 m)

end Laplace
