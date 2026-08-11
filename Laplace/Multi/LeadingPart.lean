/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The leading-part instantiation

The multivariate germbij chain consumes a scaled set `S` with the amplitude
bound `c · u^m ≤ |a (u • x)|` on `S` for small `u`
(`sector_lower_bound_multi`). This file produces that data from the
structure a multivariate Taylor expansion supplies: a continuous leading
part `P`, homogeneous of degree `m` under nonnegative scalings, nonzero in
some direction, together with a remainder bound `|a - P| ≤ C ‖x‖^(m+1)`
near `0`. The set `S` is a small closed ball around the good direction
(normalized to norm `3/2`, so `S` sits inside the sup-norm annulus), on
which `|P|` stays above half its center value by continuity; shrinking the
scale kills the remainder. This is the multivariate analogue of the 1D
analytic instantiation (`analytic_growth_lower_bound`), with the
factorisation hypothesis replacing Mathlib's one-variable analytic order
theory.
-/

open MeasureTheory

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- **Leading-part instantiation, multivariate.** A continuous homogeneous
leading part of degree `m`, nonzero at a direction of norm `3/2`, with
remainder `O(‖x‖^(m+1))`, yields a scaled set `S` in the annulus and
constants `c, u₀` with `c · u^m ≤ |a (u • x)|` for `x ∈ S`, `u ∈ (0, u₀]`. -/
theorem leading_part_scaled_set (a P : (ι → ℝ) → ℝ) (m : ℕ)
    (hPc : Continuous P)
    (hPh : ∀ (c : ℝ) (x : ι → ℝ), 0 ≤ c → P (c • x) = c ^ m * P x)
    {x₀ : ι → ℝ} (hx₀ : P x₀ ≠ 0) (hx₀n : ‖x₀‖ = 3 / 2)
    {C u₁ : ℝ} (hC : 0 ≤ C) (hu₁ : 0 < u₁)
    (hrem : ∀ x : ι → ℝ, ‖x‖ ≤ 2 * u₁ → |a x - P x| ≤ C * ‖x‖ ^ (m + 1)) :
    ∃ (S : Set (ι → ℝ)) (c u₀ : ℝ), MeasurableSet S ∧ volume S ≠ ⊤ ∧
      volume S ≠ 0 ∧ (∀ x ∈ S, ‖x‖ ≤ 2) ∧ 0 < c ∧ 0 < u₀ ∧
      ∀ u ∈ Set.Ioc (0 : ℝ) u₀, ∀ x ∈ S, c * u ^ m ≤ |a (u • x)| := by
  set c₁ : ℝ := |P x₀| / 2 with hc₁_def
  have hc₁ : 0 < c₁ := by
    have : 0 < |P x₀| := abs_pos.mpr hx₀
    positivity
  -- By continuity, `|P| > c₁` on a ball around `x₀`.
  have hgev : ∀ᶠ x in nhds x₀, c₁ < |P x| := by
    have habs : ContinuousAt (fun x ↦ |P x|) x₀ := hPc.continuousAt.abs
    have hlt : c₁ < |P x₀| := by
      have : 0 < |P x₀| := abs_pos.mpr hx₀
      rw [hc₁_def]
      linarith
    exact habs.eventually (eventually_gt_nhds hlt)
  rw [Metric.eventually_nhds_iff] at hgev
  obtain ⟨δ', hδ', hball⟩ := hgev
  set δ : ℝ := min (δ' / 2) (1 / 2) with hδ_def
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  set S : Set (ι → ℝ) := Metric.closedBall x₀ δ with hS_def
  -- The scale threshold: small enough to kill the remainder.
  set u₀ : ℝ := min u₁ (c₁ / (2 * (C * 2 ^ (m + 1) + 1))) with hu₀_def
  have hu₀ : 0 < u₀ := lt_min hu₁ (by positivity)
  refine ⟨S, c₁ / 2, u₀, measurableSet_closedBall,
    measure_closedBall_lt_top.ne, ?_, ?_, by positivity, hu₀, ?_⟩
  · -- Positive volume.
    have h1 : 0 < volume (Metric.ball x₀ δ) := Metric.measure_ball_pos _ _ hδ
    have h2 : Metric.ball x₀ δ ⊆ S := Metric.ball_subset_closedBall
    exact (h1.trans_le (measure_mono h2)).ne'
  · -- `S` sits inside the annulus `‖x‖ ≤ 2`.
    intro x hx
    have hd : dist x x₀ ≤ δ := Metric.mem_closedBall.mp hx
    calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by ring_nf
      _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
      _ ≤ 3 / 2 + 1 / 2 := by
          rw [hx₀n]
          have : ‖x - x₀‖ = dist x x₀ := (dist_eq_norm x x₀).symm
          have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
          linarith [this ▸ hd]
      _ = 2 := by norm_num
  · -- The amplitude bound at scales `u ∈ (0, u₀]`.
    intro u hu x hx
    have hu0 : 0 < u := hu.1
    have hPx : c₁ < |P x| := by
      apply hball
      calc dist x x₀ ≤ δ := Metric.mem_closedBall.mp hx
        _ ≤ δ' / 2 := min_le_left _ _
        _ < δ' := by linarith
    have hxn : ‖x‖ ≤ 2 := by
      have hd : dist x x₀ ≤ δ := Metric.mem_closedBall.mp hx
      have h1 : ‖x - x₀‖ = dist x x₀ := (dist_eq_norm x x₀).symm
      have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
      calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by ring_nf
        _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
        _ ≤ 2 := by rw [hx₀n]; linarith [h1 ▸ hd]
    have huxn : ‖u • x‖ ≤ 2 * u := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0.le]
      nlinarith
    -- `|a (u • x)| ≥ |P (u • x)| - |a - P| (u • x)`.
    have htri : |P (u • x)| - |a (u • x) - P (u • x)| ≤ |a (u • x)| := by
      have h1 : |P (u • x)| - |a (u • x)| ≤ |P (u • x) - a (u • x)| :=
        abs_sub_abs_le_abs_sub _ _
      rw [abs_sub_comm] at h1
      linarith
    have hPux : |P (u • x)| = u ^ m * |P x| := by
      rw [hPh u x hu0.le, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ m)]
    have hR : |a (u • x) - P (u • x)| ≤ C * 2 ^ (m + 1) * u ^ (m + 1) := by
      have huu₁ : u ≤ u₁ := le_trans hu.2 (min_le_left _ _)
      have h := hrem (u • x) (le_trans huxn (by nlinarith))
      calc |a (u • x) - P (u • x)| ≤ C * ‖u • x‖ ^ (m + 1) := h
        _ ≤ C * (2 * u) ^ (m + 1) := by
            apply mul_le_mul_of_nonneg_left _ hC
            exact pow_le_pow_left₀ (norm_nonneg _) huxn (m + 1)
        _ = C * 2 ^ (m + 1) * u ^ (m + 1) := by ring
    have hsmall : C * 2 ^ (m + 1) * u ≤ c₁ / 2 := by
      have hu₀2 : u ≤ c₁ / (2 * (C * 2 ^ (m + 1) + 1)) :=
        le_trans hu.2 (min_le_right _ _)
      have hpos : (0:ℝ) < 2 * (C * 2 ^ (m + 1) + 1) := by positivity
      rw [le_div_iff₀ hpos] at hu₀2
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (m + 1)]
    calc c₁ / 2 * u ^ m
        = u ^ m * c₁ - u ^ m * (c₁ / 2) := by ring
      _ ≤ u ^ m * |P x| - C * 2 ^ (m + 1) * u ^ (m + 1) := by
          have h1 : u ^ m * c₁ ≤ u ^ m * |P x| :=
            mul_le_mul_of_nonneg_left hPx.le (by positivity)
          have h2 : C * 2 ^ (m + 1) * u ^ (m + 1) ≤ u ^ m * (c₁ / 2) := by
            calc C * 2 ^ (m + 1) * u ^ (m + 1)
                = (C * 2 ^ (m + 1) * u) * u ^ m := by ring
              _ ≤ (c₁ / 2) * u ^ m :=
                  mul_le_mul_of_nonneg_right hsmall (by positivity)
              _ = u ^ m * (c₁ / 2) := by ring
          linarith
      _ = |P (u • x)| - C * 2 ^ (m + 1) * u ^ (m + 1) := by rw [hPux]
      _ ≤ |P (u • x)| - |a (u • x) - P (u • x)| := by linarith [hR]
      _ ≤ |a (u • x)| := htri

end Laplace
