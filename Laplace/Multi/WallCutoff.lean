/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.WallResponse
import Laplace.Multi.PatternAttenuation

/-!
# The wall model with a compact prior: leading order along the wall path

With a compactly supported prior `χ` the identity `t E[L_ε] = G(ε t^{m/(k+m)})` of `WallCrossover`
becomes a leading-order statement along the path `ε(t) = σ t^{-m/(k+m)}` through the wall: the
rescaled chart integrals converge to `χ(0)` times the wall-density integrals
(`tendsto_rpow_mul_wallCutoff_den`, `…_num`), and the cutoff energy statistic converges to
`G(σ)` (`tendsto_wallEnergyCutoff`). The substitution `x = t^{-1/2(k+m)} u` puts every
`t`-dependence into the cutoff, which tends to `χ(0)` by continuity, and dominated convergence
does the rest — as in `PatternAttenuation.tendsto_scaled_cutoff`.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The wall path `ε(t) = σ t^{-m/(k+m)}`. -/
noncomputable def wallPath (k m : ℕ) (σ t : ℝ) : ℝ := σ * t ^ (-((m : ℝ) / (k + m)))

/-- The substitution `x = t^{-1/2(k+m)} u` along the wall path, for any integrand shape `F`. -/
theorem rpow_mul_wall_integral_eq (χ : ℝ → ℝ) (k m h : ℕ) (hn : 1 ≤ k + m) (σ : ℝ) {t : ℝ}
    (ht : 0 < t) (F : ℝ → ℝ) :
    t ^ (((h : ℝ) + 1) / (2 * (k + m))) *
      ∫ x, χ x * |x| ^ h * F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k))) =
      ∫ u, χ (t ^ (-(1 / (2 * ((k : ℝ) + m)))) * u) * |u| ^ h *
        F (σ * u ^ (2 * k) + u ^ (2 * (k + m))) := by
  have hn' : (0 : ℝ) < (k : ℝ) + m := by exact_mod_cast hn
  set c : ℝ := t ^ (-(1 / (2 * ((k : ℝ) + m)))) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hc2n : t * c ^ (2 * (k + m)) = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast
    rw [show -(1 / (2 * ((k : ℝ) + m))) * (2 * (k + m)) = -1 by field_simp, Real.rpow_neg_one,
      mul_inv_cancel₀ ht.ne']
  have hc2k : t * (t ^ (-((m : ℝ) / (k + m))) * c ^ (2 * k)) = 1 := by
    have h1 := Real.rpow_add ht 1 (-((m : ℝ) / (k + m)))
    rw [Real.rpow_one] at h1
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← mul_assoc, ← h1, ← Real.rpow_add ht]
    push_cast
    rw [show (1 : ℝ) + -((m : ℝ) / (k + m)) + -(1 / (2 * ((k : ℝ) + m))) * (2 * k) = 0 by
      field_simp; ring, Real.rpow_zero]
  have hch : t ^ (((h : ℝ) + 1) / (2 * (k + m))) * c ^ (h + 1) = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    push_cast
    rw [show ((h : ℝ) + 1) / (2 * (k + m)) + -(1 / (2 * ((k : ℝ) + m))) * ((h : ℝ) + 1) = 0 by
      ring, Real.rpow_zero]
  have hpt : ∀ u : ℝ, t * ((wallPath k m σ t + (c * u) ^ (2 * m)) * (c * u) ^ (2 * k)) =
      σ * u ^ (2 * k) + u ^ (2 * (k + m)) := by
    intro u
    have : t * ((wallPath k m σ t + (c * u) ^ (2 * m)) * (c * u) ^ (2 * k)) =
        σ * (t * (t ^ (-((m : ℝ) / (k + m))) * c ^ (2 * k))) * u ^ (2 * k) +
          (t * c ^ (2 * (k + m))) * u ^ (2 * (k + m)) := by
      unfold wallPath
      ring
    rw [this, hc2k, hc2n, one_mul, mul_one]
  have hcomp := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ χ x * |x| ^ h * F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k)))) c
  rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at hcomp
  have hpt' : ∀ u : ℝ, χ (c * u) * |c * u| ^ h *
      F (t * ((wallPath k m σ t + (c * u) ^ (2 * m)) * (c * u) ^ (2 * k))) =
      c ^ h * (χ (c * u) * |u| ^ h * F (σ * u ^ (2 * k) + u ^ (2 * (k + m)))) := by
    intro u
    rw [hpt, abs_mul, abs_of_pos hcpos, mul_pow]
    ring
  simp only [hpt', integral_const_mul] at hcomp
  have hI : (∫ x, χ x * |x| ^ h * F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k)))) =
      c ^ (h + 1) * ∫ u, χ (c * u) * |u| ^ h * F (σ * u ^ (2 * k) + u ^ (2 * (k + m))) := by
    have hF : (∫ x, χ x * |x| ^ h * F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k)))) =
        c * (c⁻¹ * ∫ x, χ x * |x| ^ h *
          F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k)))) := by
      rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
    rw [hF, ← hcomp, pow_succ]
    ring
  rw [hI, ← mul_assoc, hch, one_mul]

/-- Dominated convergence for the rescaled cutoff against an integrable wall-type weight. -/
theorem tendsto_wall_cutoff {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m : ℕ) (hn : 1 ≤ k + m)
    {W : ℝ → ℝ} (hWc : Continuous W) (hWi : Integrable W) :
    Tendsto (fun t : ℝ ↦ ∫ u, χ (t ^ (-(1 / (2 * ((k : ℝ) + m)))) * u) * W u) atTop
      (𝓝 (χ 0 * ∫ u, W u)) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hn' : (0 : ℝ) < (k : ℝ) + m := by exact_mod_cast hn
  have hq : Tendsto (fun t : ℝ ↦ t ^ (-(1 / (2 * ((k : ℝ) + m))))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by positivity)
  have hχc := hχ.cont
  rw [← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence (fun u ↦ M * |W u|)
    (Filter.Eventually.of_forall fun t ↦ (by fun_prop : Continuous fun u : ℝ ↦
      χ (t ^ (-(1 / (2 * ((k : ℝ) + m)))) * u) * W u).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ↦ Filter.Eventually.of_forall fun u ↦ ?_)
    (hWi.abs.const_mul M) (Filter.Eventually.of_forall fun u ↦ ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  · have h0 : Tendsto (fun t : ℝ ↦ t ^ (-(1 / (2 * ((k : ℝ) + m)))) * u) atTop (𝓝 0) := by
      simpa using hq.mul_const u
    exact ((hχc.tendsto 0).comp h0).mul_const _

/-- The cutoff partition function along the wall path, rescaled. -/
theorem tendsto_rpow_mul_wallCutoff_den {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m h : ℕ) (hn : 1 ≤ k + m)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun t ↦ t ^ (((h : ℝ) + 1) / (2 * (k + m))) *
      ∫ x, χ x * |x| ^ h * Real.exp (-(t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k)))))
      atTop (𝓝 (χ 0 * ∫ u, wallW k m h σ u)) := by
  have hi := integrable_abs_pow_mul_wallW k m h 0 hn hσ
  simp only [pow_zero, one_mul] at hi
  have := tendsto_wall_cutoff hχ k m hn (W := fun u ↦ wallW k m h σ u)
    (by unfold wallW; fun_prop) hi
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [rpow_mul_wall_integral_eq χ k m h hn σ ht (fun y ↦ Real.exp (-y))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [wallW]
  ring

/-- The cutoff energy numerator along the wall path, rescaled. -/
theorem tendsto_rpow_mul_wallCutoff_num {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m h : ℕ) (hn : 1 ≤ k + m)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun t ↦ t ^ (((h : ℝ) + 1) / (2 * (k + m))) *
      ∫ x, χ x * |x| ^ h * (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k)) *
        Real.exp (-(t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k))))))
      atTop (𝓝 (χ 0 * ∫ u, (σ * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h σ u)) := by
  have hi := integrable_energy_mul_wallW k m h 0 hn hσ
  simp only [pow_zero, mul_one] at hi
  have := tendsto_wall_cutoff hχ k m hn
    (W := fun u ↦ (σ * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h σ u)
    (by unfold wallW; fun_prop) hi
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [rpow_mul_wall_integral_eq χ k m h hn σ ht (fun y ↦ y * Real.exp (-y))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [wallW]
  ring

/-- The energy statistic of the wall chart with a compact prior. -/
noncomputable def wallEnergyCutoff (χ : ℝ → ℝ) (k m h : ℕ) (ε t : ℝ) : ℝ :=
  t * ((∫ x, χ x * |x| ^ h * ((ε + x ^ (2 * m)) * x ^ (2 * k) *
      Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k)))))) /
    ∫ x, χ x * |x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k)))))

/-- **Along the wall path, the cutoff energy statistic converges to the crossover function.** -/
theorem tendsto_wallEnergyCutoff {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m h : ℕ) (hn : 1 ≤ k + m)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun t ↦ wallEnergyCutoff χ k m h (wallPath k m σ t) t) atTop
      (𝓝 (wallCross k m h σ)) := by
  have hN := tendsto_rpow_mul_wallCutoff_num hχ k m h hn hσ
  have hD := tendsto_rpow_mul_wallCutoff_den hχ k m h hn hσ
  have hD0 : χ 0 * ∫ u, wallW k m h σ u ≠ 0 :=
    (mul_pos hχ.pos (integral_wallW_pos k m h hn hσ)).ne'
  have := hN.div hD hD0
  unfold wallCross
  rw [mul_div_mul_left _ _ hχ.pos.ne'] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Pi.div_apply]
  rw [mul_div_mul_left _ _ (Real.rpow_pos_of_pos ht _).ne']
  unfold wallEnergyCutoff
  rw [mul_div_assoc']
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  ring

end Laplace.Multi
