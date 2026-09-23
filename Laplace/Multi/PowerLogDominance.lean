/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# Dominance of power–log normalisations

The selection rule of the ray-sector assembly (germbij_slop S14, item F): a sector normalised by
`t^{-λ'} (log t)^{r'}` is negligible against one normalised by `t^{-λ} (log t)^{r}` when `λ < λ'`,
or when `λ = λ'` and `r' < r` (`tendsto_powLog_div_powLog`). Competition is first by powers, then by
logarithms; the retained sectors are those with the minimal power and, among them, the maximal
logarithmic multiplicity. Feeding the ratio into `two_chart_limit`/`dominated_chart_limit` makes the
discarded sectors invisible.
-/

open Real Filter Topology

namespace Laplace.Multi

/-- The normalisation `t^{-λ} (log t)^r`. -/
noncomputable def powLog (lam r : ℝ) (t : ℝ) : ℝ := t ^ (-lam) * Real.log t ^ r

theorem powLog_pos {lam r t : ℝ} (ht : 1 < t) : 0 < powLog lam r t :=
  mul_pos (Real.rpow_pos_of_pos (one_pos.trans ht) _) (Real.rpow_pos_of_pos (Real.log_pos ht) _)

/-- Power beats log: `t^{-(λ' − λ)} (log t)^{r' − r} → 0` when `λ < λ'`. -/
theorem tendsto_powLog_div_powLog_of_lt {lam₁ lam₂ r₁ r₂ : ℝ} (h : lam₁ < lam₂) :
    Tendsto (fun t ↦ powLog lam₂ r₂ t / powLog lam₁ r₁ t) atTop (𝓝 0) := by
  have key : Tendsto (fun t : ℝ ↦ Real.log t ^ (r₂ - r₁) / t ^ (lam₂ - lam₁)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (r₂ - r₁) (by linarith : 0 < lam₂ - lam₁)).tendsto_div_nhds_zero
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have ht0 : 0 < t := one_pos.trans ht
  have hl : 0 < Real.log t := Real.log_pos ht
  have h1 := Real.rpow_pos_of_pos ht0 lam₁
  have h2 := Real.rpow_pos_of_pos ht0 lam₂
  have h3 := Real.rpow_pos_of_pos hl r₁
  have h4 := Real.rpow_pos_of_pos hl r₂
  unfold powLog
  rw [Real.rpow_sub ht0, Real.rpow_sub hl, Real.rpow_neg ht0.le lam₂, Real.rpow_neg ht0.le lam₁]
  field_simp

/-- Equal powers: the log with the smaller exponent loses. -/
theorem tendsto_powLog_div_powLog_of_eq {lam₁ r₁ r₂ : ℝ} (h : r₂ < r₁) :
    Tendsto (fun t ↦ powLog lam₁ r₂ t / powLog lam₁ r₁ t) atTop (𝓝 0) := by
  have key : Tendsto (fun t : ℝ ↦ Real.log t ^ (-(r₁ - r₂))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp Real.tendsto_log_atTop
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have ht0 : 0 < t := one_pos.trans ht
  have hl : 0 < Real.log t := Real.log_pos ht
  simp only [powLog]
  rw [Real.rpow_neg hl.le, Real.rpow_sub hl]
  field_simp

/-- **The selection rule.** `powLog lam₂ r₂ = o(powLog lam₁ r₁)` iff (as a sufficient condition) the
power is larger or the power ties and the log exponent is smaller. -/
theorem tendsto_powLog_div_powLog {lam₁ lam₂ r₁ r₂ : ℝ} (h : lam₁ < lam₂ ∨ (lam₁ = lam₂ ∧ r₂ < r₁)) :
    Tendsto (fun t ↦ powLog lam₂ r₂ t / powLog lam₁ r₁ t) atTop (𝓝 0) := by
  rcases h with h | ⟨rfl, h⟩
  · exact tendsto_powLog_div_powLog_of_lt h
  · exact tendsto_powLog_div_powLog_of_eq h

end Laplace.Multi
