/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ThermoLengthAsymptotic

/-!
# The featureless law from a base temperature

For an unbounded loss the neutral endpoint `u = 0` of the temperature line may be awkward (an
improper prior makes it infinitely far away; a proper prior needs continuity of the variance down
to `u = 0`). Astra's round-24 advice: start the thermodynamic length at a base temperature
`u₀ > 0`; the initial segment is then irrelevant after division by `log t`, and the only
requirement on `(u₀, ∞)` is continuity of `u ↦ Var_u(L)`, which for `L ≥ 0` follows from dominated
convergence with the fixed dominant `L² e^{-u₀ L} π` (`continuousOn_priorCov_self_Ici`).

  `tendsto_intervalIntegral_div_log_from`: `u g(u) → c ⇒ (∫_{u₀}^t g)/log t → c`;
  `thermoLength_from_div_log_tendsto`: `u² Var_u(L) → λ ⇒ (∫_{u₀}^t √Var_u(L) du)/log t → √λ`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- **Cesàro lemma from a base point**: if `u g(u) → c` then `(∫_{u₀}^t g)/log t → c`. -/
theorem tendsto_intervalIntegral_div_log_from {g : ℝ → ℝ} {c u₀ : ℝ}
    (hg : ∀ a b : ℝ, u₀ ≤ a → u₀ ≤ b → IntervalIntegrable g volume a b)
    (hlim : Tendsto (fun u ↦ u * g u) atTop (𝓝 c)) :
    Tendsto (fun t ↦ (∫ u in u₀..t, g u) / Real.log t) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨U₁, hU₁⟩ := Metric.tendsto_atTop.1 hlim (ε / 4) hε4
  set U₀ : ℝ := max U₁ (max 1 u₀) with hU₀
  have hU₀1 : 1 ≤ U₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hU₀u : u₀ ≤ U₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hU₀pos : 0 < U₀ := by linarith
  have hlogU : 0 ≤ Real.log U₀ := Real.log_nonneg hU₀1
  have hbnd : ∀ u, U₀ ≤ u → |u * g u - c| ≤ ε / 4 := fun u hu ↦ by
    have := hU₁ u (le_trans (le_max_left _ _) hu)
    rw [Real.dist_eq] at this
    exact this.le
  set K : ℝ := ∫ u in u₀..U₀, g u with hK
  set A : ℝ := |K| + |c| * Real.log U₀ with hA
  have hA0 : 0 ≤ A := add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hlogU)
  refine ⟨max U₀ (Real.exp (A * 4 / ε + 1)), fun t ht ↦ ?_⟩
  have htU : U₀ ≤ t := le_trans (le_max_left _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le hU₀pos htU
  have hlogT : A * 4 / ε + 1 ≤ Real.log t := by
    have h2 := Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) ht)
    rwa [Real.log_exp] at h2
  have hlogpos : 0 < Real.log t := by
    have : 0 ≤ A * 4 / ε := by positivity
    linarith
  have hsplit : ∫ u in u₀..t, g u = K + ∫ u in U₀..t, g u :=
    (intervalIntegral.integral_add_adjacent_intervals (hg u₀ U₀ le_rfl hU₀u)
      (hg U₀ t hU₀u (hU₀u.trans htU))).symm
  have hinv : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume U₀ t := by
    refine intervalIntegral.intervalIntegrable_inv (f := fun x ↦ x) (fun x hx ↦ ?_) continuousOn_id
    rw [Set.uIcc_of_le htU] at hx
    exact (lt_of_lt_of_le hU₀pos hx.1).ne'
  have hsub : ∫ u in U₀..t, g u =
      (∫ u in U₀..t, (g u - c * u⁻¹)) + c * Real.log (t / U₀) := by
    rw [← integral_inv_of_pos hU₀pos htpos, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hg U₀ t hU₀u (hU₀u.trans htU)).sub (hinv.const_mul c))
        (hinv.const_mul c)]
    exact intervalIntegral.integral_congr fun u _ ↦ by simp only [sub_add_cancel]
  have hR : |∫ u in U₀..t, (g u - c * u⁻¹)| ≤ ε / 4 * Real.log (t / U₀) := by
    have := intervalIntegral.norm_integral_le_of_norm_le (f := fun u ↦ g u - c * u⁻¹)
      (g := fun u ↦ ε / 4 * u⁻¹) htU ?_ (hinv.const_mul _)
    · rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hU₀pos htpos] at this
      simpa only [Real.norm_eq_abs] using this
    · refine Filter.Eventually.of_forall fun u hu ↦ ?_
      have hu0 : 0 < u := lt_of_lt_of_le hU₀pos hu.1.le
      rw [Real.norm_eq_abs]
      have e : g u - c * u⁻¹ = (u * g u - c) * u⁻¹ := by
        rw [sub_mul, mul_right_comm, mul_inv_cancel₀ hu0.ne', one_mul]
      rw [e, abs_mul, abs_of_pos (inv_pos.mpr hu0)]
      exact mul_le_mul_of_nonneg_right (hbnd u hu.1.le) (inv_pos.mpr hu0).le
  rw [Real.dist_eq, hsplit, hsub, Real.log_div htpos.ne' hU₀pos.ne']
  set R := ∫ u in U₀..t, (g u - c * u⁻¹) with hR'
  have hlogne : Real.log t ≠ 0 := hlogpos.ne'
  have e : (K + (R + c * (Real.log t - Real.log U₀))) / Real.log t - c =
      (K + R - c * Real.log U₀) / Real.log t := by
    rw [eq_div_iff hlogne, sub_mul, div_mul_cancel₀ _ hlogne]
    ring
  rw [e, abs_div, abs_of_pos hlogpos, div_lt_iff₀ hlogpos]
  have h1 : |K + R - c * Real.log U₀| ≤ |K| + |R| + |c| * Real.log U₀ := by
    calc |K + R - c * Real.log U₀| ≤ |K + R| + |c * Real.log U₀| := abs_sub _ _
      _ ≤ |K| + |R| + |c| * Real.log U₀ := by
          rw [abs_mul, abs_of_nonneg hlogU]
          linarith [abs_add_le K R]
  have hR2 : |R| ≤ ε / 4 * Real.log t := by
    refine le_trans hR ?_
    rw [Real.log_div htpos.ne' hU₀pos.ne']
    exact mul_le_mul_of_nonneg_left (by linarith) hε4.le
  have h2 : A ≤ ε / 4 * (Real.log t - 1) := by
    have h3 : A * 4 / ε ≤ Real.log t - 1 := by linarith
    rw [div_le_iff₀ hε] at h3
    linarith
  have h4 := mul_pos hε hlogpos
  calc |K + R - c * Real.log U₀| ≤ |K| + |R| + |c| * Real.log U₀ := h1
    _ = A + |R| := by rw [hA]; ring
    _ ≤ ε / 4 * (Real.log t - 1) + ε / 4 * Real.log t := add_le_add h2 hR2
    _ < ε * Real.log t := by linarith

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Continuity of the temperature numerators on `[u₀, ∞)` for a nonnegative loss: dominated by
`|φ| e^{-u₀ L} π`. -/
theorem continuousOn_priorNum_Ici {π L φ : X → ℝ} (hLm : Measurable L) (hL : ∀ x, 0 ≤ L x)
    (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x) (hφm : Measurable φ) {u₀ : ℝ}
    (hint : Integrable (fun x ↦ |φ x| * (Real.exp (-(u₀ * L x)) * π x)) μ) :
    ContinuousOn (fun u ↦ ∫ x, φ x * Real.exp (-(u * L x)) * π x ∂μ) (Ici u₀) := by
  refine continuousOn_of_dominated (bound := fun x ↦ |φ x| * (Real.exp (-(u₀ * L x)) * π x))
    ?_ ?_ hint ?_
  · intro u _
    exact ((hφm.mul (Real.measurable_exp.comp (hLm.const_mul u).neg)).mul hπm).aestronglyMeasurable
  · intro u hu
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp, abs_of_nonneg (hπ x), mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (hπ x)) (abs_nonneg _)
    rw [Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_right (mem_Ici.mp hu) (hL x)
    linarith
  · exact Filter.Eventually.of_forall fun x ↦ Continuous.continuousOn (by fun_prop)

/-- Continuity of the temperature variance of a nonnegative loss on `[u₀, ∞)`. -/
theorem continuousOn_priorCov_self_Ici {π L : X → ℝ} (hLm : Measurable L) (hL : ∀ x, 0 ≤ L x)
    (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x) {u₀ : ℝ}
    (hZ : ∀ u, u₀ ≤ u → priorZ μ π L u ≠ 0)
    (h0 : Integrable (fun x ↦ Real.exp (-(u₀ * L x)) * π x) μ)
    (h1 : Integrable (fun x ↦ L x * (Real.exp (-(u₀ * L x)) * π x)) μ)
    (h2 : Integrable (fun x ↦ L x * L x * (Real.exp (-(u₀ * L x)) * π x)) μ) :
    ContinuousOn (fun u ↦ priorCov μ π L L L u) (Ici u₀) := by
  have c0 := continuousOn_priorNum_Ici (φ := fun _ ↦ (1 : ℝ)) hLm hL hπm hπ measurable_const
    (by simpa using h0)
  have c1 := continuousOn_priorNum_Ici (φ := L) hLm hL hπm hπ hLm
    (by simpa [abs_of_nonneg (hL _)] using h1)
  have c2 := continuousOn_priorNum_Ici (φ := fun x ↦ L x * L x) hLm hL hπm hπ (hLm.mul hLm)
    (by simpa [abs_of_nonneg (mul_nonneg (hL _) (hL _))] using h2)
  simp only [one_mul] at c0
  have hZ' : ∀ u ∈ Ici u₀, (∫ x, Real.exp (-(u * L x)) * π x ∂μ) ≠ 0 := fun u hu ↦ hZ u hu
  unfold priorCov priorExp priorZ
  exact (c2.div c0 hZ').sub ((c1.div c0 hZ').mul (c1.div c0 hZ'))

/-- **The featureless law from a base temperature**: if `u² Var_u(L) → λ` and the variance is
continuous on `[u₀, ∞)`, then `(∫_{u₀}^t √Var_u(L) du)/log t → √λ`. -/
theorem thermoLength_from_div_log_tendsto {π L : X → ℝ} {u₀ : ℝ}
    (hcont : ContinuousOn (fun u ↦ priorCov μ π L L L u) (Ici u₀)) {lam : ℝ}
    (hlam : Tendsto (fun u ↦ u ^ 2 * priorCov μ π L L L u) atTop (𝓝 lam)) :
    Tendsto (fun t ↦ (∫ u in u₀..t, Real.sqrt (priorCov μ π L L L u)) / Real.log t) atTop
      (𝓝 (Real.sqrt lam)) := by
  have hg : Tendsto (fun u ↦ u * Real.sqrt (priorCov μ π L L L u)) atTop (𝓝 (Real.sqrt lam)) := by
    have h := (Real.continuous_sqrt.tendsto lam).comp hlam
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    simp only [Function.comp_apply]
    rw [Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu]
  refine tendsto_intervalIntegral_div_log_from (fun a b ha hb ↦ ?_) hg
  have hsub : uIcc a b ⊆ Ici u₀ := fun x hx ↦ le_trans (le_min ha hb) hx.1
  exact (Real.continuous_sqrt.comp_continuousOn (hcont.mono hsub)).intervalIntegrable

end Laplace.Multi
