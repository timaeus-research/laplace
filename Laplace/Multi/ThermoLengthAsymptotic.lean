/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ThermoLengthIntegral

/-!
# The thermodynamic length from the featureless point to the data grows like `√λ · log t`

The mixture line from a **loss-neutral** ("featureless") data distribution `q₀` (constant loss
`c`) to the data `q₁` (loss `c + Δ`) coincides with the temperature line of the target: the
posterior at mixture weight `s` and temperature `t` is the posterior of `c + Δ` at temperature
`ts` (`priorExp_neutral`). Hence the Fisher speed of the neutral line is the temperature-`ts`
variance of the loss contrast (`fisherSpeed_neutral`), and the **thermodynamic length** of the
segment `[0, 1]` from the featureless point to the data,

  `ℓ(t) = ∫₀¹ √(t² Var_{ts}(Δ)) ds = ∫₀^t √(Var_u(Δ)) du`   (`thermoLength_neutral_eq`),

is the integral of the posterior standard deviation of the loss over all temperatures up to `t`.

If the loss fluctuations obey the singular law `u² Var_u(Δ) → λ` (the real log canonical threshold
in Watanabe's theory, `d/2` for a regular model), then `u √Var_u → √λ` and the length is
logarithmically divergent with slope exactly `√λ`:

  `ℓ(t) / log t → √λ`   (`thermoLength_neutral_div_log_tendsto`).

The RLCT is therefore the **growth rate of the thermodynamic length** from the featureless
distribution to the data: the response map, measured in its own Fisher metric, places the data at
distance `√λ log t + O(1)` from the featureless point. The analytic input is the elementary
Cesàro-type lemma `tendsto_intervalIntegral_div_log`: `u g(u) → c` implies
`(∫₀^t g)/log t → c`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The thermodynamic length of the data path on `s ∈ [0, 1]` at temperature `t`. -/
noncomputable def thermoLength (μ : Measure X) (π : X → ℝ) (L L' : ℝ → X → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, Real.sqrt (fisherSpeed μ π L L' t s)

/-- On the neutral line the Fisher speed is `t²` times the temperature-`ts` variance of the loss
contrast under the target loss. -/
theorem fisherSpeed_neutral (π Δ : X → ℝ) (c t s : ℝ) :
    fisherSpeed μ π (pathLoss (fun _ ↦ c) Δ) (fun _ ↦ Δ) t s =
      t ^ 2 * priorCov μ π (fun x ↦ c + Δ x) Δ Δ (t * s) := by
  have e : pathLoss (fun _ ↦ c) Δ s = fun x ↦ (1 - s) * c + s * (c + Δ x) := by
    funext x
    simp only [pathLoss]
    ring
  simp only [fisherSpeed, priorCov]
  rw [e, priorExp_neutral, priorExp_neutral]

/-- **The length from the featureless point to the data is the integral of the temperature
standard deviation of the loss**: `ℓ(t) = ∫₀^t √Var_u(Δ) du`. -/
theorem thermoLength_neutral_eq (π Δ : X → ℝ) (c : ℝ) {t : ℝ} (ht : 0 < t) :
    thermoLength μ π (pathLoss (fun _ ↦ c) Δ) (fun _ ↦ Δ) t =
      ∫ u in (0 : ℝ)..t, Real.sqrt (priorCov μ π (fun x ↦ c + Δ x) Δ Δ u) := by
  unfold thermoLength
  have e : ∀ s, Real.sqrt (fisherSpeed μ π (pathLoss (fun _ ↦ c) Δ) (fun _ ↦ Δ) t s) =
      t * Real.sqrt (priorCov μ π (fun x ↦ c + Δ x) Δ Δ (t * s)) := fun s ↦ by
    rw [fisherSpeed_neutral, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left
    (f := fun u ↦ Real.sqrt (priorCov μ π (fun x ↦ c + Δ x) Δ Δ u)) ht.ne', mul_zero, mul_one,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

/-- **Cesàro lemma for logarithmic growth**: if `u g(u) → c` then `(∫₀^t g)/log t → c`. -/
theorem tendsto_intervalIntegral_div_log {g : ℝ → ℝ} {c : ℝ}
    (hg : ∀ a b : ℝ, 0 ≤ a → IntervalIntegrable g volume a b)
    (hlim : Tendsto (fun u ↦ u * g u) atTop (𝓝 c)) :
    Tendsto (fun t ↦ (∫ u in (0 : ℝ)..t, g u) / Real.log t) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨U₁, hU₁⟩ := Metric.tendsto_atTop.1 hlim (ε / 4) hε4
  set U₀ : ℝ := max U₁ 1 with hU₀
  have hU₀1 : 1 ≤ U₀ := le_max_right _ _
  have hU₀pos : 0 < U₀ := by linarith
  have hlogU : 0 ≤ Real.log U₀ := Real.log_nonneg hU₀1
  have hbnd : ∀ u, U₀ ≤ u → |u * g u - c| ≤ ε / 4 := fun u hu ↦ by
    have := hU₁ u (le_trans (le_max_left _ _) hu)
    rw [Real.dist_eq] at this
    exact this.le
  set K : ℝ := ∫ u in (0 : ℝ)..U₀, g u with hK
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
  have hsplit : ∫ u in (0 : ℝ)..t, g u = K + ∫ u in U₀..t, g u :=
    (intervalIntegral.integral_add_adjacent_intervals (hg 0 U₀ le_rfl) (hg U₀ t hU₀pos.le)).symm
  have hinv : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume U₀ t := by
    refine intervalIntegral.intervalIntegrable_inv (f := fun x ↦ x) (fun x hx ↦ ?_) continuousOn_id
    rw [Set.uIcc_of_le htU] at hx
    exact (lt_of_lt_of_le hU₀pos hx.1).ne'
  have hsub : ∫ u in U₀..t, g u =
      (∫ u in U₀..t, (g u - c * u⁻¹)) + c * Real.log (t / U₀) := by
    rw [← integral_inv_of_pos hU₀pos htpos, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hg U₀ t hU₀pos.le).sub (hinv.const_mul c))
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

/-- **The RLCT is the growth rate of the thermodynamic length**: if `u² Var_u(Δ) → λ` along the
temperature line of the target loss `c + Δ`, then the thermodynamic length from the featureless
point to the data at temperature `t` satisfies `ℓ(t)/log t → √λ`. -/
theorem thermoLength_neutral_div_log_tendsto (π Δ : X → ℝ) (c : ℝ)
    (hint : ∀ a b : ℝ, 0 ≤ a → IntervalIntegrable
      (fun u ↦ Real.sqrt (priorCov μ π (fun x ↦ c + Δ x) Δ Δ u)) volume a b)
    {lam : ℝ} (hlam : Tendsto (fun u ↦ u ^ 2 * priorCov μ π (fun x ↦ c + Δ x) Δ Δ u) atTop
      (𝓝 lam)) :
    Tendsto (fun t ↦ thermoLength μ π (pathLoss (fun _ ↦ c) Δ) (fun _ ↦ Δ) t / Real.log t) atTop
      (𝓝 (Real.sqrt lam)) := by
  have hg : Tendsto (fun u ↦ u * Real.sqrt (priorCov μ π (fun x ↦ c + Δ x) Δ Δ u)) atTop
      (𝓝 (Real.sqrt lam)) := by
    have h := (Real.continuous_sqrt.tendsto lam).comp hlam
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    simp only [Function.comp_apply]
    rw [Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu]
  refine (tendsto_intervalIntegral_div_log hint hg).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [thermoLength_neutral_eq π Δ c ht]

/-- For a bounded loss contrast the temperature variance is continuous in the temperature
(from the continuity of the posterior variance along the mixture line, `continuousAt_priorCov_self`,
and the neutral-line identity). -/
theorem continuous_neutral_var [Nonempty X] {π Δ : X → ℝ} (hπm : Measurable π)
    (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hΔm : Measurable Δ)
    {MΔ : ℝ} (hΔ : ∀ x, |Δ x| ≤ MΔ) (c : ℝ) :
    Continuous (fun u ↦ priorCov μ π (fun x ↦ c + Δ x) Δ Δ u) := by
  refine continuous_iff_continuousAt.mpr fun u ↦ ?_
  have h := PathData.mixture (μ := μ) hπm hπi hπ hπpos (L₀ := fun _ ↦ c) measurable_const
    (M₀ := |c|) (fun _ ↦ le_rfl) hΔm hΔ (|u| + 1)
  have hc := PathData2.continuousAt_priorCov_self h hΔm hΔ 1
    (s₀ := u) ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  have e : (fun s ↦ priorCov μ π (pathLoss (fun _ ↦ c) Δ s) Δ Δ 1) =
      fun u ↦ priorCov μ π (fun x ↦ c + Δ x) Δ Δ u := by
    funext s
    have := fisherSpeed_neutral (μ := μ) π Δ c 1 s
    simp only [fisherSpeed, one_pow, one_mul] at this
    exact this
  rwa [e] at hc

/-- **The RLCT is the growth rate of the thermodynamic length**, for a bounded loss contrast: only
the singular fluctuation law `u² Var_u(Δ) → λ` is assumed. -/
theorem thermoLength_neutral_div_log_tendsto' [Nonempty X] {π Δ : X → ℝ} (hπm : Measurable π)
    (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hΔm : Measurable Δ)
    {MΔ : ℝ} (hΔ : ∀ x, |Δ x| ≤ MΔ) (c : ℝ) {lam : ℝ}
    (hlam : Tendsto (fun u ↦ u ^ 2 * priorCov μ π (fun x ↦ c + Δ x) Δ Δ u) atTop (𝓝 lam)) :
    Tendsto (fun t ↦ thermoLength μ π (pathLoss (fun _ ↦ c) Δ) (fun _ ↦ Δ) t / Real.log t) atTop
      (𝓝 (Real.sqrt lam)) :=
  thermoLength_neutral_div_log_tendsto π Δ c
    (fun a b _ ↦ (Real.continuous_sqrt.comp
      (continuous_neutral_var hπm hπi hπ hπpos hΔm hΔ c)).intervalIntegrable a b) hlam

end Laplace.Multi
