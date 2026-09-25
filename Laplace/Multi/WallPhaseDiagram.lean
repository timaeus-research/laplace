/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.NegativeChamberLaw
import Laplace.Multi.RadialCurvature

/-!
# The phase diagram of the two-monomial wall, and self-similarity of the ray

An abstract **dilation lemma** (`tendsto_intervalIntegral_dilation`): if `c h(c) → L` then
`∫_{aT}^{bT} h(c) dc → L log(b/a)` as `T → ∞`. Applied to the wall profile through the window
isometry it gives the third regime of the wall, and with the negative chamber law and the receding
wall the complete **phase diagram** of the thermodynamic length `ℓ_t(a,b)` of the window `[a,b]`:

* `a < 0 < b`: `ℓ_t(a,b)/√t → K₋(−a)`  (`wall_phase_negative`),
* `a = 0 < b`: `ℓ_t(0,b)/log t → σ√(1/q)`  (`wall_phase_wall`),
* `0 < a ≤ b`: `ℓ_t(a,b) → √(1/q) log(b/a)`  (`wall_phase_positive`).

Applied to the featureless ray with `u²Var_u → λ` it gives the **multiplicative self-similarity**
`∫_{cu}^{du} √Var_v dv → √λ log(d/c)` (`tendsto_ray_length_dilation`), completing the triple
(length, KL, affinity) of `AffinityKL` (Astra round 28 §1.3).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- **The dilation lemma**: `c h(c) → L` implies `∫_{aT}^{bT} h → L log(b/a)`. -/
theorem tendsto_intervalIntegral_dilation {h : ℝ → ℝ} {L : ℝ} (hcont : ContinuousOn h (Ioi 0))
    (hlim : Tendsto (fun c ↦ c * h c) atTop (𝓝 L)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun T ↦ ∫ c in (a * T)..(b * T), h c) atTop (𝓝 (L * Real.log (b / a))) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  -- the substitution `c = T v`
  have hsub : ∀ T, 0 < T → (∫ c in (a * T)..(b * T), h c) = ∫ v in a..b, T * h (T * v) := by
    intro T hT
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (f := h) hT.ne', smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hT.ne', one_mul, mul_comm T a, mul_comm T b]
  -- eventual bound from the limit
  obtain ⟨C₀, hC₀⟩ := Metric.tendsto_atTop.1 hlim 1 one_pos
  have hbnd : ∀ c, C₀ ≤ c → |c * h c| ≤ |L| + 1 := fun c hc ↦ by
    have := hC₀ c hc
    rw [Real.dist_eq] at this
    calc |c * h c| = |(c * h c - L) + L| := by ring_nf
      _ ≤ |c * h c - L| + |L| := abs_add_le _ _
      _ ≤ |L| + 1 := by linarith
  -- dominated convergence on `[a, b]`
  have hdom : Tendsto (fun T ↦ ∫ v in a..b, T * h (T * v)) atTop (𝓝 (∫ v in a..b, L / v)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ (|L| + 1) / a) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine continuousOn_const.mul (hcont.comp (continuous_const.mul continuous_id).continuousOn
        fun v hv ↦ ?_)
      rw [uIoc_of_le hab] at hv
      exact mul_pos hT (lt_trans ha hv.1)
    · filter_upwards [eventually_ge_atTop (C₀ / a), eventually_gt_atTop (0 : ℝ)] with T hT hT0
      refine Filter.Eventually.of_forall fun v hv ↦ ?_
      rw [uIoc_of_le hab] at hv
      have hv0 : 0 < v := lt_trans ha hv.1
      have hTv : C₀ ≤ T * v := by
        calc C₀ = C₀ / a * a := by field_simp
          _ ≤ T * a := mul_le_mul_of_nonneg_right hT ha.le
          _ ≤ T * v := mul_le_mul_of_nonneg_left hv.1.le hT0.le
      rw [Real.norm_eq_abs]
      have e : T * h (T * v) = (T * v * h (T * v)) / v := by field_simp
      rw [e, abs_div, abs_of_pos hv0]
      calc |T * v * h (T * v)| / v ≤ (|L| + 1) / v :=
            div_le_div_of_nonneg_right (hbnd _ hTv) hv0.le
        _ ≤ (|L| + 1) / a := div_le_div_of_nonneg_left (by positivity) ha hv.1.le
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun v hv ↦ ?_
      rw [uIoc_of_le hab] at hv
      have hv0 : 0 < v := lt_trans ha hv.1
      have hT : Tendsto (fun T : ℝ ↦ T * v) atTop atTop := tendsto_id.atTop_mul_const hv0
      have := (hlim.comp hT).div_const v
      refine this.congr' (Filter.Eventually.of_forall fun T ↦ ?_)
      simp only [Function.comp_apply]
      field_simp
  have hval : (∫ v in a..b, L / v) = L * Real.log (b / a) := by
    have e : (fun v : ℝ ↦ L / v) = fun v ↦ L * v⁻¹ := by funext v; rw [div_eq_mul_inv]
    rw [e, intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
  rw [hval] at hdom
  refine hdom.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (hsub T hT).symm

/-! ### The phase diagram of the two-monomial wall -/

section Wall

variable {p q : ℝ} (hq : 0 < q) (hqp : q < p)
include hq hqp

/-- The Fisher speed of the wall path at temperature `t` is continuous in the coupling. -/
theorem continuous_sqrt_fisherSpeed_twoMono {t : ℝ} (ht : 0 < t) :
    Continuous (fun a ↦ Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1)
      (twoMonoPath p q) (twoMonoVel q) t a)) := by
  have hp : 0 < p := by linarith
  set σ : ℝ := 1 - q / p with hσ
  have hpos : 0 < t ^ σ := Real.rpow_pos_of_pos ht _
  have hinv : t ^ (-σ) = (t ^ σ)⁻¹ := Real.rpow_neg ht.le σ
  have e : ∀ a, Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q)
      (twoMonoVel q) t a) =
      t ^ σ * Real.sqrt (profilePosterior p q (fun y ↦ y ^ q * y ^ q) (a * t ^ σ)
        - profilePosterior p q (fun y ↦ y ^ q) (a * t ^ σ) ^ 2) := fun a ↦ by
    have ha : a = (a * t ^ σ) * t ^ (-σ) := by
      rw [hinv, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
    conv_lhs => rw [ha]
    rw [fisherSpeed_twoMonoPath hp ht, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le]
  rw [show (fun a ↦ Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q)
    (twoMonoVel q) t a)) = _ from funext e]
  exact continuous_const.mul (Real.continuous_sqrt.comp
    ((continuous_profileVar hq hqp).comp (continuous_id.mul continuous_const)))

/-- **Phase III, the positive chamber**: for a window `0 < a ≤ b` away from the wall the length
converges to the finite value `√(1/q) log(b/a)`. -/
theorem wall_phase_positive {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun t ↦ ∫ a' in a..b, Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1)
      (twoMonoPath p q) (twoMonoVel q) t a')) atTop (𝓝 (Real.sqrt (1 / q) * Real.log (b / a))) := by
  have hp : 0 < p := by linarith
  set σ : ℝ := 1 - q / p with hσ
  have hσpos : 0 < σ := by rw [hσ, sub_pos, div_lt_one hp]; exact hqp
  set V : ℝ → ℝ := fun c ↦ profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
    profilePosterior p q (fun y ↦ y ^ q) c ^ 2 with hV
  have hcont : ContinuousOn (fun c ↦ Real.sqrt (V c)) (Ioi 0) :=
    (Real.continuous_sqrt.comp (continuous_profileVar hq hqp)).continuousOn
  have hlim : Tendsto (fun c ↦ c * Real.sqrt (V c)) atTop (𝓝 (Real.sqrt (1 / q))) := by
    have := (Real.continuous_sqrt.tendsto _).comp (tendsto_sq_mul_profileVar hp hq)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
    simp only [Function.comp_apply, hV]
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  have hdil := tendsto_intervalIntegral_dilation hcont hlim ha hab
  have hT : Tendsto (fun t : ℝ ↦ t ^ σ) atTop atTop := tendsto_rpow_atTop hσpos
  refine (hdil.comp hT).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply]
  have hw := wall_window_length (q := q) hp ht (a * t ^ σ) (b * t ^ σ)
  have e : ∀ x : ℝ, x * t ^ σ * t ^ (-σ) = x := fun x ↦ by
    rw [mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  rw [e a, e b] at hw
  exact hw.symm

/-- **Phase II, the wall**: `ℓ_t(0,b)/log t → σ√(1/q)`. -/
theorem wall_phase_wall {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t ↦ (∫ a' in (0 : ℝ)..b, Real.sqrt (fisherSpeed (volume.restrict (Ioi 0))
      (fun _ ↦ 1) (twoMonoPath p q) (twoMonoVel q) t a')) / Real.log t) atTop
      (𝓝 ((1 - q / p) * Real.sqrt (1 / q))) := by
  have hp : 0 < p := by linarith
  have h := wall_recedes hp hq hqp hb (c₀ := 0) le_rfl
  simpa only [zero_mul] using h

/-- **Phase I, across the wall**: for `a < 0 < b`, `ℓ_t(a,b)/√t → K₋(−a)`; the logarithmic
contribution of the positive side is invisible at the `√t` scale. -/
theorem wall_phase_negative {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    Tendsto (fun t ↦ (∫ a' in a..b, Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1)
      (twoMonoPath p q) (twoMonoVel q) t a')) / Real.sqrt t) atTop
      (𝓝 (negChamberConst p q (-a))) := by
  have h1 := negative_chamber_law hq hqp (A := -a) (by linarith)
  rw [neg_neg] at h1
  have h2 := wall_phase_wall hq hqp hb
  have h3 : Tendsto (fun t ↦ Real.log t / Real.sqrt t) atTop (𝓝 0) := by
    have := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.sqrt_eq_rpow]
  have h23 := h2.mul h3
  rw [mul_zero] at h23
  have h := h1.add h23
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hcont := continuous_sqrt_fisherSpeed_twoMono hq hqp (lt_trans one_pos ht)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) a 0) (hcont.intervalIntegrable (μ := volume) 0 b)]
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr (lt_trans one_pos ht)).ne'
  field_simp

end Wall

/-! ### Multiplicative self-similarity of the featureless ray -/

/-- **The ray is self-similar in log-temperature**: under regular variation of index `−λ`,
`∫_{cu}^{du} √Var_v dv → √λ log(d/c)`. -/
theorem tendsto_ray_length_dilation (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 3 ≤ K)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) {lam : ℝ} (hlam : 0 < lam) (hreg : RegVar ν lam)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun u ↦ ∫ v in (c * u)..(d * u), Real.sqrt (lawVar ν v)) atTop
      (𝓝 (Real.sqrt lam * Real.log (d / c))) := by
  have hcont : ContinuousOn (fun v ↦ Real.sqrt (lawVar ν v)) (Ioi 0) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_lawVar ν hpos hint hK hZ)
  have hint2 : ∀ u > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(u * ℓ))) ν :=
    fun u hu k hk ↦ hint u hu k (by omega)
  have hlim : Tendsto (fun v ↦ v * Real.sqrt (lawVar ν v)) atTop (𝓝 (Real.sqrt lam)) := by
    have := (Real.continuous_sqrt.tendsto _).comp
      (tendsto_sq_mul_lawVar_of_regVar ν hpos hint2 hZ hlam hreg)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    simp only [Function.comp_apply]
    rw [Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv]
  exact tendsto_intervalIntegral_dilation hcont hlim hc hcd

end Laplace.Multi
