/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.DivisorData

/-!
# The dominated rescaling lemma

The analytic interface of the relative push-forward statement in its abstract form (Astra's item A,
germbij_slop S14): a family of rescaled phases `G t u ≥ 0` converging pointwise to `Φ₀ u`, a family
of weights `w t u` (prior times fibre density, read in the rescaled variable) converging pointwise
to `w₀ u` and bounded by `W u`, a comparability bound `c Φ₀ ≤ G t` where the weight is nonzero, and
integrability of `W e^{-cΦ₀}`, `W Φ₀ e^{-cΦ₀}`. Then `∫ w_t g e^{-G_t}` and `∫ w_t g G_t e^{-G_t}`
converge to the Boltzmann quantities of `Φ₀` for every bounded measurable `g`
(`RescaledData.tendsto_den`, `RescaledData.tendsto_num`), hence so do the energy statistic and every
bounded observable (`RescaledData.tendsto_energy`, `RescaledData.tendsto_expectation`).
`DivisorData` is the instance `G t u = t F(t^{-α}u, σ t^{-γ})`, `w t u = χ(t^{-α}u)|u|^h`
(`DivisorData.toRescaledData`); the two-well theorem is another instance with a moving centre.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {T : Type*}

/-- Hypotheses of the dominated rescaling lemma, on a fibre `(X, μ)`, along a filter `l` on the
index (a schedule `t → ∞`, or a sequence). Nonnegativity and the comparability bound are only
required where the weight is nonzero. -/
structure RescaledData (l : Filter T) (μ : Measure X) (G w : T → X → ℝ) (Φ₀ w₀ W : X → ℝ)
    (c : ℝ) : Prop where
  hc : 0 < c
  hc1 : c ≤ 1
  G_meas : ∀ t, Measurable (G t)
  w_meas : ∀ t, Measurable (w t)
  G_nonneg : ∀ᶠ t in l, ∀ u, w t u ≠ 0 → 0 ≤ G t u
  Φ₀_nonneg : ∀ u, 0 ≤ Φ₀ u
  G_lim : ∀ u, Tendsto (fun t ↦ G t u) l (𝓝 (Φ₀ u))
  w_lim : ∀ u, Tendsto (fun t ↦ w t u) l (𝓝 (w₀ u))
  w_bd : ∀ t u, |w t u| ≤ W u
  lower : ∀ᶠ t in l, ∀ u, w t u ≠ 0 → c * Φ₀ u ≤ G t u
  int : Integrable (fun u ↦ W u * Real.exp (-(c * Φ₀ u))) μ
  Φint : Integrable (fun u ↦ W u * (Φ₀ u * Real.exp (-(c * Φ₀ u)))) μ

namespace RescaledData

variable {l : Filter T} [l.IsCountablyGenerated] {μ : Measure X} {G w : T → X → ℝ}
  {Φ₀ w₀ W : X → ℝ} {c : ℝ}

omit [l.IsCountablyGenerated] in
theorem W_nonneg (hd : RescaledData l μ G w Φ₀ w₀ W c) (t : T) (u : X) : 0 ≤ W u :=
  (abs_nonneg _).trans (hd.w_bd t u)

theorem Φ₀_meas [l.NeBot] (hd : RescaledData l μ G w Φ₀ w₀ W c) : Measurable Φ₀ :=
  measurable_of_tendsto_metrizable' l hd.G_meas (tendsto_pi_nhds.mpr hd.G_lim)

theorem w₀_meas [l.NeBot] (hd : RescaledData l μ G w Φ₀ w₀ W c) : Measurable w₀ :=
  measurable_of_tendsto_metrizable' l hd.w_meas (tendsto_pi_nhds.mpr hd.w_lim)

/-- Pointwise domination of the weighted Boltzmann factor. -/
theorem bound_den (hd : RescaledData l μ G w Φ₀ w₀ W c) {t : T}
    (hl : ∀ u, w t u ≠ 0 → c * Φ₀ u ≤ G t u) (u : X) :
    |w t u| * Real.exp (-(G t u)) ≤ W u * Real.exp (-(c * Φ₀ u)) := by
  by_cases hw : w t u = 0
  · rw [hw, abs_zero, zero_mul]
    exact mul_nonneg (hd.W_nonneg t u) (Real.exp_pos _).le
  · exact mul_le_mul (hd.w_bd t u) (Real.exp_le_exp.mpr (by linarith [hl u hw]))
      (Real.exp_pos _).le (hd.W_nonneg t u)

/-- Pointwise domination of the weighted energy density. -/
theorem bound_num (hd : RescaledData l μ G w Φ₀ w₀ W c) {t : T}
    (hl : ∀ u, w t u ≠ 0 → c * Φ₀ u ≤ G t u) (hG : ∀ u, w t u ≠ 0 → 0 ≤ G t u) (u : X) :
    |w t u * (G t u * Real.exp (-(G t u)))| ≤
      W u * (c * Φ₀ u * Real.exp (-(c * Φ₀ u)) + Real.exp (-(c * Φ₀ u))) := by
  have hz : 0 ≤ c * Φ₀ u := mul_nonneg hd.hc.le (hd.Φ₀_nonneg u)
  by_cases hw : w t u = 0
  · rw [hw, zero_mul, abs_zero]
    exact mul_nonneg (hd.W_nonneg t u) (by positivity)
  · rw [abs_mul, abs_of_nonneg (mul_nonneg (hG u hw) (Real.exp_pos _).le)]
    exact mul_le_mul (hd.w_bd t u) (mul_exp_neg_le_of_le hz (hl u hw))
      (mul_nonneg (hG u hw) (Real.exp_pos _).le) (hd.W_nonneg t u)

/-- Integrability of the weighted Boltzmann factor where the comparability bound holds. -/
theorem integrable_den (hd : RescaledData l μ G w Φ₀ w₀ W c) {t : T}
    (hl : ∀ u, w t u ≠ 0 → c * Φ₀ u ≤ G t u) :
    Integrable (fun u ↦ w t u * Real.exp (-(G t u))) μ := by
  have h1 := hd.w_meas t
  have h2 := hd.G_meas t
  refine hd.int.mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun u ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  exact hd.bound_den hl u

/-- Integrability of the weighted energy density where the comparability bound holds. -/
theorem integrable_num (hd : RescaledData l μ G w Φ₀ w₀ W c) {t : T}
    (hl : ∀ u, w t u ≠ 0 → c * Φ₀ u ≤ G t u) (hG : ∀ u, w t u ≠ 0 → 0 ≤ G t u) :
    Integrable (fun u ↦ w t u * (G t u * Real.exp (-(G t u)))) μ := by
  have h1 := hd.w_meas t
  have h2 := hd.G_meas t
  have hdom : Integrable (fun u ↦
      W u * (c * Φ₀ u * Real.exp (-(c * Φ₀ u)) + Real.exp (-(c * Φ₀ u)))) μ := by
    refine ((hd.Φint.const_mul c).add hd.int).congr (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [Pi.add_apply]
    ring
  refine hdom.mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun u ↦ ?_)
  rw [Real.norm_eq_abs]
  exact hd.bound_num hl hG u

/-- Weighted partition function / bounded observable. -/
theorem tendsto_den (hd : RescaledData l μ G w Φ₀ w₀ W c) {g : X → ℝ} (hg : Measurable g) {Mg : ℝ}
    (hMg : ∀ u, |g u| ≤ Mg) (hMg0 : 0 ≤ Mg) :
    Tendsto (fun t ↦ ∫ u, w t u * (g u * Real.exp (-(G t u))) ∂μ) l
      (𝓝 (∫ u, w₀ u * (g u * Real.exp (-Φ₀ u)) ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u ↦ Mg * (W u * Real.exp (-(c * Φ₀ u)))) (Filter.Eventually.of_forall fun t ↦ ?_) ?_
    (hd.int.const_mul Mg) (Filter.Eventually.of_forall fun u ↦ ?_)
  · have h1 := hd.w_meas t
    have h2 := hd.G_meas t
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [hd.lower] with t hl
    refine Filter.Eventually.of_forall fun u ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp]
    calc |w t u| * (|g u| * Real.exp (-(G t u)))
        = |g u| * (|w t u| * Real.exp (-(G t u))) := by ring
      _ ≤ Mg * (W u * Real.exp (-(c * Φ₀ u))) :=
          mul_le_mul (hMg u) (hd.bound_den hl u) (by positivity) hMg0
  · exact (hd.w_lim u).mul (tendsto_const_nhds.mul
      ((Real.continuous_exp.tendsto _).comp (hd.G_lim u).neg))

/-- Weighted energy numerator. -/
theorem tendsto_num (hd : RescaledData l μ G w Φ₀ w₀ W c) {g : X → ℝ} (hg : Measurable g) {Mg : ℝ}
    (hMg : ∀ u, |g u| ≤ Mg) (hMg0 : 0 ≤ Mg) :
    Tendsto (fun t ↦ ∫ u, w t u * (g u * (G t u * Real.exp (-(G t u)))) ∂μ) l
      (𝓝 (∫ u, w₀ u * (g u * (Φ₀ u * Real.exp (-Φ₀ u))) ∂μ)) := by
  have hdom : Integrable (fun u ↦
      Mg * (W u * (c * Φ₀ u * Real.exp (-(c * Φ₀ u)) + Real.exp (-(c * Φ₀ u))))) μ := by
    refine (((hd.Φint.const_mul c).add hd.int).const_mul Mg).congr
      (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [Pi.add_apply]
    ring
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u ↦ Mg * (W u * (c * Φ₀ u * Real.exp (-(c * Φ₀ u)) + Real.exp (-(c * Φ₀ u)))))
    (Filter.Eventually.of_forall fun t ↦ ?_) ?_ hdom (Filter.Eventually.of_forall fun u ↦ ?_)
  · have h1 := hd.w_meas t
    have h2 := hd.G_meas t
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [hd.lower, hd.G_nonneg] with t hl hG
    refine Filter.Eventually.of_forall fun u ↦ ?_
    calc ‖w t u * (g u * (G t u * Real.exp (-(G t u))))‖
        = |g u| * |w t u * (G t u * Real.exp (-(G t u)))| := by
          simp only [Real.norm_eq_abs, abs_mul]; ring
      _ ≤ Mg * (W u * (c * Φ₀ u * Real.exp (-(c * Φ₀ u)) + Real.exp (-(c * Φ₀ u)))) :=
          mul_le_mul (hMg u) (hd.bound_num hl hG u) (abs_nonneg _) hMg0
  · exact (hd.w_lim u).mul (tendsto_const_nhds.mul
      ((hd.G_lim u).mul ((Real.continuous_exp.tendsto _).comp (hd.G_lim u).neg)))

/-- The energy statistic of the rescaled family converges to the Boltzmann energy of `Φ₀`. -/
theorem tendsto_energy (hd : RescaledData l μ G w Φ₀ w₀ W c)
    (hpos : ∫ u, w₀ u * Real.exp (-Φ₀ u) ∂μ ≠ 0) :
    Tendsto (fun t ↦ (∫ u, w t u * (G t u * Real.exp (-(G t u))) ∂μ) /
      ∫ u, w t u * Real.exp (-(G t u)) ∂μ) l
      (𝓝 ((∫ u, w₀ u * (Φ₀ u * Real.exp (-Φ₀ u)) ∂μ) / ∫ u, w₀ u * Real.exp (-Φ₀ u) ∂μ)) := by
  have hN := hd.tendsto_num (g := fun _ ↦ (1 : ℝ)) measurable_const (Mg := 1) (fun _ ↦ by simp)
    zero_le_one
  have hD := hd.tendsto_den (g := fun _ ↦ (1 : ℝ)) measurable_const (Mg := 1) (fun _ ↦ by simp)
    zero_le_one
  simp only [one_mul] at hN hD
  exact hN.div hD hpos

/-- Every bounded observable of the rescaled family converges to its Boltzmann expectation. -/
theorem tendsto_expectation (hd : RescaledData l μ G w Φ₀ w₀ W c)
    (hpos : ∫ u, w₀ u * Real.exp (-Φ₀ u) ∂μ ≠ 0) {g : X → ℝ} (hg : Measurable g) {Mg : ℝ}
    (hMg : ∀ u, |g u| ≤ Mg) (hMg0 : 0 ≤ Mg) :
    Tendsto (fun t ↦ (∫ u, w t u * (g u * Real.exp (-(G t u))) ∂μ) /
      ∫ u, w t u * Real.exp (-(G t u)) ∂μ) l
      (𝓝 ((∫ u, w₀ u * (g u * Real.exp (-Φ₀ u)) ∂μ) / ∫ u, w₀ u * Real.exp (-Φ₀ u) ∂μ)) := by
  have hN := hd.tendsto_den hg hMg hMg0
  have hD := hd.tendsto_den (g := fun _ ↦ (1 : ℝ)) measurable_const (Mg := 1) (fun _ ↦ by simp)
    zero_le_one
  simp only [one_mul] at hD
  exact hN.div hD hpos

end RescaledData

/-- `DivisorData` is an instance of the dominated rescaling lemma. -/
theorem DivisorData.toRescaledData {F : ℝ → ℝ → ℝ} {Φ₀ : ℝ → ℝ} {α γ σ c : ℝ} {h : ℕ}
    (hd : DivisorData F Φ₀ α γ σ c h) {χ : ℝ → ℝ} (hχ : Cutoff χ) {M : ℝ}
    (hM : ∀ x, |χ x| ≤ M) :
    RescaledData atTop volume (fun t u ↦ t * F (t ^ (-α) * u) (σ * t ^ (-γ)))
      (fun t u ↦ χ (t ^ (-α) * u) * |u| ^ h) Φ₀ (fun u ↦ χ 0 * |u| ^ h) (fun u ↦ M * |u| ^ h)
      c where
  hc := hd.hc
  hc1 := hd.hc1
  G_meas := fun t ↦ (hd.continuous_rescaled t).measurable
  w_meas := fun t ↦ by
    have := hχ.cont
    fun_prop
  G_nonneg := by
    filter_upwards [eventually_gt_atTop 0] with t ht u _
    exact mul_nonneg ht.le (hd.F_nonneg _ _)
  Φ₀_nonneg := hd.Φ₀_nonneg
  G_lim := hd.lim
  w_lim := fun u ↦ (hd.tendsto_scaled_cutoff hχ u).mul_const _
  w_bd := fun t u ↦ by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (abs_nonneg u) h)]
    exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
  lower := by
    filter_upwards [hd.lower] with t hl u _
    exact hl u
  int := by simpa [mul_assoc] using hd.int.const_mul M
  Φint := by simpa [mul_assoc] using hd.Φint.const_mul M

end Laplace.Multi
