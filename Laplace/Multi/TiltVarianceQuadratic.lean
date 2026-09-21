/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TiltVariance

/-!
# The `q = 2` law: centering at the empirical score

Split the residual `R = K − L` at the minimizer into its value, its linear part `ℓ = ∇R(p)` and
a quadratic remainder `|R(w) − R(p) − ℓ(w − p)| ≤ ρ₂ ‖w − p‖²`. Interpolating between the
score-tilted population loss `L + ℓ(· − p)` and `L + R`, the tilted fourth moment
`E_u ‖w − p‖⁴` is `O(1/t²)` uniformly in `u` (for `‖ℓ‖² t ≤ 1`, `ρ₂ ≤ c/2`), so
`Var_u(remainder) ≤ ρ₂² C₄ / t²` and the interpolation bound gives

  `|⟨φ⟩_{L+R,t} − ⟨φ⟩_{L + ℓ(·−p), t}| ≤ ‖φ‖_∞ · ρ₂ · √C₄`,

uniformly in the temperature (`abs_winExp_sub_le_quadratic`). For an empirical residual the
Hessian fluctuation `ρ₂ ≍ n^{-1/2}` and the score `‖ℓ‖ ≍ n^{-1/2}` are the statistical inputs;
the condition `‖ℓ‖² t ≤ 1` is admissibility `t ≲ n`. So up to the random linear tilt by the
empirical score, the empirical expectations are within `O(n^{-1/2})` of the population ones at
every temperature up to the posterior one.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {d : ℕ}

/-- `‖y‖^n e^{-a‖y‖² + b‖y‖}` is integrable. -/
theorem integrable_pow_mul_exp_lin (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    Integrable fun y : EuclidD d ↦ ‖y‖ ^ n * Real.exp (-(a * ‖y‖ ^ 2) + b * ‖y‖) := by
  have hdom := (integrable_pow_mul_exp_neg_mul_sq (d := d) (half_pos ha) n).const_mul
    (Real.exp (b ^ 2 / (2 * a)))
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y ↦ ?_)
  · exact ((continuous_norm.pow n).mul (Real.continuous_exp.comp
      (((continuous_norm.pow 2).const_mul a).neg.add (continuous_norm.const_mul b))))
      |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hkey : -(a * ‖y‖ ^ 2) + b * ‖y‖ ≤ b ^ 2 / (2 * a) + -(a / 2) * ‖y‖ ^ 2 := by
      rw [← sub_nonneg]
      have : b ^ 2 / (2 * a) + -(a / 2) * ‖y‖ ^ 2 - (-(a * ‖y‖ ^ 2) + b * ‖y‖) =
          (b - a * ‖y‖) ^ 2 / (2 * a) := by
        field_simp
        ring
      rw [this]
      positivity
    calc ‖y‖ ^ n * Real.exp (-(a * ‖y‖ ^ 2) + b * ‖y‖)
        ≤ ‖y‖ ^ n * Real.exp (b ^ 2 / (2 * a) + -(a / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) (by positivity)
      _ = Real.exp (b ^ 2 / (2 * a)) * (‖y‖ ^ n * Real.exp (-(a / 2) * ‖y‖ ^ 2)) := by
          rw [Real.exp_add]
          ring

/-- `I₄ = ∫ ‖z‖⁴ e^{-(c/2)‖z‖² + ‖z‖}`. -/
noncomputable def gaussLinConst4 (c : ℝ) : ℝ :=
  ∫ z : EuclidD d, ‖z‖ ^ 4 * Real.exp (-(c / 2 * ‖z‖ ^ 2) + 1 * ‖z‖)

namespace NondegWindow

variable {p : EuclidD d} {χ L : EuclidD d → ℝ} {r₀ c C₀ : ℝ} (h : NondegWindow p χ L r₀ c C₀)

/-- The score-tilted population weight `χ e^{-t(L − L(p) + ℓ(w − p))}`. -/
noncomputable def weightLin (_h : NondegWindow p χ L r₀ c C₀) (ℓ : EuclidD d →L[ℝ] ℝ) (t : ℝ)
    (w : EuclidD d) : ℝ := χ w * Real.exp (-(t * (L w - L p + ℓ (w - p))))

/-- The truncated quadratic remainder `1_{supp χ} (R − R(p) − ℓ(w − p))`. -/
noncomputable def resid2 (_h : NondegWindow p χ L r₀ c C₀) (ℓ : EuclidD d →L[ℝ] ℝ)
    (R : EuclidD d → ℝ) (w : EuclidD d) : ℝ :=
  (tsupport χ).indicator (fun w ↦ R w - R p - ℓ (w - p)) w

/-- The truncated fourth power `1_{supp χ} ‖w − p‖⁴`. -/
noncomputable def quart (_h : NondegWindow p χ L r₀ c C₀) (w : EuclidD d) : ℝ :=
  (tsupport χ).indicator (fun w ↦ ‖w - p‖ ^ 4) w

include h

theorem weightLin_nonneg (ℓ : EuclidD d →L[ℝ] ℝ) (t : ℝ) (w : EuclidD d) :
    0 ≤ h.weightLin ℓ t w := mul_nonneg (h.χ_nonneg w) (Real.exp_pos _).le

theorem weightLin_measurable (ℓ : EuclidD d →L[ℝ] ℝ) (t : ℝ) : Measurable (h.weightLin ℓ t) := by
  unfold weightLin
  exact h.χ_cont.measurable.mul (Real.measurable_exp.comp
    ((((h.L_cont.measurable.sub measurable_const).add
      (ℓ.continuous.comp (continuous_id.sub continuous_const)).measurable).const_mul t).neg))

theorem weightLin_integrable (ℓ : EuclidD d →L[ℝ] ℝ) (t : ℝ) : Integrable (h.weightLin ℓ t) := by
  unfold weightLin
  have hc : Continuous fun w ↦ χ w * Real.exp (-(t * (L w - L p + ℓ (w - p)))) :=
    h.χ_cont.mul (Real.continuous_exp.comp ((((h.L_cont.sub continuous_const).add
      (ℓ.continuous.comp (continuous_id.sub continuous_const))).const_mul t).neg))
  exact hc.integrable_of_hasCompactSupport h.χ_supp.mul_right

theorem weightLin_eq_zero_of_notMem (ℓ : EuclidD d →L[ℝ] ℝ) (t : ℝ) {w : EuclidD d}
    (hw : w ∉ tsupport χ) : h.weightLin ℓ t w = 0 := by
  unfold weightLin
  rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]

theorem resid2_measurable (ℓ : EuclidD d →L[ℝ] ℝ) {R : EuclidD d → ℝ} (hRm : Measurable R) :
    Measurable (h.resid2 ℓ R) :=
  ((hRm.sub measurable_const).sub (ℓ.continuous.comp
    (continuous_id.sub continuous_const)).measurable).indicator (isClosed_tsupport χ).measurableSet

theorem abs_resid2_le (ℓ : EuclidD d →L[ℝ] ℝ) {R : EuclidD d → ℝ} {ρ₂ : ℝ} (hρ₂ : 0 ≤ ρ₂)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) (w : EuclidD d) :
    |h.resid2 ℓ R w| ≤ ρ₂ * ‖w - p‖ ^ 2 := by
  unfold resid2
  by_cases hw : w ∈ tsupport χ
  · rw [Set.indicator_of_mem hw]
    exact hR w
  · rw [Set.indicator_of_notMem hw, abs_zero]
    positivity

theorem resid2_bound (ℓ : EuclidD d →L[ℝ] ℝ) {R : EuclidD d → ℝ} {ρ₂ D : ℝ} (hρ₂ : 0 ≤ ρ₂)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D)
    (w : EuclidD d) : |h.resid2 ℓ R w| ≤ ρ₂ * D ^ 2 := by
  unfold resid2
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD p h.p_mem_tsupport)
  by_cases hw : w ∈ tsupport χ
  · rw [Set.indicator_of_mem hw]
    exact (hR w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hD w hw) 2) hρ₂)
  · rw [Set.indicator_of_notMem hw, abs_zero]
    positivity

theorem quart_measurable : Measurable h.quart :=
  ((continuous_id.sub continuous_const).norm.pow 4).measurable.indicator
    (isClosed_tsupport χ).measurableSet

theorem quart_bound {D : ℝ} (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D) (w : EuclidD d) :
    |h.quart w| ≤ D ^ 4 := by
  unfold quart
  by_cases hw : w ∈ tsupport χ
  · rw [Set.indicator_of_mem hw, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hD w hw) 4
  · rw [Set.indicator_of_notMem hw, abs_zero]
    have := le_trans (norm_nonneg _) (hD p h.p_mem_tsupport)
    positivity

theorem exp_tilt2_le (ℓ : EuclidD d →L[ℝ] ℝ) {R : EuclidD d → ℝ} {ρ₂ D : ℝ} (hρ₂ : 0 ≤ ρ₂)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D)
    {t : ℝ} (ht0 : 0 ≤ t) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (w : EuclidD d) :
    Real.exp (-(t * h.resid2 ℓ R w * u)) ≤ Real.exp (t * (ρ₂ * D ^ 2)) := by
  have hb := abs_le.mp (h.resid2_bound ℓ hρ₂ hR hD w)
  have hD0 : 0 ≤ ρ₂ * D ^ 2 := le_trans (abs_nonneg _) (h.resid2_bound ℓ hρ₂ hR hD p)
  rw [Real.exp_le_exp]
  obtain ⟨hu0, hu1⟩ := hu
  have hpos : 0 ≤ h.resid2 ℓ R w + ρ₂ * D ^ 2 := by linarith [hb.1]
  nlinarith [mul_nonneg ht0 hu0, mul_nonneg (mul_nonneg ht0 hu0) hpos, mul_nonneg ht0 hD0]

theorem integrable_tilt2_of_bound (ℓ : EuclidD d →L[ℝ] ℝ) {R : EuclidD d → ℝ}
    (hRm : Measurable R) {ρ₂ D : ℝ} (hρ₂ : 0 ≤ ρ₂)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D)
    {t : ℝ} (ht0 : 0 ≤ t) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) {g : EuclidD d → ℝ}
    (hgm : Measurable g) {Mg : ℝ} (hg : ∀ w, |g w| ≤ Mg) :
    Integrable fun w ↦ g w * Real.exp (-(t * h.resid2 ℓ R w * u)) * h.weightLin ℓ t w := by
  refine (h.weightLin_integrable ℓ t).bdd_mul (c := Mg * Real.exp (t * (ρ₂ * D ^ 2))) ?_
    (Filter.Eventually.of_forall fun w ↦ ?_)
  · exact (hgm.mul (Real.measurable_exp.comp
      ((((h.resid2_measurable ℓ hRm).const_mul t).mul_const u).neg))) |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_mul (hg w) (h.exp_tilt2_le ℓ hρ₂ hR hD ht0 hu w) (Real.exp_pos _).le
      (le_trans (abs_nonneg _) (hg w))

/-! ### The scale parameters -/

/-- The bookkeeping for `s = t^{-1/2}`. -/
theorem scale_facts {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t) (ht1 : 1 ≤ t) :
    0 < (Real.sqrt t)⁻¹ ∧ ((Real.sqrt t)⁻¹) ^ 2 = t⁻¹ ∧ t * (Real.sqrt t)⁻¹ = Real.sqrt t ∧
      (Real.sqrt t)⁻¹ ≤ r₀ := by
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  refine ⟨inv_pos.mpr hst, ?_, ?_, ?_⟩
  · rw [inv_pow, Real.sq_sqrt ht0.le]
  · rw [← div_eq_mul_inv, Real.div_sqrt]
  · have hr₀ := h.r₀_pos
    have h1 : r₀ ^ (-2 : ℝ) = (r₀ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hr₀.le]
      norm_cast
    rw [h1] at ht
    have h2 : (r₀ ^ 2)⁻¹ * r₀ ^ 2 ≤ t * r₀ ^ 2 := mul_le_mul_of_nonneg_right ht (by positivity)
    rw [inv_mul_cancel₀ (by positivity)] at h2
    have h3 : Real.sqrt 1 ≤ Real.sqrt (t * r₀ ^ 2) := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_one, Real.sqrt_mul ht0.le, Real.sqrt_sq hr₀.le] at h3
    rw [inv_le_iff_one_le_mul₀ hst]
    linarith

omit h in
theorem sqrt_mul_le_one {γ t : ℝ} (_hγ : 0 ≤ γ) (ht0 : 0 < t) (hγt : γ ^ 2 * t ≤ 1) :
    γ * Real.sqrt t ≤ 1 := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have : (γ * Real.sqrt t) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt ht0.le]
    exact hγt
  nlinarith [this]

/-! ### The tilted normalizer from below -/

theorem tiltNum_one_lower2 (ℓ : EuclidD d →L[ℝ] ℝ) {γ : ℝ} (hℓ : ‖ℓ‖ ≤ γ)
    {R : EuclidD d → ℝ} (hRm : Measurable R) {ρ₂ : ℝ} (hρ₂ : 0 ≤ ρ₂) (hρc : ρ₂ ≤ c / 2)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t)
    (ht1 : 1 ≤ t) (hγt : γ ^ 2 * t ≤ 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-(C₀ + 1 + c / 2)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal *
        ((Real.sqrt t)⁻¹) ^ d ≤
      tiltNum volume (h.weightLin ℓ t) (fun _ ↦ 1) (h.resid2 ℓ R) t u := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hs, hs2, hts, hsr⟩ := h.scale_facts ht ht1
  set s : ℝ := (Real.sqrt t)⁻¹ with hs_def
  have hγ : 0 ≤ γ := le_trans (norm_nonneg _) hℓ
  have hγs := sqrt_mul_le_one hγ ht0 hγt
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨D, hD0, hD⟩ := h.exists_diam
  have hden_pt : ∀ w, (Metric.ball p s).indicator (fun _ ↦ Real.exp (-(C₀ + 1 + c / 2))) w ≤
      (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * h.resid2 ℓ R w * u)) * h.weightLin ℓ t w := by
    intro w
    by_cases hw : w ∈ Metric.ball p s
    · rw [Set.indicator_of_mem hw]
      have hwr : w ∈ Metric.ball p r₀ := Metric.ball_subset_ball hsr hw
      have hwt : w ∈ tsupport χ := h.ball_subset_tsupport hwr
      have hnorm : ‖w - p‖ < s := by
        rw [Metric.mem_ball, dist_eq_norm] at hw
        exact hw
      unfold resid2 weightLin
      rw [Set.indicator_of_mem hwt, h.χ_ball w hwr, one_mul, one_mul, ← Real.exp_add,
        Real.exp_le_exp]
      have hup := h.upper w hwr
      have hres := abs_le.mp (hR w)
      have hn := norm_nonneg (w - p)
      have hℓw : |ℓ (w - p)| ≤ γ * ‖w - p‖ := by
        have := ℓ.le_of_opNorm_le hℓ (w - p)
        rwa [Real.norm_eq_abs] at this
      have hsq : t * ‖w - p‖ ^ 2 ≤ 1 := by
        have : ‖w - p‖ ^ 2 ≤ s ^ 2 := by nlinarith
        rw [hs2] at this
        calc t * ‖w - p‖ ^ 2 ≤ t * t⁻¹ := mul_le_mul_of_nonneg_left this ht0.le
          _ = 1 := mul_inv_cancel₀ ht0.ne'
      have hA : t * (L w - L p) ≤ C₀ := by
        calc t * (L w - L p) ≤ t * (C₀ * ‖w - p‖ ^ 2) := mul_le_mul_of_nonneg_left hup ht0.le
          _ = C₀ * (t * ‖w - p‖ ^ 2) := by ring
          _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left hsq h.C₀_nonneg
          _ = C₀ := mul_one _
      have hB : t * ℓ (w - p) ≤ 1 := by
        calc t * ℓ (w - p) ≤ t * (γ * ‖w - p‖) :=
              mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hℓw) ht0.le
          _ ≤ t * (γ * s) := by gcongr
          _ = γ * Real.sqrt t := by rw [← hts]; ring
          _ ≤ 1 := hγs
      have hC : t * (R w - R p - ℓ (w - p)) * u ≤ c / 2 := by
        calc t * (R w - R p - ℓ (w - p)) * u ≤ t * (ρ₂ * ‖w - p‖ ^ 2) * 1 := by
              have h1 : t * (R w - R p - ℓ (w - p)) ≤ t * (ρ₂ * ‖w - p‖ ^ 2) :=
                mul_le_mul_of_nonneg_left hres.2 ht0.le
              exact mul_le_mul h1 hu1 hu0 (by positivity)
          _ = ρ₂ * (t * ‖w - p‖ ^ 2) := by ring
          _ ≤ ρ₂ * 1 := mul_le_mul_of_nonneg_left hsq hρ₂
          _ ≤ c / 2 := by linarith
      linarith
    · rw [Set.indicator_of_notMem hw]
      exact mul_nonneg (mul_nonneg zero_le_one (Real.exp_pos _).le) (h.weightLin_nonneg ℓ t w)
  have hind : Integrable
      ((Metric.ball p s).indicator fun _ : EuclidD d ↦ Real.exp (-(C₀ + 1 + c / 2))) :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      (integrableOn_const measure_ball_lt_top.ne)
  have hint := h.integrable_tilt2_of_bound ℓ hRm hρ₂ hR hD ht0.le ⟨hu0, hu1⟩ measurable_const
    (Mg := 1) (fun _ ↦ abs_one.le)
  have hmono := integral_mono hind hint hden_pt
  rw [integral_indicator_const _ Metric.isOpen_ball.measurableSet, smul_eq_mul, measureReal_def,
    Measure.addHaar_ball_of_pos volume p hs, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hmono
  have hfold : tiltNum volume (h.weightLin ℓ t) (fun _ ↦ 1) (h.resid2 ℓ R) t u =
      ∫ w, (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * h.resid2 ℓ R w * u)) * h.weightLin ℓ t w := rfl
  rw [hfold]
  calc Real.exp (-(C₀ + 1 + c / 2)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal * s ^ d
      = s ^ d * (volume (Metric.ball (0 : EuclidD d) 1)).toReal * Real.exp (-(C₀ + 1 + c / 2)) := by
        ring
    _ ≤ _ := hmono

/-! ### The tilted fourth moment from above -/

theorem tiltNum_quart_upper (ℓ : EuclidD d →L[ℝ] ℝ) {γ : ℝ} (hℓ : ‖ℓ‖ ≤ γ)
    {R : EuclidD d → ℝ} (hRm : Measurable R) {ρ₂ : ℝ} (hρ₂ : 0 ≤ ρ₂) (hρc : ρ₂ ≤ c / 2)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t)
    (ht1 : 1 ≤ t) (hγt : γ ^ 2 * t ≤ 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    tiltNum volume (h.weightLin ℓ t) h.quart (h.resid2 ℓ R) t u ≤
      ((Real.sqrt t)⁻¹) ^ d * ((t ^ 2)⁻¹ * gaussLinConst4 (d := d) c) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hs, hs2, hts, _⟩ := h.scale_facts ht ht1
  set s : ℝ := (Real.sqrt t)⁻¹ with hs_def
  have hγ : 0 ≤ γ := le_trans (norm_nonneg _) hℓ
  have hγs := sqrt_mul_le_one hγ ht0 hγt
  have hc2 : 0 < c / 2 := half_pos h.c_pos
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨D, hD0, hD⟩ := h.exists_diam
  have hnum_pt : ∀ w, h.quart w * Real.exp (-(t * h.resid2 ℓ R w * u)) * h.weightLin ℓ t w ≤
      ‖w - p‖ ^ 4 * Real.exp (-(t * (c / 2) * ‖w - p‖ ^ 2) + t * γ * ‖w - p‖) := by
    intro w
    by_cases hw : w ∈ tsupport χ
    · unfold quart resid2 weightLin
      rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      have hcoer := h.coer w hw
      have hres := abs_le.mp (hR w)
      have hχ := h.χ_le_one w
      have hχ0 := h.χ_nonneg w
      have hn := norm_nonneg (w - p)
      have hℓw : |ℓ (w - p)| ≤ γ * ‖w - p‖ := by
        have := ℓ.le_of_opNorm_le hℓ (w - p)
        rwa [Real.norm_eq_abs] at this
      have he : Real.exp (-(t * (R w - R p - ℓ (w - p)) * u)) *
          Real.exp (-(t * (L w - L p + ℓ (w - p)))) ≤
          Real.exp (-(t * (c / 2) * ‖w - p‖ ^ 2) + t * γ * ‖w - p‖) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        have h1 : t * c * ‖w - p‖ ^ 2 ≤ t * (L w - L p) := by
          have := mul_le_mul_of_nonneg_left hcoer ht0.le
          linarith
        have h2 : -(t * ℓ (w - p)) ≤ t * γ * ‖w - p‖ := by
          have := mul_le_mul_of_nonneg_left (le_trans (neg_le_abs _) hℓw) ht0.le
          linarith
        have h3 : -(t * (R w - R p - ℓ (w - p)) * u) ≤ t * (c / 2) * ‖w - p‖ ^ 2 := by
          have ha : -(R w - R p - ℓ (w - p)) ≤ ρ₂ * ‖w - p‖ ^ 2 := by linarith [hres.1]
          have hb : t * u * (-(R w - R p - ℓ (w - p))) ≤ t * u * (ρ₂ * ‖w - p‖ ^ 2) :=
            mul_le_mul_of_nonneg_left ha (mul_nonneg ht0.le hu0)
          have hc' : t * u * (ρ₂ * ‖w - p‖ ^ 2) ≤ t * 1 * (c / 2 * ‖w - p‖ ^ 2) := by
            have : ρ₂ * ‖w - p‖ ^ 2 ≤ c / 2 * ‖w - p‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hρc (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_left hu1 ht0.le) this (by positivity)
              (by positivity)
          nlinarith
        nlinarith
      calc ‖w - p‖ ^ 4 * Real.exp (-(t * (R w - R p - ℓ (w - p)) * u)) *
            (χ w * Real.exp (-(t * (L w - L p + ℓ (w - p)))))
          ≤ ‖w - p‖ ^ 4 * Real.exp (-(t * (R w - R p - ℓ (w - p)) * u)) *
            (1 * Real.exp (-(t * (L w - L p + ℓ (w - p))))) := by
            gcongr
        _ = ‖w - p‖ ^ 4 * (Real.exp (-(t * (R w - R p - ℓ (w - p)) * u)) *
            Real.exp (-(t * (L w - L p + ℓ (w - p))))) := by
            ring
        _ ≤ ‖w - p‖ ^ 4 * Real.exp (-(t * (c / 2) * ‖w - p‖ ^ 2) + t * γ * ‖w - p‖) :=
            mul_le_mul_of_nonneg_left he (by positivity)
    · rw [h.weightLin_eq_zero_of_notMem ℓ t hw, mul_zero]
      positivity
  have hmaj_int : Integrable fun w : EuclidD d ↦
      ‖w - p‖ ^ 4 * Real.exp (-(t * (c / 2) * ‖w - p‖ ^ 2) + t * γ * ‖w - p‖) :=
    (integrable_pow_mul_exp_lin (d := d) 4 (b := t * γ) (mul_pos ht0 hc2)).comp_sub_right p
  have hint := h.integrable_tilt2_of_bound ℓ hRm hρ₂ hR hD ht0.le ⟨hu0, hu1⟩ h.quart_measurable
    (h.quart_bound hD)
  have hmono := integral_mono hint hmaj_int hnum_pt
  have hmaj_val : (∫ w : EuclidD d, ‖w - p‖ ^ 4 *
      Real.exp (-(t * (c / 2) * ‖w - p‖ ^ 2) + t * γ * ‖w - p‖)) ≤
      s ^ d * ((t ^ 2)⁻¹ * gaussLinConst4 (d := d) c) := by
    rw [integral_sub_right_eq_self (fun y : EuclidD d ↦ ‖y‖ ^ 4 *
      Real.exp (-(t * (c / 2) * ‖y‖ ^ 2) + t * γ * ‖y‖)) p]
    have hscale := Measure.integral_comp_smul (volume : Measure (EuclidD d))
      (fun y : EuclidD d ↦ ‖y‖ ^ 4 * Real.exp (-(t * (c / 2) * ‖y‖ ^ 2) + t * γ * ‖y‖)) s
    rw [finrank_euclideanSpace_fin, smul_eq_mul, abs_of_pos (by positivity)] at hscale
    have hF : (∫ y : EuclidD d, ‖y‖ ^ 4 * Real.exp (-(t * (c / 2) * ‖y‖ ^ 2) + t * γ * ‖y‖)) =
        s ^ d * ∫ z : EuclidD d, ‖s • z‖ ^ 4 *
          Real.exp (-(t * (c / 2) * ‖s • z‖ ^ 2) + t * γ * ‖s • z‖) := by
      rw [hscale, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    rw [hF]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold gaussLinConst4
    rw [← integral_const_mul]
    have hintz : Integrable fun z : EuclidD d ↦ ‖s • z‖ ^ 4 *
        Real.exp (-(t * (c / 2) * ‖s • z‖ ^ 2) + t * γ * ‖s • z‖) :=
      (integrable_pow_mul_exp_lin (d := d) 4 (b := t * γ) (mul_pos ht0 hc2)).comp_smul hs.ne'
    refine integral_mono hintz
      ((integrable_pow_mul_exp_lin (d := d) 4 (b := 1) hc2).const_mul _) fun z ↦ ?_
    beta_reduce
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, mul_pow, hs2]
    have hz := norm_nonneg z
    have hs4 : (t⁻¹) ^ 2 = (t ^ 2)⁻¹ := by rw [inv_pow]
    have hexp : Real.exp (-(t * (c / 2) * (t⁻¹ * ‖z‖ ^ 2)) + t * γ * (s * ‖z‖)) ≤
        Real.exp (-(c / 2 * ‖z‖ ^ 2) + 1 * ‖z‖) := by
      rw [Real.exp_le_exp]
      have h1 : t * (c / 2) * (t⁻¹ * ‖z‖ ^ 2) = c / 2 * ‖z‖ ^ 2 := by
        field_simp
      have h2 : t * γ * (s * ‖z‖) = (γ * Real.sqrt t) * ‖z‖ := by
        rw [← hts]
        ring
      rw [h1, h2]
      have : (γ * Real.sqrt t) * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hγs hz
      linarith
    have hpow : (s ^ 4 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hs2, inv_pow]
    calc s ^ 4 * ‖z‖ ^ 4 * Real.exp (-(t * (c / 2) * (t⁻¹ * ‖z‖ ^ 2)) + t * γ * (s * ‖z‖))
        ≤ s ^ 4 * ‖z‖ ^ 4 * Real.exp (-(c / 2 * ‖z‖ ^ 2) + 1 * ‖z‖) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (t ^ 2)⁻¹ * (‖z‖ ^ 4 * Real.exp (-(c / 2 * ‖z‖ ^ 2) + 1 * ‖z‖)) := by
          rw [hpow]
          ring
  exact hmono.trans hmaj_val

/-- The constant `C₄ = I₄ e^{C₀ + 1 + c/2} / vol B(0,1)`. -/
noncomputable def cstar4 (d : ℕ) (c C₀ : ℝ) : ℝ :=
  gaussLinConst4 (d := d) c * Real.exp (C₀ + 1 + c / 2) /
    (volume (Metric.ball (0 : EuclidD d) 1)).toReal

/-- **The tilted fourth moment is `O(1/t²)` uniformly in the interpolation parameter.** -/
theorem tiltExp_quart_le (ℓ : EuclidD d →L[ℝ] ℝ) {γ : ℝ} (hℓ : ‖ℓ‖ ≤ γ) {R : EuclidD d → ℝ}
    (hRm : Measurable R) {ρ₂ : ℝ} (hρ₂ : 0 ≤ ρ₂) (hρc : ρ₂ ≤ c / 2)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t)
    (ht1 : 1 ≤ t) (hγt : γ ^ 2 * t ≤ 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    tiltExp volume (h.weightLin ℓ t) h.quart (h.resid2 ℓ R) t u ≤ cstar4 d c C₀ / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hlow := h.tiltNum_one_lower2 ℓ hℓ hRm hρ₂ hρc hR ht ht1 hγt hu
  have hup := h.tiltNum_quart_upper ℓ hℓ hRm hρ₂ hρc hR ht ht1 hγt hu
  have hv : 0 < (volume (Metric.ball (0 : EuclidD d) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
  have hs : 0 < ((Real.sqrt t)⁻¹) ^ d := by positivity
  have hZmin : 0 < Real.exp (-(C₀ + 1 + c / 2)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal *
      ((Real.sqrt t)⁻¹) ^ d := by positivity
  have hZ : 0 < tiltNum volume (h.weightLin ℓ t) (fun _ ↦ 1) (h.resid2 ℓ R) t u :=
    lt_of_lt_of_le hZmin hlow
  have hI0 : 0 ≤ gaussLinConst4 (d := d) c :=
    integral_nonneg fun z ↦ mul_nonneg (by positivity) (Real.exp_pos _).le
  have hN0 : 0 ≤ ((Real.sqrt t)⁻¹) ^ d * ((t ^ 2)⁻¹ * gaussLinConst4 (d := d) c) := by positivity
  unfold tiltExp
  calc tiltNum volume (h.weightLin ℓ t) h.quart (h.resid2 ℓ R) t u /
        tiltNum volume (h.weightLin ℓ t) (fun _ ↦ 1) (h.resid2 ℓ R) t u
      ≤ ((Real.sqrt t)⁻¹) ^ d * ((t ^ 2)⁻¹ * gaussLinConst4 (d := d) c) /
        tiltNum volume (h.weightLin ℓ t) (fun _ ↦ 1) (h.resid2 ℓ R) t u :=
        div_le_div_of_nonneg_right hup hZ.le
    _ ≤ ((Real.sqrt t)⁻¹) ^ d * ((t ^ 2)⁻¹ * gaussLinConst4 (d := d) c) /
        (Real.exp (-(C₀ + 1 + c / 2)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal *
          ((Real.sqrt t)⁻¹) ^ d) :=
        div_le_div_of_nonneg_left hN0 hZmin hlow
    _ = cstar4 d c C₀ / t ^ 2 := by
        unfold cstar4
        rw [Real.exp_neg]
        field_simp

/-! ### Variance of the quadratic remainder and the `q = 2` law -/

theorem tiltData2 (ℓ : EuclidD d →L[ℝ] ℝ) {γ : ℝ} (hℓ : ‖ℓ‖ ≤ γ) {R : EuclidD d → ℝ}
    (hRm : Measurable R) {ρ₂ D : ℝ} (hρ₂ : 0 ≤ ρ₂) (hρc : ρ₂ ≤ c / 2)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D)
    {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t) (ht1 : 1 ≤ t) (hγt : γ ^ 2 * t ≤ 1) :
    TiltData volume (h.weightLin ℓ t) (h.resid2 ℓ R) (ρ₂ * D ^ 2) := by
  refine ⟨h.weightLin_measurable ℓ t, h.weightLin_integrable ℓ t, h.weightLin_nonneg ℓ t, ?_,
    h.resid2_measurable ℓ hRm, fun w ↦ h.resid2_bound ℓ hρ₂ hR hD w⟩
  have hlow := h.tiltNum_one_lower2 ℓ hℓ hRm hρ₂ hρc hR ht ht1 hγt
    (Set.left_mem_Icc.mpr zero_le_one)
  have hZmin : 0 < Real.exp (-(C₀ + 1 + c / 2)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal *
      ((Real.sqrt t)⁻¹) ^ d := by
    have : 0 < (volume (Metric.ball (0 : EuclidD d) 1)).toReal :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
    have : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
    positivity
  have h0 : tiltNum volume (h.weightLin ℓ t) (fun _ ↦ 1) (h.resid2 ℓ R) t 0 =
      ∫ w, h.weightLin ℓ t w := by
    unfold tiltNum
    simp
  rw [h0] at hlow
  exact lt_of_lt_of_le hZmin hlow

theorem tiltCov_resid2_le (ℓ : EuclidD d →L[ℝ] ℝ) {γ : ℝ} (hℓ : ‖ℓ‖ ≤ γ) {R : EuclidD d → ℝ}
    (hRm : Measurable R) {ρ₂ D : ℝ} (hρ₂ : 0 ≤ ρ₂) (hρc : ρ₂ ≤ c / 2)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D)
    {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t) (ht1 : 1 ≤ t) (hγt : γ ^ 2 * t ≤ 1) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    tiltCov volume (h.weightLin ℓ t) (h.resid2 ℓ R) (h.resid2 ℓ R) (h.resid2 ℓ R) t u ≤
      ρ₂ ^ 2 * (cstar4 d c C₀ / t ^ 2) := by
  have hT := h.tiltData2 ℓ hℓ hRm hρ₂ hρc hR hD ht ht1 hγt
  have hbR : Bdd (h.resid2 ℓ R) := hT.bdd_R
  have hbq : Bdd h.quart := ⟨h.quart_measurable, D ^ 4, h.quart_bound hD⟩
  have hpt : ∀ w, h.resid2 ℓ R w * h.resid2 ℓ R w ≤ ρ₂ ^ 2 * h.quart w := by
    intro w
    unfold resid2 quart
    by_cases hw : w ∈ tsupport χ
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      have := hR w
      have h2 : (R w - R p - ℓ (w - p)) * (R w - R p - ℓ (w - p)) =
          |R w - R p - ℓ (w - p)| ^ 2 := by
        rw [sq_abs]
        ring
      rw [h2]
      calc |R w - R p - ℓ (w - p)| ^ 2 ≤ (ρ₂ * ‖w - p‖ ^ 2) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = ρ₂ ^ 2 * ‖w - p‖ ^ 4 := by ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      simp
  have hvar : tiltCov volume (h.weightLin ℓ t) (h.resid2 ℓ R) (h.resid2 ℓ R) (h.resid2 ℓ R) t u ≤
      tiltExp volume (h.weightLin ℓ t) (fun w ↦ h.resid2 ℓ R w * h.resid2 ℓ R w)
        (h.resid2 ℓ R) t u := by
    unfold tiltCov
    nlinarith [sq_nonneg (tiltExp volume (h.weightLin ℓ t) (h.resid2 ℓ R) (h.resid2 ℓ R) t u)]
  calc _ ≤ _ := hvar
    _ ≤ tiltExp volume (h.weightLin ℓ t) (fun w ↦ ρ₂ ^ 2 * h.quart w) (h.resid2 ℓ R) t u :=
        hT.tiltExp_mono (hbR.mul hbR) (hbq.const_mul _) hpt t u
    _ = ρ₂ ^ 2 * tiltExp volume (h.weightLin ℓ t) h.quart (h.resid2 ℓ R) t u :=
        tiltExp_const_mul _ _ _ _ _ _
    _ ≤ ρ₂ ^ 2 * (cstar4 d c C₀ / t ^ 2) :=
        mul_le_mul_of_nonneg_left (h.tiltExp_quart_le ℓ hℓ hRm hρ₂ hρc hR ht ht1 hγt hu)
          (by positivity)

/-- The endpoints: `u = 1` is the windowed expectation of `L + R`, `u = 0` that of the
score-tilted population loss `L + ℓ(· − p)`. -/
theorem tiltExp_endpoints2 (ℓ : EuclidD d →L[ℝ] ℝ) {R φ : EuclidD d → ℝ}
    (hφχ : ∀ w, φ w * χ w = φ w) (t : ℝ) :
    tiltExp volume (h.weightLin ℓ t) φ (h.resid2 ℓ R) t 1 = winExp (fun w ↦ L w + R w) φ χ t ∧
      tiltExp volume (h.weightLin ℓ t) φ (h.resid2 ℓ R) t 0 =
        winExp (fun w ↦ L w + ℓ (w - p)) φ χ t := by
  have hφ0 : ∀ w, w ∉ tsupport χ → φ w = 0 := by
    intro w hw
    have := hφχ w
    rw [image_eq_zero_of_notMem_tsupport hw, mul_zero] at this
    exact this.symm
  constructor
  · unfold tiltExp tiltNum winExp weightLin resid2
    have key : ∀ w, w ∈ tsupport χ →
        Real.exp (-(t * (R w - R p - ℓ (w - p)) * 1)) * Real.exp (-(t * (L w - L p + ℓ (w - p)))) =
        Real.exp (t * (L p + R p)) * Real.exp (-(t * (L w + R w))) := by
      intro w _
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hnum : (∫ w, φ w * Real.exp (-(t * (tsupport χ).indicator
        (fun w ↦ R w - R p - ℓ (w - p)) w * 1)) *
        (χ w * Real.exp (-(t * (L w - L p + ℓ (w - p)))))) =
        Real.exp (t * (L p + R p)) * ∫ w, φ w * Real.exp (-(t * (L w + R w))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      by_cases hw : w ∈ tsupport χ
      · rw [Set.indicator_of_mem hw]
        have : φ w * Real.exp (-(t * (R w - R p - ℓ (w - p)) * 1)) *
            (χ w * Real.exp (-(t * (L w - L p + ℓ (w - p))))) =
            (φ w * χ w) * (Real.exp (-(t * (R w - R p - ℓ (w - p)) * 1)) *
              Real.exp (-(t * (L w - L p + ℓ (w - p))))) := by
          ring
        rw [this, hφχ w, key w hw]
        ring
      · rw [hφ0 w hw]
        simp
    have hden : (∫ w, (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * (tsupport χ).indicator
        (fun w ↦ R w - R p - ℓ (w - p)) w * 1)) *
        (χ w * Real.exp (-(t * (L w - L p + ℓ (w - p)))))) =
        Real.exp (t * (L p + R p)) * ∫ w, χ w * Real.exp (-(t * (L w + R w))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      by_cases hw : w ∈ tsupport χ
      · rw [Set.indicator_of_mem hw]
        have : (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * (R w - R p - ℓ (w - p)) * 1)) *
            (χ w * Real.exp (-(t * (L w - L p + ℓ (w - p))))) =
            χ w * (Real.exp (-(t * (R w - R p - ℓ (w - p)) * 1)) *
              Real.exp (-(t * (L w - L p + ℓ (w - p))))) := by
          ring
        rw [this, key w hw]
        ring
      · rw [image_eq_zero_of_notMem_tsupport hw]
        simp
    rw [hnum, hden, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  · unfold tiltExp tiltNum winExp weightLin resid2
    have key : ∀ w, Real.exp (-(t * (L w - L p + ℓ (w - p)))) =
        Real.exp (t * L p) * Real.exp (-(t * (L w + ℓ (w - p)))) := by
      intro w
      rw [← Real.exp_add]
      congr 1
      ring
    have hnum : (∫ w, φ w * Real.exp (-(t * (tsupport χ).indicator
        (fun w ↦ R w - R p - ℓ (w - p)) w * 0)) *
        (χ w * Real.exp (-(t * (L w - L p + ℓ (w - p)))))) =
        Real.exp (t * L p) * ∫ w, φ w * Real.exp (-(t * (L w + ℓ (w - p)))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      have : φ w * Real.exp (-(t * (tsupport χ).indicator (fun w ↦ R w - R p - ℓ (w - p)) w * 0)) *
          (χ w * Real.exp (-(t * (L w - L p + ℓ (w - p))))) =
          (φ w * χ w) * Real.exp (-(t * (L w - L p + ℓ (w - p)))) := by
        simp [mul_assoc]
      rw [this, hφχ w, key w]
      ring
    have hden : (∫ w, (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * (tsupport χ).indicator
        (fun w ↦ R w - R p - ℓ (w - p)) w * 0)) *
        (χ w * Real.exp (-(t * (L w - L p + ℓ (w - p)))))) =
        Real.exp (t * L p) * ∫ w, χ w * Real.exp (-(t * (L w + ℓ (w - p)))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      have : (fun _ ↦ (1 : ℝ)) w *
          Real.exp (-(t * (tsupport χ).indicator (fun w ↦ R w - R p - ℓ (w - p)) w * 0)) *
          (χ w * Real.exp (-(t * (L w - L p + ℓ (w - p))))) =
          χ w * Real.exp (-(t * (L w - L p + ℓ (w - p)))) := by
        simp
      rw [this, key w]
      ring
    rw [hnum, hden, mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- **The `q = 2` law.** Modulo the tilt by the empirical score `ℓ = ∇R(p)`, a residual with
quadratic remainder `|R − R(p) − ℓ(· − p)| ≤ ρ₂‖w − p‖²` perturbs the windowed expectation of a
bounded test by at most `‖φ‖_∞ ρ₂ √C₄`, uniformly in `t ≥ max(r₀^{-2}, 1)` with `‖ℓ‖² t ≤ 1`
and `ρ₂ ≤ c/2`. -/
theorem abs_winExp_sub_le_quadratic (ℓ : EuclidD d →L[ℝ] ℝ) {γ : ℝ} (hℓ : ‖ℓ‖ ≤ γ)
    {R φ : EuclidD d → ℝ} (hRm : Measurable R) {ρ₂ : ℝ} (hρ₂ : 0 ≤ ρ₂) (hρc : ρ₂ ≤ c / 2)
    (hR : ∀ w, |R w - R p - ℓ (w - p)| ≤ ρ₂ * ‖w - p‖ ^ 2) (hφm : Measurable φ) {Mφ : ℝ}
    (hφ : ∀ w, |φ w| ≤ Mφ) (hφχ : ∀ w, φ w * χ w = φ w) {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t)
    (ht1 : 1 ≤ t) (hγt : γ ^ 2 * t ≤ 1) :
    |winExp (fun w ↦ L w + R w) φ χ t - winExp (fun w ↦ L w + ℓ (w - p)) φ χ t| ≤
      Mφ * ρ₂ * Real.sqrt (cstar4 d c C₀) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨D, hD0, hD⟩ := h.exists_diam
  have hT := h.tiltData2 ℓ hℓ hRm hρ₂ hρc hR hD ht ht1 hγt
  have hMφ : 0 ≤ Mφ := le_trans (abs_nonneg _) (hφ p)
  have hbφ : Bdd φ := ⟨hφm, Mφ, hφ⟩
  have hC0 : 0 ≤ cstar4 d c C₀ := by
    unfold cstar4
    have hI0 : 0 ≤ gaussLinConst4 (d := d) c :=
      integral_nonneg fun z ↦ mul_nonneg (by positivity) (Real.exp_pos _).le
    positivity
  have hVφ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      tiltCov volume (h.weightLin ℓ t) φ φ (h.resid2 ℓ R) t u ≤ Mφ ^ 2 := by
    intro u _
    have hpt : ∀ w, φ w * φ w ≤ (fun _ ↦ Mφ ^ 2) w := fun w ↦ by
      have := hφ w
      have h2 : φ w * φ w = |φ w| ^ 2 := by rw [sq_abs]; ring
      rw [h2]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have := hT.tiltExp_mono (hbφ.mul hbφ) (Bdd.const _) hpt t u
    rw [hT.tiltExp_const] at this
    unfold tiltCov
    nlinarith [sq_nonneg (tiltExp volume (h.weightLin ℓ t) φ (h.resid2 ℓ R) t u)]
  have hVR : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      tiltCov volume (h.weightLin ℓ t) (h.resid2 ℓ R) (h.resid2 ℓ R) (h.resid2 ℓ R) t u ≤
        (ρ₂ * Real.sqrt (cstar4 d c C₀ / t ^ 2)) ^ 2 := by
    intro u hu
    have := h.tiltCov_resid2_le ℓ hℓ hRm hρ₂ hρc hR hD ht ht1 hγt hu
    rwa [mul_pow, Real.sq_sqrt (by positivity)]
  have hmain := hT.abs_tiltExp_one_sub_zero_le_of_var hbφ ht0.le hMφ
    (by positivity : 0 ≤ ρ₂ * Real.sqrt (cstar4 d c C₀ / t ^ 2)) hVφ hVR
  obtain ⟨he1, he0⟩ := h.tiltExp_endpoints2 ℓ (R := R) hφχ t
  rw [he1, he0] at hmain
  refine hmain.trans (le_of_eq ?_)
  rw [Real.sqrt_div hC0, Real.sqrt_sq ht0.le]
  field_simp

end NondegWindow

end Laplace.Multi
