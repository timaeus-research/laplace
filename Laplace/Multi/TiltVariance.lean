/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TiltCauchySchwarz
import Laplace.Multi.RateCalculus
import Laplace.Multi.StdGaussian

/-!
# Variance of a Lipschitz residual under the tilted Gibbs laws: the `q = 1` law

Around a nondegenerate minimum `p` of the population loss (`c‖w−p‖² ≤ L − L(p)` on the window,
`L − L(p) ≤ C₀‖w−p‖²` near `p`), a residual `R` that is `ρ`-Lipschitz from `p`
(`|R(w) − R(p)| ≤ ρ‖w − p‖`) has tilted variance
`Var_{P_u}(R) ≤ ρ² E_{P_u}‖w − p‖² ≤ ρ² C_* / t` uniformly in `u ∈ [0,1]`, for `t ≥ r₀^{-2}` and
`ρ² t ≤ 1` (`tiltExp_sq_le`, `tiltCov_res_le`): the tilted laws stay localized at scale
`t^{-1/2}` because the tilt costs at most a factor `e^{±1}` there. With the interpolation
identity this gives (`abs_winExp_sub_le_of_lipschitz`)

  `|⟨f⟩_{L+R,t} − ⟨f⟩_{L,t}| ≤ ‖f‖_∞ · ρ · √C_* · √t`,

the `q = 1` law of `TiltCauchySchwarz`: for an empirical residual with Lipschitz constant
`ρ_n ≍ n^{-1/2}` near the minimizer the error is `O(n^{-1/2} t^{1/2})`, versus the sup-norm
bound `O(t δ_n)`. The Lipschitz constant is the external statistical input.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {d : ℕ}

/-- The windowed normalized expectation `∫ φ e^{-tK} / ∫ χ e^{-tK}` on `EuclidD d`. -/
noncomputable def winExp (K φ χ : EuclidD d → ℝ) (t : ℝ) : ℝ :=
  (∫ w, φ w * Real.exp (-(t * K w))) / ∫ w, χ w * Real.exp (-(t * K w))

/-- A nondegenerate minimum `p` of `L` seen through a window `χ`. -/
structure NondegWindow (p : EuclidD d) (χ L : EuclidD d → ℝ) (r₀ c C₀ : ℝ) : Prop where
  χ_cont : Continuous χ
  χ_supp : HasCompactSupport χ
  χ_nonneg : ∀ w, 0 ≤ χ w
  χ_le_one : ∀ w, χ w ≤ 1
  r₀_pos : 0 < r₀
  χ_ball : ∀ w ∈ Metric.ball p r₀, χ w = 1
  L_cont : Continuous L
  c_pos : 0 < c
  C₀_nonneg : 0 ≤ C₀
  coer : ∀ w ∈ tsupport χ, c * ‖w - p‖ ^ 2 ≤ L w - L p
  upper : ∀ w ∈ Metric.ball p r₀, L w - L p ≤ C₀ * ‖w - p‖ ^ 2

namespace NondegWindow

variable {p : EuclidD d} {χ L : EuclidD d → ℝ} {r₀ c C₀ : ℝ} (h : NondegWindow p χ L r₀ c C₀)

/-- The population weight `χ e^{-t(L − L(p))}`. -/
noncomputable def weight (_h : NondegWindow p χ L r₀ c C₀) (t : ℝ) (w : EuclidD d) : ℝ :=
  χ w * Real.exp (-(t * (L w - L p)))

/-- The truncated centered residual `1_{supp χ} (R − R(p))`. -/
noncomputable def resid (_h : NondegWindow p χ L r₀ c C₀) (R : EuclidD d → ℝ) (w : EuclidD d) :
    ℝ := (tsupport χ).indicator (fun w ↦ R w - R p) w

/-- The truncated squared distance `1_{supp χ} ‖w − p‖²`. -/
noncomputable def sqdist (_h : NondegWindow p χ L r₀ c C₀) (w : EuclidD d) : ℝ :=
  (tsupport χ).indicator (fun w ↦ ‖w - p‖ ^ 2) w

include h

theorem p_mem_tsupport : p ∈ tsupport χ :=
  subset_tsupport χ (by
    rw [Function.mem_support, h.χ_ball p (Metric.mem_ball_self h.r₀_pos)]
    exact one_ne_zero)

theorem ball_subset_tsupport : Metric.ball p r₀ ⊆ tsupport χ := fun w hw ↦
  subset_tsupport χ (by
    rw [Function.mem_support, h.χ_ball w hw]
    exact one_ne_zero)

/-- The window's support is bounded: `‖w − p‖ ≤ D` on it. -/
theorem exists_diam : ∃ D : ℝ, 0 ≤ D ∧ ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D := by
  obtain ⟨D, hD⟩ := (h.χ_supp.isCompact).exists_bound_of_continuousOn
    (f := fun w ↦ w - p) (continuous_id.sub continuous_const).continuousOn
  exact ⟨max D 0, le_max_right _ _, fun w hw ↦ (hD w hw).trans (le_max_left _ _)⟩

theorem weight_nonneg (t : ℝ) (w : EuclidD d) : 0 ≤ h.weight t w :=
  mul_nonneg (h.χ_nonneg w) (Real.exp_pos _).le

theorem weight_measurable (t : ℝ) : Measurable (h.weight t) := by
  unfold weight
  exact h.χ_cont.measurable.mul
    (Real.measurable_exp.comp (((h.L_cont.measurable.sub measurable_const).const_mul t).neg))

theorem weight_integrable (t : ℝ) : Integrable (h.weight t) := by
  unfold weight
  have hc : Continuous fun w ↦ χ w * Real.exp (-(t * (L w - L p))) :=
    h.χ_cont.mul (Real.continuous_exp.comp (((h.L_cont.sub continuous_const).const_mul t).neg))
  exact hc.integrable_of_hasCompactSupport h.χ_supp.mul_right

theorem weight_eq_zero_of_notMem (t : ℝ) {w : EuclidD d} (hw : w ∉ tsupport χ) :
    h.weight t w = 0 := by
  unfold weight
  rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]

theorem resid_measurable {R : EuclidD d → ℝ} (hRm : Measurable R) :
    Measurable (h.resid R) :=
  (hRm.sub measurable_const).indicator (isClosed_tsupport χ).measurableSet

theorem abs_resid_le {R : EuclidD d → ℝ} {ρ : ℝ} (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖)
    (hρ : 0 ≤ ρ) (w : EuclidD d) : |h.resid R w| ≤ ρ * ‖w - p‖ := by
  unfold resid
  by_cases hw : w ∈ tsupport χ
  · rw [Set.indicator_of_mem hw]
    exact hR w
  · rw [Set.indicator_of_notMem hw, abs_zero]
    positivity

/-- The residual is bounded by `ρ D`. -/
theorem resid_bound {R : EuclidD d → ℝ} {ρ D : ℝ} (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖)
    (hρ : 0 ≤ ρ) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D) (w : EuclidD d) :
    |h.resid R w| ≤ ρ * D := by
  unfold resid
  by_cases hw : w ∈ tsupport χ
  · rw [Set.indicator_of_mem hw]
    exact (hR w).trans (mul_le_mul_of_nonneg_left (hD w hw) hρ)
  · rw [Set.indicator_of_notMem hw, abs_zero]
    have := hD p h.p_mem_tsupport
    have : 0 ≤ D := le_trans (norm_nonneg _) this
    positivity

/-! ### The Gaussian-type integral with a linear term -/

omit h in
/-- `‖y‖² e^{-a‖y‖² + b‖y‖}` is integrable (`b‖y‖ ≤ a‖y‖²/2 + b²/(2a)`). -/
theorem integrable_sq_mul_exp_lin {a b : ℝ} (ha : 0 < a) :
    Integrable fun y : EuclidD d ↦ ‖y‖ ^ 2 * Real.exp (-(a * ‖y‖ ^ 2) + b * ‖y‖) := by
  have hdom := (integrable_pow_mul_exp_neg_mul_sq (d := d) (half_pos ha) 2).const_mul
    (Real.exp (b ^ 2 / (2 * a)))
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y ↦ ?_)
  · exact ((continuous_norm.pow 2).mul (Real.continuous_exp.comp
      (((continuous_norm.pow 2).const_mul a).neg.add (continuous_norm.const_mul b))))
      |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hkey : -(a * ‖y‖ ^ 2) + b * ‖y‖ ≤ b ^ 2 / (2 * a) + -(a / 2) * ‖y‖ ^ 2 := by
      have h2a : 0 < 2 * a := by positivity
      rw [← sub_nonneg]
      have : b ^ 2 / (2 * a) + -(a / 2) * ‖y‖ ^ 2 - (-(a * ‖y‖ ^ 2) + b * ‖y‖) =
          (b - a * ‖y‖) ^ 2 / (2 * a) := by
        field_simp
        ring
      rw [this]
      positivity
    calc ‖y‖ ^ 2 * Real.exp (-(a * ‖y‖ ^ 2) + b * ‖y‖)
        ≤ ‖y‖ ^ 2 * Real.exp (b ^ 2 / (2 * a) + -(a / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) (by positivity)
      _ = Real.exp (b ^ 2 / (2 * a)) * (‖y‖ ^ 2 * Real.exp (-(a / 2) * ‖y‖ ^ 2)) := by
          rw [Real.exp_add]
          ring

omit h in
/-- The constant `I₂ = ∫ ‖z‖² e^{-c‖z‖² + ‖z‖}`. -/
noncomputable def gaussLinConst (c : ℝ) : ℝ :=
  ∫ z : EuclidD d, ‖z‖ ^ 2 * Real.exp (-(c * ‖z‖ ^ 2) + 1 * ‖z‖)

/-! ### Integrability and boundedness of the tilted integrands -/

theorem sqdist_bound {D : ℝ} (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D) (w : EuclidD d) :
    |h.sqdist w| ≤ D ^ 2 := by
  unfold sqdist
  by_cases hw : w ∈ tsupport χ
  · rw [Set.indicator_of_mem hw, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hD w hw) 2
  · rw [Set.indicator_of_notMem hw, abs_zero]
    have := le_trans (norm_nonneg _) (hD p h.p_mem_tsupport)
    positivity

theorem sqdist_measurable : Measurable h.sqdist :=
  ((continuous_id.sub continuous_const).norm.pow 2).measurable.indicator
    (isClosed_tsupport χ).measurableSet

/-- The tilt factor is bounded by `e^{t ρ D}` for `u ∈ [0,1]`. -/
theorem exp_tilt_le {R : EuclidD d → ℝ} {ρ D : ℝ} (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖)
    (hρ : 0 ≤ ρ) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D) {t : ℝ} (ht0 : 0 ≤ t) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (w : EuclidD d) :
    Real.exp (-(t * h.resid R w * u)) ≤ Real.exp (t * (ρ * D)) := by
  have hb := abs_le.mp (h.resid_bound hR hρ hD w)
  have hD0 : 0 ≤ ρ * D := le_trans (abs_nonneg _) (h.resid_bound hR hρ hD p)
  rw [Real.exp_le_exp]
  obtain ⟨hu0, hu1⟩ := hu
  have hpos : 0 ≤ h.resid R w + ρ * D := by linarith [hb.1]
  nlinarith [mul_nonneg ht0 hu0, mul_nonneg (mul_nonneg ht0 hu0) hpos, mul_nonneg ht0 hD0]

theorem integrable_tilt_of_bound {R : EuclidD d → ℝ} (hRm : Measurable R) {ρ D : ℝ}
    (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖) (hρ : 0 ≤ ρ) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D)
    {t : ℝ} (ht0 : 0 ≤ t) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) {g : EuclidD d → ℝ}
    (hgm : Measurable g) {Mg : ℝ} (hg : ∀ w, |g w| ≤ Mg) :
    Integrable fun w ↦ g w * Real.exp (-(t * h.resid R w * u)) * h.weight t w := by
  refine (h.weight_integrable t).bdd_mul (c := Mg * Real.exp (t * (ρ * D))) ?_
    (Filter.Eventually.of_forall fun w ↦ ?_)
  · exact (hgm.mul (Real.measurable_exp.comp
      ((((h.resid_measurable hRm).const_mul t).mul_const u).neg)))
      |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_mul (hg w) (h.exp_tilt_le hR hρ hD ht0 hu w) (Real.exp_pos _).le
      (le_trans (abs_nonneg _) (hg w))

/-! ### The tilted normalizer from below -/

/-- On the ball of radius `s = t^{-1/2}` the tilted weight is at least `e^{-(C₀+1)}`, so the
tilted normalizer is at least `e^{-(C₀+1)} · vol B(0,1) · s^d`. -/
theorem tiltNum_one_lower {R : EuclidD d → ℝ} (hRm : Measurable R) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖) {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t) (ht1 : 1 ≤ t)
    (hρt : ρ ^ 2 * t ≤ 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-(C₀ + 1)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal *
        ((Real.sqrt t)⁻¹) ^ d ≤
      tiltNum volume (h.weight t) (fun _ ↦ 1) (h.resid R) t u := by
  have ht0 : 0 < t := by linarith
  set s : ℝ := (Real.sqrt t)⁻¹ with hs_def
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs : 0 < s := inv_pos.mpr hst
  have hs2 : s ^ 2 = t⁻¹ := by
    rw [hs_def, inv_pow, Real.sq_sqrt ht0.le]
  have hts : t * s = Real.sqrt t := by
    rw [hs_def, ← div_eq_mul_inv, Real.div_sqrt]
  have hρs : ρ * Real.sqrt t ≤ 1 := by
    have : (ρ * Real.sqrt t) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt ht0.le]
      exact hρt
    nlinarith [mul_nonneg hρ hst.le, this]
  have hsr : s ≤ r₀ := by
    have hr₀ := h.r₀_pos
    have h1 : r₀ ^ (-2 : ℝ) = (r₀ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hr₀.le]
      norm_cast
    rw [h1] at ht
    have h2 : (r₀ ^ 2)⁻¹ * r₀ ^ 2 ≤ t * r₀ ^ 2 := mul_le_mul_of_nonneg_right ht (by positivity)
    rw [inv_mul_cancel₀ (by positivity)] at h2
    have h3 : Real.sqrt 1 ≤ Real.sqrt (t * r₀ ^ 2) := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_one, Real.sqrt_mul ht0.le, Real.sqrt_sq hr₀.le] at h3
    rw [hs_def, inv_le_iff_one_le_mul₀ hst]
    linarith
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨D, hD0, hD⟩ := h.exists_diam
  have hden_pt : ∀ w, (Metric.ball p s).indicator (fun _ ↦ Real.exp (-(C₀ + 1))) w ≤
      (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * h.resid R w * u)) *
        h.weight t w := by
    intro w
    by_cases hw : w ∈ Metric.ball p s
    · rw [Set.indicator_of_mem hw]
      have hwr : w ∈ Metric.ball p r₀ := Metric.ball_subset_ball hsr hw
      have hwt : w ∈ tsupport χ := h.ball_subset_tsupport hwr
      have hnorm : ‖w - p‖ < s := by
        rw [Metric.mem_ball, dist_eq_norm] at hw
        exact hw
      unfold resid weight
      rw [Set.indicator_of_mem hwt, h.χ_ball w hwr, one_mul, one_mul, ← Real.exp_add,
        Real.exp_le_exp]
      have hup := h.upper w hwr
      have hres := abs_le.mp (hR w)
      have hn := norm_nonneg (w - p)
      have hA : t * (L w - L p) ≤ C₀ := by
        have hsq : t * ‖w - p‖ ^ 2 ≤ 1 := by
          have : ‖w - p‖ ^ 2 ≤ s ^ 2 := by nlinarith
          rw [hs2] at this
          calc t * ‖w - p‖ ^ 2 ≤ t * t⁻¹ := mul_le_mul_of_nonneg_left this ht0.le
            _ = 1 := mul_inv_cancel₀ ht0.ne'
        calc t * (L w - L p) ≤ t * (C₀ * ‖w - p‖ ^ 2) := mul_le_mul_of_nonneg_left hup ht0.le
          _ = C₀ * (t * ‖w - p‖ ^ 2) := by ring
          _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left hsq h.C₀_nonneg
          _ = C₀ := mul_one _
      have hB : t * (R w - R p) * u ≤ 1 := by
        have h1 : t * (R w - R p) * u ≤ t * (ρ * ‖w - p‖) * u := by
          have := mul_le_mul_of_nonneg_left hres.2 ht0.le
          exact mul_le_mul_of_nonneg_right this hu0
        have h2 : t * (ρ * ‖w - p‖) * u ≤ t * (ρ * s) * 1 := by
          have : ρ * ‖w - p‖ ≤ ρ * s := mul_le_mul_of_nonneg_left hnorm.le hρ
          have := mul_le_mul_of_nonneg_left this ht0.le
          exact mul_le_mul this hu1 hu0 (by positivity)
        have h3 : t * (ρ * s) * 1 = ρ * Real.sqrt t := by
          rw [← hts]
          ring
        linarith
      linarith
    · rw [Set.indicator_of_notMem hw]
      exact mul_nonneg (mul_nonneg zero_le_one (Real.exp_pos _).le) (h.weight_nonneg t w)
  have hind : Integrable
      ((Metric.ball p s).indicator fun _ : EuclidD d ↦ Real.exp (-(C₀ + 1))) :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      (integrableOn_const measure_ball_lt_top.ne)
  have hint := h.integrable_tilt_of_bound hRm hR hρ hD ht0.le ⟨hu0, hu1⟩ measurable_const
    (Mg := 1) (fun _ ↦ abs_one.le)
  have hmono := integral_mono hind hint hden_pt
  rw [integral_indicator_const _ Metric.isOpen_ball.measurableSet, smul_eq_mul, measureReal_def,
    Measure.addHaar_ball_of_pos volume p hs, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hmono
  have hfold : tiltNum volume (h.weight t) (fun _ ↦ 1) (h.resid R) t u =
      ∫ w, (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * h.resid R w * u)) * h.weight t w := rfl
  rw [hfold]
  calc Real.exp (-(C₀ + 1)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal * s ^ d
      = s ^ d * (volume (Metric.ball (0 : EuclidD d) 1)).toReal * Real.exp (-(C₀ + 1)) := by
        ring
    _ ≤ _ := hmono

/-! ### The tilted second moment from above -/

/-- The tilted second moment numerator is at most `s^d · t⁻¹ · I₂`. -/
theorem tiltNum_sqdist_upper {R : EuclidD d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖) {t : ℝ} (ht1 : 1 ≤ t) (hρt : ρ ^ 2 * t ≤ 1)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hRm : Measurable R) :
    tiltNum volume (h.weight t) (h.sqdist) (h.resid R) t u ≤
      ((Real.sqrt t)⁻¹) ^ d * (t⁻¹ * gaussLinConst (d := d) c) := by
  have ht0 : 0 < t := by linarith
  set s : ℝ := (Real.sqrt t)⁻¹ with hs_def
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs : 0 < s := inv_pos.mpr hst
  have hs2 : s ^ 2 = t⁻¹ := by
    rw [hs_def, inv_pow, Real.sq_sqrt ht0.le]
  have hts : t * s = Real.sqrt t := by
    rw [hs_def, ← div_eq_mul_inv, Real.div_sqrt]
  have hρs : ρ * Real.sqrt t ≤ 1 := by
    have : (ρ * Real.sqrt t) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt ht0.le]
      exact hρt
    nlinarith [mul_nonneg hρ hst.le, this]
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨D, hD0, hD⟩ := h.exists_diam
  -- pointwise domination
  have hnum_pt : ∀ w, h.sqdist w *
      Real.exp (-(t * h.resid R w * u)) * h.weight t w ≤
      ‖w - p‖ ^ 2 * Real.exp (-(t * c * ‖w - p‖ ^ 2) + t * ρ * ‖w - p‖) := by
    intro w
    by_cases hw : w ∈ tsupport χ
    · unfold sqdist resid weight
      rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      have hcoer := h.coer w hw
      have hres := abs_le.mp (hR w)
      have hχ := h.χ_le_one w
      have hχ0 := h.χ_nonneg w
      have hn := norm_nonneg (w - p)
      have he : Real.exp (-(t * (R w - R p) * u)) * Real.exp (-(t * (L w - L p))) ≤
          Real.exp (-(t * c * ‖w - p‖ ^ 2) + t * ρ * ‖w - p‖) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        have h1 : t * (L w - L p) ≥ t * c * ‖w - p‖ ^ 2 := by
          have := mul_le_mul_of_nonneg_left hcoer ht0.le
          linarith
        have h2 : -(t * (R w - R p) * u) ≤ t * ρ * ‖w - p‖ := by
          have ha : -(R w - R p) ≤ ρ * ‖w - p‖ := by linarith [hres.1]
          have hb : t * u * (-(R w - R p)) ≤ t * u * (ρ * ‖w - p‖) :=
            mul_le_mul_of_nonneg_left ha (mul_nonneg ht0.le hu0)
          have hc' : t * u * (ρ * ‖w - p‖) ≤ t * 1 * (ρ * ‖w - p‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu1 ht0.le) (by positivity)
          nlinarith
        linarith
      calc ‖w - p‖ ^ 2 * Real.exp (-(t * (R w - R p) * u)) *
            (χ w * Real.exp (-(t * (L w - L p))))
          ≤ ‖w - p‖ ^ 2 * Real.exp (-(t * (R w - R p) * u)) *
            (1 * Real.exp (-(t * (L w - L p)))) := by
            gcongr
        _ = ‖w - p‖ ^ 2 * (Real.exp (-(t * (R w - R p) * u)) *
            Real.exp (-(t * (L w - L p)))) := by
            ring
        _ ≤ ‖w - p‖ ^ 2 * Real.exp (-(t * c * ‖w - p‖ ^ 2) + t * ρ * ‖w - p‖) :=
            mul_le_mul_of_nonneg_left he (by positivity)
    · rw [h.weight_eq_zero_of_notMem t hw, mul_zero]
      positivity
  have hmaj_int : Integrable fun w : EuclidD d ↦
      ‖w - p‖ ^ 2 * Real.exp (-(t * c * ‖w - p‖ ^ 2) + t * ρ * ‖w - p‖) :=
    (integrable_sq_mul_exp_lin (d := d) (b := t * ρ) (mul_pos ht0 h.c_pos)).comp_sub_right p
  have hint := h.integrable_tilt_of_bound hRm hR hρ hD ht0.le ⟨hu0, hu1⟩
    h.sqdist_measurable (h.sqdist_bound hD)
  have hmono := integral_mono hint hmaj_int hnum_pt
  -- evaluate the majorant by translation and scaling
  have hmaj_val : (∫ w : EuclidD d, ‖w - p‖ ^ 2 *
      Real.exp (-(t * c * ‖w - p‖ ^ 2) + t * ρ * ‖w - p‖)) ≤
      s ^ d * (t⁻¹ * gaussLinConst (d := d) c) := by
    rw [integral_sub_right_eq_self (fun y : EuclidD d ↦ ‖y‖ ^ 2 *
      Real.exp (-(t * c * ‖y‖ ^ 2) + t * ρ * ‖y‖)) p]
    have hscale := Measure.integral_comp_smul (volume : Measure (EuclidD d))
      (fun y : EuclidD d ↦ ‖y‖ ^ 2 * Real.exp (-(t * c * ‖y‖ ^ 2) + t * ρ * ‖y‖)) s
    rw [finrank_euclideanSpace_fin, smul_eq_mul, abs_of_pos (by positivity)] at hscale
    have hF : (∫ y : EuclidD d, ‖y‖ ^ 2 * Real.exp (-(t * c * ‖y‖ ^ 2) + t * ρ * ‖y‖)) =
        s ^ d * ∫ z : EuclidD d, ‖s • z‖ ^ 2 *
          Real.exp (-(t * c * ‖s • z‖ ^ 2) + t * ρ * ‖s • z‖) := by
      rw [hscale, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    rw [hF]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold gaussLinConst
    rw [← integral_const_mul]
    have hintz : Integrable fun z : EuclidD d ↦ ‖s • z‖ ^ 2 *
        Real.exp (-(t * c * ‖s • z‖ ^ 2) + t * ρ * ‖s • z‖) :=
      (integrable_sq_mul_exp_lin (d := d) (b := t * ρ) (mul_pos ht0 h.c_pos)).comp_smul hs.ne'
    refine integral_mono hintz
      ((integrable_sq_mul_exp_lin (d := d) (b := 1) h.c_pos).const_mul _) fun z ↦ ?_
    beta_reduce
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, hs2]
    have hz := norm_nonneg z
    have hexp : Real.exp (-(t * c * (t⁻¹ * ‖z‖ ^ 2)) + t * ρ * (s * ‖z‖)) ≤
        Real.exp (-(c * ‖z‖ ^ 2) + 1 * ‖z‖) := by
      rw [Real.exp_le_exp]
      have h1 : t * c * (t⁻¹ * ‖z‖ ^ 2) = c * ‖z‖ ^ 2 := by
        field_simp
      have h2 : t * ρ * (s * ‖z‖) = (ρ * Real.sqrt t) * ‖z‖ := by
        rw [← hts]
        ring
      rw [h1, h2]
      have : (ρ * Real.sqrt t) * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hρs hz
      linarith
    calc t⁻¹ * ‖z‖ ^ 2 * Real.exp (-(t * c * (t⁻¹ * ‖z‖ ^ 2)) + t * ρ * (s * ‖z‖))
        ≤ t⁻¹ * ‖z‖ ^ 2 * Real.exp (-(c * ‖z‖ ^ 2) + 1 * ‖z‖) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = t⁻¹ * (‖z‖ ^ 2 * Real.exp (-(c * ‖z‖ ^ 2) + 1 * ‖z‖)) := by ring
  exact hmono.trans hmaj_val

/-- The constant `C_* = I₂ e^{C₀+1} / vol B(0,1)`. -/
noncomputable def cstar (d : ℕ) (c C₀ : ℝ) : ℝ :=
  gaussLinConst (d := d) c * Real.exp (C₀ + 1) / (volume (Metric.ball (0 : EuclidD d) 1)).toReal

/-- **The tilted second moment is `O(1/t)` uniformly in the interpolation parameter.** -/
theorem tiltExp_sq_le {R : EuclidD d → ℝ} (hRm : Measurable R) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖) {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t) (ht1 : 1 ≤ t)
    (hρt : ρ ^ 2 * t ≤ 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    tiltExp volume (h.weight t) (h.sqdist) (h.resid R) t u ≤
      cstar d c C₀ / t := by
  have ht0 : 0 < t := by linarith
  have hlow := h.tiltNum_one_lower hRm hρ hR ht ht1 hρt hu
  have hup := h.tiltNum_sqdist_upper hρ hR ht1 hρt hu hRm
  have hv : 0 < (volume (Metric.ball (0 : EuclidD d) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
  have hs : 0 < ((Real.sqrt t)⁻¹) ^ d := by positivity
  have hZmin : 0 < Real.exp (-(C₀ + 1)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal *
      ((Real.sqrt t)⁻¹) ^ d := by positivity
  have hZ : 0 < tiltNum volume (h.weight t) (fun _ ↦ 1) (h.resid R) t u :=
    lt_of_lt_of_le hZmin hlow
  have hI0 : 0 ≤ gaussLinConst (d := d) c :=
    integral_nonneg fun z ↦ mul_nonneg (by positivity) (Real.exp_pos _).le
  have hN0 : 0 ≤ ((Real.sqrt t)⁻¹) ^ d * (t⁻¹ * gaussLinConst (d := d) c) := by positivity
  unfold tiltExp
  calc tiltNum volume (h.weight t) (h.sqdist) (h.resid R) t u /
        tiltNum volume (h.weight t) (fun _ ↦ 1) (h.resid R) t u
      ≤ ((Real.sqrt t)⁻¹) ^ d * (t⁻¹ * gaussLinConst (d := d) c) /
        tiltNum volume (h.weight t) (fun _ ↦ 1) (h.resid R) t u :=
        div_le_div_of_nonneg_right hup hZ.le
    _ ≤ ((Real.sqrt t)⁻¹) ^ d * (t⁻¹ * gaussLinConst (d := d) c) /
        (Real.exp (-(C₀ + 1)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal *
          ((Real.sqrt t)⁻¹) ^ d) :=
        div_le_div_of_nonneg_left hN0 hZmin hlow
    _ = cstar d c C₀ / t := by
        unfold cstar
        rw [Real.exp_neg]
        field_simp

/-! ### Variance of the residual and the `q = 1` law -/

/-- The standing `TiltData` for the window weight and the truncated residual. -/
theorem tiltData {R : EuclidD d → ℝ} (hRm : Measurable R) {ρ D : ℝ} (hρ : 0 ≤ ρ)
    (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D) {t : ℝ}
    (ht : r₀ ^ (-2 : ℝ) ≤ t) (ht1 : 1 ≤ t) (hρt : ρ ^ 2 * t ≤ 1) :
    TiltData volume (h.weight t) (h.resid R) (ρ * D) := by
  refine ⟨h.weight_measurable t, h.weight_integrable t, h.weight_nonneg t, ?_,
    h.resid_measurable hRm, fun w ↦ h.resid_bound hR hρ hD w⟩
  have hlow := h.tiltNum_one_lower hRm hρ hR ht ht1 hρt (Set.left_mem_Icc.mpr zero_le_one)
  have hZmin : 0 < Real.exp (-(C₀ + 1)) * (volume (Metric.ball (0 : EuclidD d) 1)).toReal *
      ((Real.sqrt t)⁻¹) ^ d := by
    have : 0 < (volume (Metric.ball (0 : EuclidD d) 1)).toReal :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
    have : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
    positivity
  have h0 : tiltNum volume (h.weight t) (fun _ ↦ 1) (h.resid R) t 0 =
      ∫ w, h.weight t w := by
    unfold tiltNum
    simp
  rw [h0] at hlow
  exact lt_of_lt_of_le hZmin hlow

omit h in
/-- Monotonicity of the tilted expectation on bounded functions. -/
theorem _root_.Laplace.Multi.TiltData.tiltExp_mono {X : Type*} [MeasurableSpace X] [Nonempty X]
    {μ : Measure X} {ν R : X → ℝ} {M : ℝ} (hT : TiltData μ ν R M) {f g : X → ℝ} (hf : Bdd f)
    (hg : Bdd g) (hfg : ∀ x, f x ≤ g x) (t u : ℝ) :
    tiltExp μ ν f R t u ≤ tiltExp μ ν g R t u := by
  unfold tiltExp
  refine div_le_div_of_nonneg_right ?_ (hT.tiltNum_one_pos t u).le
  unfold tiltNum
  refine integral_mono (hT.integrable_of_bdd hf t u) (hT.integrable_of_bdd hg t u) fun x ↦ ?_
  beta_reduce
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hfg x) (Real.exp_pos _).le)
    (hT.ν_nonneg x)

/-- **Variance of the residual under the tilted laws**: `Var_u(R) ≤ ρ² C_* / t`. -/
theorem tiltCov_res_le {R : EuclidD d → ℝ} (hRm : Measurable R) {ρ D : ℝ} (hρ : 0 ≤ ρ)
    (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖) (hD : ∀ w ∈ tsupport χ, ‖w - p‖ ≤ D) {t : ℝ}
    (ht : r₀ ^ (-2 : ℝ) ≤ t) (ht1 : 1 ≤ t) (hρt : ρ ^ 2 * t ≤ 1) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    tiltCov volume (h.weight t) (h.resid R) (h.resid R)
        (h.resid R) t u ≤ ρ ^ 2 * (cstar d c C₀ / t) := by
  have hT := h.tiltData hRm hρ hR hD ht ht1 hρt
  have hbR : Bdd (h.resid R) := hT.bdd_R
  have hbsq : Bdd (h.sqdist) :=
    ⟨h.sqdist_measurable, D ^ 2, h.sqdist_bound hD⟩
  have hpt : ∀ w, h.resid R w * h.resid R w ≤
      ρ ^ 2 * h.sqdist w := by
    intro w
    unfold resid sqdist
    by_cases hw : w ∈ tsupport χ
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      have := hR w
      have h2 : (R w - R p) * (R w - R p) = |R w - R p| ^ 2 := by
        rw [sq_abs]
        ring
      rw [h2]
      calc |R w - R p| ^ 2 ≤ (ρ * ‖w - p‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = ρ ^ 2 * ‖w - p‖ ^ 2 := by ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      simp
  have hvar : tiltCov volume (h.weight t) (h.resid R)
      (h.resid R) (h.resid R) t u ≤
      tiltExp volume (h.weight t) (fun w ↦ h.resid R w *
        h.resid R w) (h.resid R) t u := by
    unfold tiltCov
    nlinarith [sq_nonneg (tiltExp volume (h.weight t) (h.resid R)
      (h.resid R) t u)]
  calc _ ≤ _ := hvar
    _ ≤ tiltExp volume (h.weight t) (fun w ↦ ρ ^ 2 * h.sqdist w)
        (h.resid R) t u :=
        hT.tiltExp_mono (hbR.mul hbR) (hbsq.const_mul _) hpt t u
    _ = ρ ^ 2 * tiltExp volume (h.weight t) (h.sqdist)
        (h.resid R) t u := tiltExp_const_mul _ _ _ _ _ _
    _ ≤ ρ ^ 2 * (cstar d c C₀ / t) :=
        mul_le_mul_of_nonneg_left (h.tiltExp_sq_le hRm hρ hR ht ht1 hρt hu) (by positivity)

/-- The endpoints of the interpolation are the windowed expectations of `L + R` and of `L`. -/
theorem tiltExp_endpoints {R φ : EuclidD d → ℝ} (hφχ : ∀ w, φ w * χ w = φ w) (t : ℝ) :
    tiltExp volume (h.weight t) φ (h.resid R) t 1 =
        winExp (fun w ↦ L w + R w) φ χ t ∧
      tiltExp volume (h.weight t) φ (h.resid R) t 0 = winExp L φ χ t := by
  have hφ0 : ∀ w, w ∉ tsupport χ → φ w = 0 := by
    intro w hw
    have := hφχ w
    rw [image_eq_zero_of_notMem_tsupport hw, mul_zero] at this
    exact this.symm
  constructor
  · unfold tiltExp tiltNum winExp weight resid
    have hnum : (∫ w, φ w * Real.exp (-(t * (tsupport χ).indicator (fun w ↦ R w - R p) w * 1)) *
        (χ w * Real.exp (-(t * (L w - L p))))) =
        Real.exp (t * (L p + R p)) * ∫ w, φ w * Real.exp (-(t * (L w + R w))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      by_cases hw : w ∈ tsupport χ
      · rw [Set.indicator_of_mem hw]
        have key : Real.exp (-(t * (R w - R p) * 1)) * Real.exp (-(t * (L w - L p))) =
            Real.exp (t * (L p + R p)) * Real.exp (-(t * (L w + R w))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        have : φ w * Real.exp (-(t * (R w - R p) * 1)) * (χ w * Real.exp (-(t * (L w - L p)))) =
            (φ w * χ w) * (Real.exp (-(t * (R w - R p) * 1)) * Real.exp (-(t * (L w - L p)))) := by
          ring
        rw [this, hφχ w, key]
        ring
      · rw [hφ0 w hw]
        simp
    have hden : (∫ w, (fun _ ↦ (1 : ℝ)) w *
        Real.exp (-(t * (tsupport χ).indicator (fun w ↦ R w - R p) w * 1)) *
        (χ w * Real.exp (-(t * (L w - L p))))) =
        Real.exp (t * (L p + R p)) * ∫ w, χ w * Real.exp (-(t * (L w + R w))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      by_cases hw : w ∈ tsupport χ
      · rw [Set.indicator_of_mem hw]
        have key : Real.exp (-(t * (R w - R p) * 1)) * Real.exp (-(t * (L w - L p))) =
            Real.exp (t * (L p + R p)) * Real.exp (-(t * (L w + R w))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        have : (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * (R w - R p) * 1)) *
            (χ w * Real.exp (-(t * (L w - L p)))) =
            χ w * (Real.exp (-(t * (R w - R p) * 1)) * Real.exp (-(t * (L w - L p)))) := by
          ring
        rw [this, key]
        ring
      · rw [image_eq_zero_of_notMem_tsupport hw]
        simp
    rw [hnum, hden, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  · unfold tiltExp tiltNum winExp weight resid
    have hnum : (∫ w, φ w * Real.exp (-(t * (tsupport χ).indicator (fun w ↦ R w - R p) w * 0)) *
        (χ w * Real.exp (-(t * (L w - L p))))) =
        Real.exp (t * L p) * ∫ w, φ w * Real.exp (-(t * L w)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      have key : Real.exp (-(t * (L w - L p))) = Real.exp (t * L p) * Real.exp (-(t * L w)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have : φ w * Real.exp (-(t * (tsupport χ).indicator (fun w ↦ R w - R p) w * 0)) *
          (χ w * Real.exp (-(t * (L w - L p)))) = (φ w * χ w) * Real.exp (-(t * (L w - L p))) := by
        simp [mul_assoc]
      rw [this, hφχ w, key]
      ring
    have hden : (∫ w, (fun _ ↦ (1 : ℝ)) w *
        Real.exp (-(t * (tsupport χ).indicator (fun w ↦ R w - R p) w * 0)) *
        (χ w * Real.exp (-(t * (L w - L p))))) =
        Real.exp (t * L p) * ∫ w, χ w * Real.exp (-(t * L w)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      have key : Real.exp (-(t * (L w - L p))) = Real.exp (t * L p) * Real.exp (-(t * L w)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have : (fun _ ↦ (1 : ℝ)) w *
          Real.exp (-(t * (tsupport χ).indicator (fun w ↦ R w - R p) w * 0)) *
          (χ w * Real.exp (-(t * (L w - L p)))) = χ w * Real.exp (-(t * (L w - L p))) := by
        simp
      rw [this, key]
      ring
    rw [hnum, hden, mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- **The `q = 1` law.** Around a nondegenerate minimum, a residual `R` that is `ρ`-Lipschitz
from the minimizer perturbs the windowed normalized expectation of a bounded test `φ`
(supported where `χ = 1`) by at most `‖φ‖_∞ ρ √C_* √t`, for `t ≥ max(r₀^{-2}, 1)` and
`ρ² t ≤ 1`. -/
theorem abs_winExp_sub_le_of_lipschitz {R φ : EuclidD d → ℝ} (hRm : Measurable R) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hR : ∀ w, |R w - R p| ≤ ρ * ‖w - p‖) (hφm : Measurable φ) {Mφ : ℝ}
    (hφ : ∀ w, |φ w| ≤ Mφ) (hφχ : ∀ w, φ w * χ w = φ w) {t : ℝ} (ht : r₀ ^ (-2 : ℝ) ≤ t)
    (ht1 : 1 ≤ t) (hρt : ρ ^ 2 * t ≤ 1) :
    |winExp (fun w ↦ L w + R w) φ χ t - winExp L φ χ t| ≤
      Mφ * ρ * Real.sqrt (cstar d c C₀) * Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  obtain ⟨D, hD0, hD⟩ := h.exists_diam
  have hT := h.tiltData hRm hρ hR hD ht ht1 hρt
  have hMφ : 0 ≤ Mφ := le_trans (abs_nonneg _) (hφ p)
  have hbφ : Bdd φ := ⟨hφm, Mφ, hφ⟩
  have hC0 : 0 ≤ cstar d c C₀ := by
    unfold cstar
    have hI0 : 0 ≤ gaussLinConst (d := d) c :=
      integral_nonneg fun z ↦ mul_nonneg (by positivity) (Real.exp_pos _).le
    positivity
  -- the variance of the test is at most `Mφ²`
  have hVφ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      tiltCov volume (h.weight t) φ φ (h.resid R) t u ≤ Mφ ^ 2 := by
    intro u _
    have hpt : ∀ w, φ w * φ w ≤ (fun _ ↦ Mφ ^ 2) w := fun w ↦ by
      have := hφ w
      have h2 : φ w * φ w = |φ w| ^ 2 := by rw [sq_abs]; ring
      rw [h2]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have := hT.tiltExp_mono (hbφ.mul hbφ) (Bdd.const _) hpt t u
    rw [hT.tiltExp_const] at this
    unfold tiltCov
    nlinarith [sq_nonneg (tiltExp volume (h.weight t) φ (h.resid R) t u)]
  have hVR : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      tiltCov volume (h.weight t) (h.resid R) (h.resid R)
        (h.resid R) t u ≤ (ρ * Real.sqrt (cstar d c C₀ / t)) ^ 2 := by
    intro u hu
    have := h.tiltCov_res_le hRm hρ hR hD ht ht1 hρt hu
    rwa [mul_pow, Real.sq_sqrt (by positivity)]
  have hmain := hT.abs_tiltExp_one_sub_zero_le_of_var hbφ ht0.le hMφ
    (by positivity : 0 ≤ ρ * Real.sqrt (cstar d c C₀ / t)) hVφ hVR
  obtain ⟨he1, he0⟩ := h.tiltExp_endpoints (R := R) hφχ t
  rw [he1, he0] at hmain
  refine hmain.trans (le_of_eq ?_)
  rw [Real.sqrt_div hC0]
  calc t * (Mφ * (ρ * (Real.sqrt (cstar d c C₀) / Real.sqrt t)))
      = Mφ * ρ * Real.sqrt (cstar d c C₀) * (t / Real.sqrt t) := by ring
    _ = Mφ * ρ * Real.sqrt (cstar d c C₀) * Real.sqrt t := by rw [Real.div_sqrt]

end NondegWindow

end Laplace.Multi
