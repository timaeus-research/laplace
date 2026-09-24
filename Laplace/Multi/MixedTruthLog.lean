/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The mixed truth monomial `xy = s` at the logarithmic endpoint

The canonical mixed-truth model: the fibre `{xy = σ/t}` inside the box `(0,ρ)²`, carrying the
measure `dx/x`, and an integrand `f(x, y)` continuous on the closed box. Neither coordinate is
solved for the other near the corner, so the bridge map of the wall-chart layer does not extend
continuously to the face point; nevertheless the fibre integral has a logarithmic asymptotic with
a point mass at the corner:

`(1/log t) ∫_{σ/(ρt)}^{ρ} f(x, σ/(tx)) dx/x → f(0,0)`

(`tendsto_mixedLog`). The substitution `x = ρ e^{−Lu}`, `L = log(ρ² t/σ)`, turns the fibre
integral into `L ∫_0^1 f(ρe^{−Lu}, ρe^{−L(1−u)}) du` (`integral_fibre_eq_scale`); for `0 < u < 1`
both coordinates tend to `0`, the endpoint layers carry no logarithmic mass, and `L/log t → 1`.
Applied to `F(x,y) = xy·a(x,y)` with a positive unit `a`, weight `w` and observables `ψ, χ`, the
fibre expectation converges to the point evaluation `ψ(0,0)/χ(0,0)` when `w(0,0)χ(0,0) > 0`
(`tendsto_mixedLog_ratio`): concentration arises after logarithmic averaging rather than by
pointwise extension of the bridge (Astra's round-3 target (2), `research_round3_v1.md`).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

section Substitution

variable {ρ σ : ℝ}

/-- The logarithmic scale `L = log(ρ² t/σ)`. -/
noncomputable def mixedScale (ρ σ t : ℝ) : ℝ := log (ρ ^ 2 * t / σ)

theorem mixedScale_pos (hρ : 0 < ρ) (hσ : 0 < σ) {t : ℝ} (ht : σ / ρ ^ 2 < t) :
    0 < mixedScale ρ σ t := by
  unfold mixedScale
  refine log_pos ?_
  rw [lt_div_iff₀ hσ, one_mul, ← div_lt_iff₀' (by positivity)]
  exact ht

theorem exp_neg_mixedScale (hρ : 0 < ρ) (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    ρ * exp (-mixedScale ρ σ t) = σ / (ρ * t) := by
  unfold mixedScale
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

theorem mixedScale_eq (hρ : 0 < ρ) (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    mixedScale ρ σ t = 2 * log ρ - log σ + log t := by
  unfold mixedScale
  rw [Real.log_div (by positivity) hσ.ne', Real.log_mul (by positivity) ht.ne',
    Real.log_pow]
  push_cast
  ring

/-- The image of `(0,1)` under `u ↦ ρ e^{−Lu}` is the fibre range `(σ/(ρt), ρ)`. -/
theorem image_mixed (hρ : 0 < ρ) (hσ : 0 < σ) {t : ℝ} (ht : σ / ρ ^ 2 < t) :
    (fun u : ℝ ↦ ρ * exp (-(mixedScale ρ σ t * u))) '' Ioo 0 1 = Ioo (σ / (ρ * t)) ρ := by
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
  have hL := mixedScale_pos hρ hσ ht
  rw [← exp_neg_mixedScale hρ hσ ht0]
  ext x
  simp only [Set.mem_image, Set.mem_Ioo]
  constructor
  · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
    constructor
    · refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) hρ
      nlinarith
    · calc ρ * exp (-(mixedScale ρ σ t * u)) < ρ * exp 0 := by
            refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) hρ
            nlinarith
        _ = ρ := by rw [Real.exp_zero, mul_one]
  · rintro ⟨h1, h2⟩
    have hx0 : 0 < x := lt_trans (by positivity) h1
    refine ⟨-log (x / ρ) / mixedScale ρ σ t, ⟨?_, ?_⟩, ?_⟩
    · have : log (x / ρ) < 0 := log_neg (by positivity) ((div_lt_one hρ).mpr h2)
      exact div_pos (by linarith) hL
    · rw [div_lt_one hL, neg_lt]
      have h := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul hρ.ne' (exp_pos _).ne', Real.log_exp] at h
      rw [Real.log_div hx0.ne' hρ.ne']
      linarith
    · rw [show mixedScale ρ σ t * (-log (x / ρ) / mixedScale ρ σ t) = -log (x / ρ) by
        field_simp, neg_neg, Real.exp_log (div_pos hx0 hρ)]
      field_simp

/-- **The substitution `x = ρ e^{−Lu}`** on the fibre range:
`∫ g(x) dx/x = L ∫_0^1 g(ρe^{−Lu}) du`. -/
theorem integral_fibre_eq_scale (hρ : 0 < ρ) (hσ : 0 < σ) {t : ℝ} (ht : σ / ρ ^ 2 < t)
    (g : ℝ → ℝ) :
    ∫ x in Ioo (σ / (ρ * t)) ρ, g x / x =
      ∫ u in Ioo (0 : ℝ) 1, mixedScale ρ σ t * g (ρ * exp (-(mixedScale ρ σ t * u))) := by
  have hL := mixedScale_pos hρ hσ ht
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun u : ℝ ↦ ρ * exp (-(mixedScale ρ σ t * u)))
        (-(mixedScale ρ σ t * (ρ * exp (-(mixedScale ρ σ t * u))))) (Ioo 0 1) u := fun u _ ↦ by
    have h := (((hasDerivAt_id' u).const_mul (-mixedScale ρ σ t)).exp).const_mul ρ
    refine ((h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)).congr_deriv
      ?_).hasDerivWithinAt
    · simp only [neg_mul]
    · rw [neg_mul]
      ring
  have hinj : InjOn (fun u : ℝ ↦ ρ * exp (-(mixedScale ρ σ t * u))) (Ioo 0 1) := by
    intro u _ v _ huv
    have h1 := mul_left_cancel₀ hρ.ne' huv
    have h2 := neg_injective (exp_injective h1)
    exact mul_left_cancel₀ hL.ne' h2
  rw [← image_mixed hρ hσ ht, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv
    hinj (fun x ↦ g x / x)]
  refine setIntegral_congr_fun measurableSet_Ioo fun u _ ↦ ?_
  have hΦ : ρ * exp (-(mixedScale ρ σ t * u)) ≠ 0 := by positivity
  rw [abs_neg, abs_of_pos (by positivity), smul_eq_mul, mul_assoc, ← mul_div_assoc,
    mul_div_cancel_left₀ _ hΦ]

end Substitution

section Limit

variable {ρ σ : ℝ}

/-- The second coordinate on the fibre: `σ/(t x) = ρ e^{−L(1−u)}` at `x = ρ e^{−Lu}`. -/
theorem fibre_second_coord (hρ : 0 < ρ) (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    σ / (t * (ρ * exp (-(mixedScale ρ σ t * u)))) = ρ * exp (-(mixedScale ρ σ t * (1 - u))) := by
  rw [show -(mixedScale ρ σ t * (1 - u)) = -mixedScale ρ σ t + mixedScale ρ σ t * u by ring,
    Real.exp_add, ← mul_assoc ρ, exp_neg_mixedScale hρ hσ ht, Real.exp_neg]
  have := exp_pos (mixedScale ρ σ t * u)
  field_simp

/-- **The mixed truth monomial at the logarithmic endpoint**: the fibre integral of a continuous
integrand against `dx/x` on `{xy = σ/t}` grows like `log t · f(0,0)`. -/
theorem tendsto_mixedLog (hρ : 0 < ρ) (hσ : 0 < σ) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ ↦ f p.1 p.2) (Icc 0 ρ ×ˢ Icc 0 ρ)) :
    Tendsto (fun t ↦ (∫ x in Ioo (σ / (ρ * t)) ρ, f x (σ / (t * x)) / x) / log t) atTop
      (𝓝 (f 0 0)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf
  have hLt : Tendsto (fun t ↦ mixedScale ρ σ t) atTop atTop := by
    have : Tendsto (fun t : ℝ ↦ ρ ^ 2 * t / σ) atTop atTop :=
      (tendsto_id.const_mul_atTop (by positivity)).atTop_div_const hσ
    exact Real.tendsto_log_atTop.comp this
  have hratio : Tendsto (fun t ↦ mixedScale ρ σ t / log t) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t ↦ (2 * log ρ - log σ) / log t + 1) atTop (𝓝 (0 + 1)) :=
      (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add tendsto_const_nhds
    rw [zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [mixedScale_eq hρ hσ (by linarith), add_div, div_self (log_pos ht).ne']
  -- the arguments stay in the closed box once `L ≥ 0`
  have hbox : ∀ {t : ℝ}, 0 ≤ mixedScale ρ σ t → ∀ u ∈ Ioo (0 : ℝ) 1,
      (ρ * exp (-(mixedScale ρ σ t * u)), ρ * exp (-(mixedScale ρ σ t * (1 - u)))) ∈
        Icc (0 : ℝ) ρ ×ˢ Icc (0 : ℝ) ρ := by
    intro t hL u hu
    have e1 : ∀ v : ℝ, 0 ≤ v → ρ * exp (-(mixedScale ρ σ t * v)) ≤ ρ := fun v hv ↦ by
      calc ρ * exp (-(mixedScale ρ σ t * v)) ≤ ρ * 1 := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr ?_) hρ.le
            exact neg_nonpos.mpr (mul_nonneg hL hv)
        _ = ρ := mul_one _
    exact ⟨⟨by positivity, e1 u hu.1.le⟩, ⟨by positivity, e1 (1 - u) (by linarith [hu.2])⟩⟩
  have hGlim : Tendsto (fun t ↦ ∫ u in Ioo (0 : ℝ) 1,
      f (ρ * exp (-(mixedScale ρ σ t * u))) (ρ * exp (-(mixedScale ρ σ t * (1 - u))))) atTop
      (𝓝 (f 0 0)) := by
    have hint : ∫ u in Ioo (0 : ℝ) 1, f 0 0 = f 0 0 := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioo, sub_zero,
        ENNReal.toReal_ofReal zero_le_one, one_smul]
    rw [← hint]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C) ?_ ?_ (integrable_const _)
      ?_
    · filter_upwards [eventually_gt_atTop (σ / ρ ^ 2)] with t ht
      have hL := (mixedScale_pos hρ hσ ht).le
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      have hmapc : Continuous fun u : ℝ ↦ (ρ * exp (-(mixedScale ρ σ t * u)),
          ρ * exp (-(mixedScale ρ σ t * (1 - u)))) := by fun_prop
      exact hf.comp hmapc.continuousOn fun u hu ↦ hbox hL u hu
    · filter_upwards [eventually_gt_atTop (σ / ρ ^ 2)] with t ht
      have hL := (mixedScale_pos hρ hσ ht).le
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact ae_of_all _ fun u hu ↦ hC _ (hbox hL u hu)
    · rw [ae_restrict_iff' measurableSet_Ioo]
      refine ae_of_all _ fun u hu ↦ ?_
      have h1 : Tendsto (fun t ↦ ρ * exp (-(mixedScale ρ σ t * u))) atTop (𝓝 0) := by
        have := (tendsto_exp_neg_atTop_nhds_zero.comp (hLt.atTop_mul_const hu.1)).const_mul ρ
        simpa [Function.comp_def] using this
      have h2 : Tendsto (fun t ↦ ρ * exp (-(mixedScale ρ σ t * (1 - u)))) atTop (𝓝 0) := by
        have := (tendsto_exp_neg_atTop_nhds_zero.comp
          (hLt.atTop_mul_const (by linarith [hu.2] : (0 : ℝ) < 1 - u))).const_mul ρ
        simpa [Function.comp_def] using this
      have hpair := h1.prodMk_nhds h2
      have hmem : ∀ᶠ t in atTop, (ρ * exp (-(mixedScale ρ σ t * u)),
          ρ * exp (-(mixedScale ρ σ t * (1 - u)))) ∈ Icc (0 : ℝ) ρ ×ˢ Icc (0 : ℝ) ρ := by
        filter_upwards [eventually_gt_atTop (σ / ρ ^ 2)] with t ht
        exact hbox (mixedScale_pos hρ hσ ht).le u hu
      have h00 : ((0 : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) ρ ×ˢ Icc (0 : ℝ) ρ :=
        ⟨⟨le_rfl, hρ.le⟩, ⟨le_rfl, hρ.le⟩⟩
      exact (hf _ h00).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hpair, hmem⟩)
  have hmain := hratio.mul hGlim
  rw [one_mul] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (σ / ρ ^ 2), eventually_gt_atTop 1] with t ht ht1
  have ht0 : 0 < t := by linarith
  have hfib := integral_fibre_eq_scale hρ hσ ht (fun x ↦ f x (σ / (t * x)))
  beta_reduce at hfib
  rw [hfib, integral_const_mul, div_mul_eq_mul_div]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioo fun u _ ↦ ?_
  rw [fibre_second_coord hρ hσ ht0]

/-- **The mixed truth fibre expectation**: for `F(x,y) = xy·a(x,y)` with a continuous unit `a`,
weight `w` and observables `ψ, χ` on the closed box, the fibre expectation on `{xy = σ/t}`
converges to the point evaluation `ψ(0,0)/χ(0,0)` when `w(0,0) χ(0,0) ≠ 0`. -/
theorem tendsto_mixedLog_ratio (hρ : 0 < ρ) (hσ : 0 < σ) {a w ψ χ : ℝ → ℝ → ℝ}
    (ha : ContinuousOn (fun p : ℝ × ℝ ↦ a p.1 p.2) (Icc 0 ρ ×ˢ Icc 0 ρ))
    (hw : ContinuousOn (fun p : ℝ × ℝ ↦ w p.1 p.2) (Icc 0 ρ ×ˢ Icc 0 ρ))
    (hψ : ContinuousOn (fun p : ℝ × ℝ ↦ ψ p.1 p.2) (Icc 0 ρ ×ˢ Icc 0 ρ))
    (hχ : ContinuousOn (fun p : ℝ × ℝ ↦ χ p.1 p.2) (Icc 0 ρ ×ˢ Icc 0 ρ))
    (hpos : w 0 0 * χ 0 0 ≠ 0) :
    Tendsto (fun t ↦
        (∫ x in Ioo (σ / (ρ * t)) ρ,
          exp (-(t * (x * (σ / (t * x)) * a x (σ / (t * x))))) * w x (σ / (t * x)) *
            ψ x (σ / (t * x)) / x) /
        ∫ x in Ioo (σ / (ρ * t)) ρ,
          exp (-(t * (x * (σ / (t * x)) * a x (σ / (t * x))))) * w x (σ / (t * x)) *
            χ x (σ / (t * x)) / x) atTop (𝓝 (ψ 0 0 / χ 0 0)) := by
  have hE : ContinuousOn (fun p : ℝ × ℝ ↦ exp (-(σ * a p.1 p.2)) * w p.1 p.2)
      (Icc 0 ρ ×ˢ Icc 0 ρ) :=
    (Real.continuous_exp.comp_continuousOn ((continuousOn_const.mul ha).neg)).mul hw
  have hfψ : ContinuousOn (fun p : ℝ × ℝ ↦ exp (-(σ * a p.1 p.2)) * w p.1 p.2 * ψ p.1 p.2)
      (Icc 0 ρ ×ˢ Icc 0 ρ) := hE.mul hψ
  have hfχ : ContinuousOn (fun p : ℝ × ℝ ↦ exp (-(σ * a p.1 p.2)) * w p.1 p.2 * χ p.1 p.2)
      (Icc 0 ρ ×ˢ Icc 0 ρ) := hE.mul hχ
  have h1 := tendsto_mixedLog hρ hσ (f := fun x y ↦ exp (-(σ * a x y)) * w x y * ψ x y) hfψ
  have h2 := tendsto_mixedLog hρ hσ (f := fun x y ↦ exp (-(σ * a x y)) * w x y * χ x y) hfχ
  have hw0 : w 0 0 ≠ 0 := left_ne_zero_of_mul hpos
  have hχ0 : χ 0 0 ≠ 0 := right_ne_zero_of_mul hpos
  have hne : exp (-(σ * a 0 0)) * w 0 0 * χ 0 0 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (exp_pos _).ne' hw0) hχ0
  have hlim := h1.div h2 hne
  rw [mul_div_mul_left _ _ (mul_ne_zero (exp_pos _).ne' hw0)] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have hlog : log t ≠ 0 := (log_pos ht).ne'
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hlog]
  have e : ∀ x ∈ Ioo (σ / (ρ * t)) ρ, ∀ g : ℝ → ℝ → ℝ,
      exp (-(t * (x * (σ / (t * x)) * a x (σ / (t * x))))) * w x (σ / (t * x)) *
        g x (σ / (t * x)) / x =
      exp (-(σ * a x (σ / (t * x)))) * w x (σ / (t * x)) * g x (σ / (t * x)) / x := by
    intro x hx g
    have hx0 : 0 < x := lt_trans (by positivity) hx.1
    rw [show t * (x * (σ / (t * x)) * a x (σ / (t * x))) = σ * a x (σ / (t * x)) by
      field_simp]
  rw [setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ e x hx ψ,
    setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ e x hx χ]

end Limit

end Laplace.Multi
