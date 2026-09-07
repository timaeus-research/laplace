/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PolydiscCoeff

/-!
# Holomorphy of the Cauchy coefficients in a parameter (Stage 8a — the gate)

Unit 266 (Astra #32, unit 1 of the derivative-identification sprint). The several-variable Cauchy
coefficient of the slice `F(x, ·)`, `x ↦ polyCoeff d r (F ∘ Fin.cons x) γ'`, is holomorphic in the
parameter `x` on a disc of radius `ρ ∈ (r, R)` when `F` is holomorphic on the open polydisc of
radius `R` (`differentiableOn_polyCoeff_param`). No differentiation under the integral is used: the
slice is represented by the one-variable Cauchy formula at radius `ρ`, the circle operator at radius
`ρ` is interchanged with the iterated operator at radius `r` (Fubini for continuous integrands,
`iterOp_circleOp_swap`), and the resulting Cauchy-type integral `x ↦ A_ρ((1 − x/z)⁻¹ g(z))` is
holomorphic by Mathlib's `hasFPowerSeriesOn_cauchy_integral`. Along the way `circleOp` is identified
with the circle average `(2π)⁻¹ ∫₀^{2π} g(ρe^{iθ}) dθ` (`circleOp_eq_integral`).
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

/-- The normalised circle operator is the circle average. -/
theorem circleOp_eq_integral {r : ℝ} (hr : r ≠ 0) (g : ℂ → ℂ) :
    circleOp r g =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap 0 r θ) := by
  unfold circleOp
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
  have h : ∀ θ : ℝ, circleMap 0 r θ * I * ((circleMap 0 r θ)⁻¹ * g (circleMap 0 r θ)) =
      I * g (circleMap 0 r θ) := by
    intro θ
    have hne : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr
    field_simp
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, ← mul_assoc]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

/-- Fubini for two interval integrals of a jointly continuous integrand. -/
theorem intervalIntegral_swap_of_continuous {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {f : ℝ → ℝ → ℂ} (hf : Continuous fun q : ℝ × ℝ => f q.1 q.2) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have hunc : Function.uncurry f = fun q : ℝ × ℝ => f q.1 q.2 := rfl
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    have h1 : IntegrableOn (Function.uncurry f) (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
      rw [hunc]
      exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact h1.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact integral_integral_swap hint

/-- Two circle operators with a jointly continuous integrand commute. -/
theorem circleOp_circleOp_swap {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) {K : ℂ → ℂ → ℂ}
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2)
      (Metric.sphere (0 : ℂ) ρ ×ˢ Metric.sphere (0 : ℂ) r)) :
    circleOp r (fun w => circleOp ρ fun z => K z w) =
      circleOp ρ fun z => circleOp r fun w => K z w := by
  have hc : Continuous fun q : ℝ × ℝ => K (circleMap 0 ρ q.2) (circleMap 0 r q.1) := by
    refine hK.comp_continuous ((continuous_circleMap 0 ρ).comp continuous_snd |>.prodMk
      ((continuous_circleMap 0 r).comp continuous_fst)) fun q => ?_
    exact ⟨circleMap_mem_sphere 0 hρ.le _, circleMap_mem_sphere 0 hr.le _⟩
  simp only [circleOp_eq_integral hr.ne', circleOp_eq_integral hρ.ne',
    intervalIntegral.integral_const_mul]
  rw [mul_left_comm]
  congr 2
  exact intervalIntegral_swap_of_continuous (by positivity) (by positivity) hc

/-- The iterated operator at radius `r` commutes with a circle operator at radius `ρ`. -/
theorem iterOp_circleOp_swap : ∀ (d : ℕ) {r ρ : ℝ}, 0 < r → 0 < ρ → ∀ {K : ℂ → (Fin d → ℂ) → ℂ},
    ContinuousOn (fun p : ℂ × (Fin d → ℂ) => K p.1 p.2) (Metric.sphere (0 : ℂ) ρ ×ˢ torusSet d r) →
    iterOp d r (fun w => circleOp ρ fun z => K z w) = circleOp ρ fun z => iterOp d r (K z)
  | 0, _, _, _, _, _, _ => by simp only [iterOp]
  | d + 1, r, ρ, hr, hρ, K, hK => by
    simp only [iterOp]
    have hcons : ∀ w₀ : ℂ, Continuous fun p : ℂ × (Fin d → ℂ) =>
        ((p.1, (Fin.cons w₀ p.2 : Fin (d + 1) → ℂ)) : ℂ × (Fin (d + 1) → ℂ)) := by
      intro w₀
      exact continuous_fst.prodMk (continuous_fin_cons_pair.comp (continuous_const.prodMk
        continuous_snd))
    have step1 : circleOp r (fun w₀ => iterOp d r fun w' => circleOp ρ fun z =>
        K z (Fin.cons w₀ w')) =
        circleOp r fun w₀ => circleOp ρ fun z => iterOp d r fun w' => K z (Fin.cons w₀ w') := by
      refine circleOp_congr hr.le fun w₀ hw₀ => ?_
      have hw₀' : ‖w₀‖ = r := by simpa using hw₀
      refine iterOp_circleOp_swap d hr hρ (K := fun z w' => K z (Fin.cons w₀ w')) ?_
      refine hK.comp (hcons w₀).continuousOn fun p hp => ?_
      exact ⟨hp.1, cons_mem_torusSet hw₀' hp.2⟩
    rw [step1]
    refine circleOp_circleOp_swap hr hρ ?_
    refine continuousOn_iterOp_param d hr (X := ℂ × ℂ)
      (G := fun p w' => K p.1 (Fin.cons p.2 w')) ?_
    have hmap : Continuous fun q : (ℂ × ℂ) × (Fin d → ℂ) =>
        ((q.1.1, (Fin.cons q.1.2 q.2 : Fin (d + 1) → ℂ)) : ℂ × (Fin (d + 1) → ℂ)) :=
      (continuous_fst.comp continuous_fst).prodMk (continuous_fin_cons_pair.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    refine hK.comp hmap.continuousOn fun q hq => ?_
    have hq2 : ‖q.1.2‖ = r := by simpa using hq.1.2
    exact ⟨hq.1.1, cons_mem_torusSet hq2 hq.2⟩

/-- The Cauchy-type integral `x ↦ A_ρ(z ↦ (1 − x/z)⁻¹ g(z))` of a continuous `g` is holomorphic on
the open disc. -/
theorem differentiableOn_circleOp_cauchyKernel {ρ : ℝ} (hρ : 0 < ρ) {g : ℂ → ℂ}
    (hg : ContinuousOn g (Metric.sphere (0 : ℂ) ρ)) :
    DifferentiableOn ℂ (fun x => circleOp ρ fun z => (1 - x / z)⁻¹ * g z) (Metric.ball 0 ρ) := by
  have hint : CircleIntegrable g 0 ρ := hg.circleIntegrable hρ.le
  set R : NNReal := ⟨ρ, hρ.le⟩ with hR
  have hRρ : (R : ℝ) = ρ := rfl
  have hRpos : 0 < R := by
    rw [← NNReal.coe_pos, hRρ]; exact hρ
  have hps := hasFPowerSeriesOn_cauchy_integral (c := 0) (R := R) (by rw [hRρ]; exact hint) hRpos
  have hdiff := hps.differentiableOn
  rw [Metric.eball_coe, hRρ] at hdiff
  refine hdiff.congr fun x hx => ?_
  have hx' : ‖x‖ < ρ := by simpa using hx
  unfold circleOp
  rw [smul_eq_mul]
  congr 1
  refine circleIntegral.integral_congr hρ.le fun z hz => ?_
  have hz' : ‖z‖ = ρ := by simpa using hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz'; exact hρ.ne hz'
  have hzx : z - x ≠ 0 := by
    intro h
    have : z = x := sub_eq_zero.1 h
    rw [this] at hz'; linarith
  simp only [smul_eq_mul]
  field_simp

/-- **The gate**: the several-variable Cauchy coefficient of the slice `F(x, ·)` is holomorphic in
the parameter `x` on the disc of radius `ρ ∈ (r, R)`. -/
theorem differentiableOn_polyCoeff_param {d : ℕ} {r ρ R : ℝ} (hr : 0 < r) (hrρ : r < ρ)
    (hρR : ρ < R) {F : (Fin (d + 1) → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (openPolydisc (d + 1) R))
    (γ' : Fin d → ℕ) :
    DifferentiableOn ℂ (fun x => polyCoeff d r (fun w' => F (Fin.cons x w')) γ')
      (Metric.ball 0 ρ) := by
  have hρ : 0 < ρ := hr.trans hrρ
  have hrR : r < R := hrρ.trans hρR
  have htorus : ∀ w' ∈ torusSet d r, w' ∈ openPolydisc d R := by
    intro w' hw'
    rw [mem_torusSet] at hw'
    rw [mem_openPolydisc]
    intro i; rw [hw' i]; exact hrR
  have hP : ContinuousOn (fun w' : Fin d → ℂ => ∏ i, (w' i)⁻¹ ^ γ' i) (torusSet d r) := by
    refine continuousOn_finsetProd _ fun i _ => ?_
    refine ContinuousOn.pow ?_ _
    refine ContinuousOn.inv₀ (continuous_apply i).continuousOn fun w' hw' => ?_
    rw [mem_torusSet] at hw'
    intro h; have := hw' i; rw [h, norm_zero] at this; exact hr.ne this
  -- continuity of the slice integrand on `sphere ρ × torus r`
  have hGcont : ContinuousOn (fun p : ℂ × (Fin d → ℂ) => F (Fin.cons p.1 p.2) *
      ∏ i, (p.2 i)⁻¹ ^ γ' i) (Metric.sphere (0 : ℂ) ρ ×ˢ torusSet d r) := by
    refine ContinuousOn.mul ?_ (hP.comp continuous_snd.continuousOn fun p hp => hp.2)
    refine hF.continuousOn.comp continuous_fin_cons_pair.continuousOn fun p hp => ?_
    have h1 : ‖p.1‖ < R := by
      have : ‖p.1‖ = ρ := by simpa using hp.1
      rw [this]; exact hρR
    exact cons_mem_openPolydisc h1 (htorus _ hp.2)
  have hg : ContinuousOn (fun z => polyCoeff d r (fun w' => F (Fin.cons z w')) γ')
      (Metric.sphere (0 : ℂ) ρ) := by
    unfold polyCoeff
    exact continuousOn_iterOp_param d hr (S := Metric.sphere (0 : ℂ) ρ)
      (G := fun z w' => F (Fin.cons z w') * ∏ i, (w' i)⁻¹ ^ γ' i) hGcont
  have key : ∀ x ∈ Metric.ball (0 : ℂ) ρ, polyCoeff d r (fun w' => F (Fin.cons x w')) γ' =
      circleOp ρ fun z => (1 - x / z)⁻¹ * polyCoeff d r (fun w' => F (Fin.cons z w')) γ' := by
    intro x hx
    have hx' : ‖x‖ < ρ := by simpa using hx
    unfold polyCoeff
    have hA : ∀ w' ∈ torusSet d r, F (Fin.cons x w') * ∏ i, (w' i)⁻¹ ^ γ' i =
        circleOp ρ fun z => (1 - x / z)⁻¹ * (F (Fin.cons z w') * ∏ i, (w' i)⁻¹ ^ γ' i) := by
      intro w' hw'
      have hslice : DiffContOnCl ℂ (fun t : ℂ => F (Fin.cons t w')) (Metric.ball 0 ρ) := by
        have hd : DifferentiableOn ℂ (fun t : ℂ => F (Fin.cons t w')) (Metric.ball 0 R) := by
          refine hF.comp (differentiable_cons_left w').differentiableOn fun t ht => ?_
          exact cons_mem_openPolydisc (by simpa using ht) (htorus _ hw')
        exact hd.diffContOnCl_ball (Metric.closedBall_subset_ball hρR)
      have hc := circleOp_cauchy hρ hslice hx'
      rw [← hc, mul_comm, ← circleOp_const_mul]
      congr 1; funext z; ring
    rw [iterOp_congr d hr.le hA]
    have hK : ContinuousOn (fun p : ℂ × (Fin d → ℂ) => (1 - x / p.1)⁻¹ *
        (F (Fin.cons p.1 p.2) * ∏ i, (p.2 i)⁻¹ ^ γ' i))
        (Metric.sphere (0 : ℂ) ρ ×ˢ torusSet d r) := by
      refine ContinuousOn.mul ?_ hGcont
      refine ContinuousOn.inv₀ ?_ fun p hp => ?_
      · refine continuousOn_const.sub (continuousOn_const.div continuous_fst.continuousOn ?_)
        intro p hp
        have : ‖p.1‖ = ρ := by simpa using hp.1
        intro h; rw [h, norm_zero] at this; exact hρ.ne this
      · have hp1 : ‖p.1‖ = ρ := by simpa using hp.1
        have hp0 : p.1 ≠ 0 := by
          intro h; rw [h, norm_zero] at hp1; exact hρ.ne hp1
        intro h
        have : x = p.1 := by
          have h' : x / p.1 = 1 := by linear_combination -h
          rwa [div_eq_one_iff_eq hp0] at h'
        rw [this] at hx'; linarith
    rw [iterOp_circleOp_swap d hr hρ hK]
    congr 1; funext z
    exact iterOp_const_mul d r _ _
  exact (differentiableOn_circleOp_cauchyKernel hρ hg).congr key

end Laplace.Grammar
