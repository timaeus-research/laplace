/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Headline

/-!
# Convergence in distribution is stable under modifications of small probability

A generic lemma (`tendstoInDistribution_of_approx`): if for every `η > 0` there are random variables
`Y_n^η ⇒ W^η` with `μ {X_n ≠ Y_n^η} ≤ η` eventually and `μ' {Z ≠ W^η} ≤ η`, then `X_n ⇒ Z`.
Proof via the bounded-Lipschitz characterisation of weak convergence
(`tendsto_iff_forall_lipschitz_integral_tendsto`): a test function `f` with `dist (f x) (f y) ≤ C`
changes its integral by at most `C η` under a modification on an event of probability `η`
(`abs_integral_comp_sub_le_of_ne`). This is the tool that lets a continuous-mapping argument be
run on a map that is only continuous off a set of small limiting probability (the division in the
posterior ratio). Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology

namespace Laplace.Grammar

variable {E : Type*} [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [MeasurableEq E] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [PseudoEMetricSpace E] [OpensMeasurableSpace E] [MeasurableEq E] in
/-- A bounded measurable test function has an integrable composite. -/
theorem integrable_comp_of_bounded (f : E → ℝ) (hf : Measurable f) (x₀ : E) (C : ℝ)
    (hC : ∀ x y, dist (f x) (f y) ≤ C) (X : Ω → E) (hX : Measurable X) :
    Integrable (fun ω => f (X ω)) μ := by
  refine Integrable.of_bound (hf.comp hX).aestronglyMeasurable (‖f x₀‖ + C)
    (Filter.Eventually.of_forall fun ω => ?_)
  have := hC (X ω) x₀
  rw [Real.dist_eq] at this
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := abs_sub_abs_le_abs_sub (f (X ω)) (f x₀)
  linarith

omit [PseudoEMetricSpace E] [OpensMeasurableSpace E] in
/-- **Modification bound**: two random variables that differ on an event of probability `≤ η`
have integrals of a `C`-bounded test function within `C η`. -/
theorem abs_integral_comp_sub_le_of_ne (f : E → ℝ) (hf : Measurable f) (x₀ : E) (C : ℝ)
    (hC : ∀ x y, dist (f x) (f y) ≤ C) (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (η : ℝ) (hη : 0 ≤ η) (hS : μ {ω | X ω ≠ Y ω} ≤ ENNReal.ofReal η) :
    |(∫ ω, f (X ω) ∂μ) - ∫ ω, f (Y ω) ∂μ| ≤ C * η := by
  have hC0 : 0 ≤ C := le_trans dist_nonneg (hC x₀ x₀)
  have hSm : MeasurableSet {ω | X ω ≠ Y ω} := (measurableSet_eq_fun hX hY).compl
  have hiX := integrable_comp_of_bounded (μ := μ) f hf x₀ C hC X hX
  have hiY := integrable_comp_of_bounded (μ := μ) f hf x₀ C hC Y hY
  rw [← integral_sub hiX hiY]
  have hg : Integrable ({ω | X ω ≠ Y ω}.indicator fun _ => C) μ :=
    (integrable_const C).indicator hSm
  have hbound : ∀ ω, ‖f (X ω) - f (Y ω)‖ ≤ {ω | X ω ≠ Y ω}.indicator (fun _ => C) ω := by
    intro ω
    by_cases h : X ω = Y ω
    · have : ω ∉ {ω | X ω ≠ Y ω} := fun h' => h' h
      rw [Set.indicator_of_notMem this, h, sub_self, norm_zero]
    · have : ω ∈ {ω | X ω ≠ Y ω} := h
      rw [Set.indicator_of_mem this, Real.norm_eq_abs, ← Real.dist_eq]
      exact hC _ _
  have h := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  rw [integral_indicator_const C hSm, smul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hη hS) hC0

variable {ι : Type*} {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {l : Filter ι} [l.IsCountablyGenerated]

set_option backward.isDefEq.respectTransparency.types false in
/-- **Approximation lemma**: convergence in distribution is stable under modifications on events
of small probability. -/
theorem tendstoInDistribution_of_approx [Nonempty E] (X : ι → Ω → E) (Z : Ω' → E)
    (hX : ∀ n, Measurable (X n)) (hZ : Measurable Z)
    (happrox : ∀ η : ℝ, 0 < η → ∃ (Y : ι → Ω → E) (W : Ω' → E),
      (∀ n, Measurable (Y n)) ∧ Measurable W ∧
      TendstoInDistribution Y l W (fun _ => μ) μ' ∧
      (∀ᶠ n in l, μ {ω | X n ω ≠ Y n ω} ≤ ENNReal.ofReal η) ∧
      μ' {ω | Z ω ≠ W ω} ≤ ENNReal.ofReal η) :
    TendstoInDistribution X l Z (fun _ => μ) μ' where
  forall_aemeasurable := fun n => (hX n).aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro f ⟨C, hC⟩ ⟨L, hL⟩
    have hfm : Measurable f := hL.continuous.measurable
    obtain ⟨x₀⟩ := (inferInstance : Nonempty E)
    have hC0 : 0 ≤ C := le_trans dist_nonneg (hC x₀ x₀)
    simp only [ProbabilityMeasure.coe_mk]
    simp only [integral_map (hX _).aemeasurable hfm.aestronglyMeasurable,
      integral_map hZ.aemeasurable hfm.aestronglyMeasurable]
    rw [Metric.tendsto_nhds]
    intro ε hε
    set η : ℝ := ε / (3 * (C + 1)) with hηdef
    have hη : 0 < η := by positivity
    have hCη : C * η ≤ ε / 3 := by
      rw [hηdef]
      have : C * (ε / (3 * (C + 1))) = ε / 3 * (C / (C + 1)) := by field_simp
      rw [this]
      have : C / (C + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact mul_le_of_le_one_right (by positivity) this
    obtain ⟨Y, W, hYm, hWm, hYW, hXY, hZW⟩ := happrox η hη
    have h1 := hYW.tendsto
    rw [tendsto_iff_forall_lipschitz_integral_tendsto] at h1
    have h2 := h1 f ⟨C, hC⟩ ⟨L, hL⟩
    simp only [ProbabilityMeasure.coe_mk] at h2
    simp only [integral_map (hYW.forall_aemeasurable _) hfm.aestronglyMeasurable,
      integral_map hYW.aemeasurable_limit hfm.aestronglyMeasurable] at h2
    rw [Metric.tendsto_nhds] at h2
    have hZW' := abs_integral_comp_sub_le_of_ne (μ := μ') f hfm x₀ C hC Z W hZ hWm η hη.le hZW
    filter_upwards [h2 (ε / 3) (by positivity), hXY] with n hn hXYn
    have hXY' := abs_integral_comp_sub_le_of_ne (μ := μ) f hfm x₀ C hC (X n) (Y n) (hX n) (hYm n)
      η hη.le hXYn
    rw [Real.dist_eq] at hn ⊢
    calc |(∫ ω, f (X n ω) ∂μ) - ∫ ω, f (Z ω) ∂μ'|
        = |((∫ ω, f (X n ω) ∂μ) - ∫ ω, f (Y n ω) ∂μ) + ((∫ ω, f (Y n ω) ∂μ) - ∫ ω, f (W ω) ∂μ')
            + ((∫ ω, f (W ω) ∂μ') - ∫ ω, f (Z ω) ∂μ')| := by ring_nf
      _ ≤ |(∫ ω, f (X n ω) ∂μ) - ∫ ω, f (Y n ω) ∂μ| + |(∫ ω, f (Y n ω) ∂μ) - ∫ ω, f (W ω) ∂μ'|
            + |(∫ ω, f (W ω) ∂μ') - ∫ ω, f (Z ω) ∂μ'| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ < ε / 3 + ε / 3 + ε / 3 := by
          have h3 : |(∫ ω, f (W ω) ∂μ') - ∫ ω, f (Z ω) ∂μ'| ≤ C * η := by
            rw [abs_sub_comm]; exact hZW'
          have := hXY'.trans hCη
          have := h3.trans hCη
          linarith
      _ = ε := by ring

end Laplace.Grammar
