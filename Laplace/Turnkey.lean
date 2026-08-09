/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.AnalyticIdentifiability

/-!
# Turnkey integrability for the identifiability bound

The analytic identifiability bound
(`analytic_pencil_difference_lower_bound`) carries three per-`t`
integrability premises. This file discharges all of them from global
continuity of the potentials and continuity plus compact support of the
bump, and packages the result as
`analytic_pencil_difference_lower_bound'`: the 1D germbij Theorem 7.3
lower bound whose hypotheses are purely mathematical (analyticity at `0`
with differing germs, nonnegativity, quadratic domination near `0`, and a
continuous compactly supported bump equal to `1` near `0`).
-/

open MeasureTheory

namespace Laplace

section Integrability

variable {L₁ L₂ ψ : ℝ → ℝ}

/-- The minorant integrand is integrable: continuous, with support inside
`tsupport ψ`. -/
lemma integrable_minorant (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (t : ℝ) :
    Integrable (fun w ↦
      (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w)))) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  apply HasCompactSupport.intro hψs
  intro w hw
  rw [image_eq_zero_of_notMem_tsupport hw]
  ring

/-- Each pencil slice is integrable: continuous, with support inside
`tsupport ψ`. -/
lemma integrable_slice (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (t s : ℝ) :
    Integrable (fun w ↦
      ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
        Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))))) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  apply HasCompactSupport.intro hψs
  intro w hw
  rw [image_eq_zero_of_notMem_tsupport hw]
  ring

/-- The uncurried pencil integrand is integrable on the restricted product:
jointly continuous, bounded on `[0,1] × tsupport ψ`, and vanishing off
`ℝ × tsupport ψ`. -/
lemma integrable_pencil_product (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (t : ℝ) :
    Integrable (Function.uncurry fun s w ↦
      ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
        Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
  set f : ℝ × ℝ → ℝ := Function.uncurry fun s w ↦
    ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
      Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) with hf_def
  have hfc : Continuous f := by
    rw [hf_def]
    unfold Function.uncurry
    fun_prop
  -- Uniform bound on the compact cylinder `[0,1] × tsupport ψ`.
  have hTc : IsCompact (tsupport ψ) := hψs
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    hTc).exists_bound_of_continuousOn hfc.continuousOn
  set B' : ℝ := max B 0 with hB'_def
  -- The indicator majorant on `univ × tsupport ψ` is integrable.
  have hTm : MeasurableSet (tsupport ψ) := hTc.isClosed.measurableSet
  have hCylm : MeasurableSet (Set.univ ×ˢ tsupport ψ : Set (ℝ × ℝ)) :=
    MeasurableSet.univ.prod hTm
  have hμ : ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume)
      (Set.univ ×ˢ tsupport ψ) < ⊤ := by
    rw [Measure.prod_prod]
    apply ENNReal.mul_lt_top
    · rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono Set.Ioc_subset_Icc_self)
        isCompact_Icc.measure_lt_top
    · exact hTc.measure_lt_top
  have hmaj : Integrable
      ((Set.univ ×ˢ tsupport ψ : Set (ℝ × ℝ)).indicator fun _ ↦ B')
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
    rw [integrable_indicator_iff hCylm]
    exact integrableOn_const hμ.ne
  apply hmaj.mono' hfc.aestronglyMeasurable
  -- The a.e. bound, on the restricted product.
  have hrw : (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume
      = (volume.prod (volume : Measure ℝ)).restrict
          ((Set.Ioc (0 : ℝ) 1) ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hrw]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)]
    with p hp
  by_cases hw : p.2 ∈ tsupport ψ
  · have hpK : p ∈ Set.Icc (0 : ℝ) 1 ×ˢ tsupport ψ :=
      ⟨Set.Ioc_subset_Icc_self hp.1, hw⟩
    calc ‖f p‖ ≤ B := hB p hpK
      _ ≤ B' := le_max_left _ _
      _ = (Set.univ ×ˢ tsupport ψ : Set (ℝ × ℝ)).indicator (fun _ ↦ B') p := by
          have hpC : p ∈ (Set.univ ×ˢ tsupport ψ : Set (ℝ × ℝ)) :=
            ⟨Set.mem_univ _, hw⟩
          rw [Set.indicator_of_mem hpC]
  · have hf0 : f p = 0 := by
      have hψ0 : ψ p.2 = 0 := image_eq_zero_of_notMem_tsupport hw
      simp only [hf_def, Function.uncurry, hψ0, mul_zero, zero_mul]
    rw [hf0, norm_zero]
    exact Set.indicator_nonneg (fun _ _ ↦ le_max_right B 0) p

end Integrability

/-- **Turnkey identifiability lower bound** (germbij Theorem 7.3, 1D). All
hypotheses are mathematical: analyticity at `0` with differing germs,
nonnegativity, quadratic domination near `0`, and a continuous compactly
supported bump equal to `1` near `0`. -/
theorem analytic_pencil_difference_lower_bound'
    (L₁ L₂ ψ : ℝ → ℝ)
    (hL1a : AnalyticAt ℝ L₁ 0) (hL2a : AnalyticAt ℝ L₂ 0)
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hne : analyticOrderAt (fun w ↦ L₂ w - L₁ w) 0 ≠ ⊤)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hsum : ∀ w ∈ Set.Icc (0 : ℝ) R, L₁ w + L₂ w ≤ C0 * w ^ 2)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w ∈ Set.Icc (0 : ℝ) R, ψ w = 1) :
    ∃ (m : ℕ) (c r0 : ℝ), 0 < c ∧ 0 < r0 ∧ r0 ≤ R ∧
      ∀ t : ℝ, 4 ≤ r0 ^ 2 * t →
        c * (t * t ^ (-(m : ℝ) - 1 / 2))
          ≤ ∫ w, ((L₂ w - L₁ w) * ψ w) *
              (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := by
  obtain ⟨m, c, r0, hc, hr0, hr0R, hbound⟩ :=
    analytic_pencil_difference_lower_bound L₁ L₂ ψ hL1a hL2a hne hL1 hL2
      hC0 hR hsum hψ0 hψ1
  exact ⟨m, c, r0, hc, hr0, hr0R, fun t hrt ↦
    hbound t hrt (integrable_minorant hL1c hL2c hψc hψs t)
      (integrable_pencil_product hL1c hL2c hψc hψs t)
      (fun s _ ↦ integrable_slice hL1c hL2c hψc hψs t s)⟩

end Laplace
