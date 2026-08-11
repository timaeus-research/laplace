/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.LeadingIdentifiability

/-!
# Turnkey identifiability, multivariate

The multivariate analogue of the 1D turnkey theorem: the three per-`t`
integrability premises of the leading-part corollary are discharged from
global continuity of the potentials and continuity plus compact support of
the bump. The integrability lemmas are the 1D ones with `ι → ℝ` in place of
`ℝ`; nothing in their proofs was one-dimensional. The result,
`leading_part_pencil_difference_lower_bound'`, is the germbij Theorem 7.3
lower bound in `ℝ^d` whose every hypothesis is a mathematical property of
the potentials and the bump.
-/

open MeasureTheory

namespace Laplace

section Integrability

variable {ι : Type*} [Fintype ι] {L₁ L₂ ψ : (ι → ℝ) → ℝ}

/-- The minorant integrand is integrable (multivariate). -/
lemma integrable_minorant_multi (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (t : ℝ) :
    Integrable (fun w ↦
      (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w)))) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  apply HasCompactSupport.intro hψs
  intro w hw
  rw [image_eq_zero_of_notMem_tsupport hw]
  ring

/-- Each pencil slice is integrable (multivariate). -/
lemma integrable_slice_multi (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (t s : ℝ) :
    Integrable (fun w ↦
      ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
        Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))))) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  apply HasCompactSupport.intro hψs
  intro w hw
  rw [image_eq_zero_of_notMem_tsupport hw]
  ring

/-- The uncurried pencil integrand is integrable on the restricted product
(multivariate). -/
lemma integrable_pencil_product_multi (hL1c : Continuous L₁)
    (hL2c : Continuous L₂) (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (t : ℝ) :
    Integrable (Function.uncurry fun s w ↦
      ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
        Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
  set f : ℝ × (ι → ℝ) → ℝ := Function.uncurry fun s w ↦
    ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
      Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) with hf_def
  have hfc : Continuous f := by
    rw [hf_def]
    unfold Function.uncurry
    fun_prop
  have hTc : IsCompact (tsupport ψ) := hψs
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    hTc).exists_bound_of_continuousOn hfc.continuousOn
  set B' : ℝ := max B 0 with hB'_def
  have hTm : MeasurableSet (tsupport ψ) := hTc.isClosed.measurableSet
  have hCylm : MeasurableSet
      (Set.univ ×ˢ tsupport ψ : Set (ℝ × (ι → ℝ))) :=
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
      ((Set.univ ×ˢ tsupport ψ : Set (ℝ × (ι → ℝ))).indicator fun _ ↦ B')
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
    rw [integrable_indicator_iff hCylm]
    exact integrableOn_const hμ.ne
  apply hmaj.mono' hfc.aestronglyMeasurable
  have hrw : (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (volume : Measure (ι → ℝ))
      = ((volume : Measure ℝ).prod volume).restrict
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
      _ = (Set.univ ×ˢ tsupport ψ : Set (ℝ × (ι → ℝ))).indicator
            (fun _ ↦ B') p := by
          have hpC : p ∈ (Set.univ ×ˢ tsupport ψ : Set (ℝ × (ι → ℝ))) :=
            ⟨Set.mem_univ _, hw⟩
          rw [Set.indicator_of_mem hpC]
  · have hf0 : f p = 0 := by
      have hψ0 : ψ p.2 = 0 := image_eq_zero_of_notMem_tsupport hw
      simp only [hf_def, Function.uncurry, hψ0, mul_zero, zero_mul]
    rw [hf0, norm_zero]
    exact Set.indicator_nonneg (fun _ _ ↦ le_max_right B 0) p

end Integrability

/-- **Turnkey identifiability lower bound, multivariate** (germbij
Theorem 7.3, `ℝ^d`). Every hypothesis is mathematical: Taylor structure of
the difference, nonnegativity, quadratic domination near `0`, and a
continuous compactly supported bump equal to `1` near `0`. -/
theorem leading_part_pencil_difference_lower_bound'
    {ι : Type*} [Fintype ι] (L₁ L₂ ψ P : (ι → ℝ) → ℝ) (m : ℕ)
    (hPc : Continuous P)
    (hPh : ∀ (c : ℝ) (x : ι → ℝ), 0 ≤ c → P (c • x) = c ^ m * P x)
    {x₀ : ι → ℝ} (hx₀ : P x₀ ≠ 0) (hx₀n : ‖x₀‖ = 3 / 2)
    {C u₁ : ℝ} (hC : 0 ≤ C) (hu₁ : 0 < u₁)
    (hrem : ∀ x : ι → ℝ, ‖x‖ ≤ 2 * u₁ →
      |(L₂ x - L₁ x) - P x| ≤ C * ‖x‖ ^ (m + 1))
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hsum : ∀ w : ι → ℝ, ‖w‖ ≤ R → L₁ w + L₂ w ≤ C0 * ‖w‖ ^ 2)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ R → ψ w = 1) :
    ∃ (κ T₀ : ℝ), 0 < κ ∧ 0 < T₀ ∧
      ∀ t : ℝ, T₀ ≤ t →
        κ * (t * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2))
          ≤ ∫ w, ((L₂ w - L₁ w) * ψ w) *
              (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := by
  obtain ⟨κ, T₀, hκ, hT₀, hbound⟩ :=
    leading_part_pencil_difference_lower_bound L₁ L₂ ψ P m hPc hPh hx₀ hx₀n
      hC hu₁ hrem hL1 hL2 hC0 hR hsum hψ0 hψ1
  exact ⟨κ, T₀, hκ, hT₀, fun t ht ↦
    hbound t ht (integrable_minorant_multi hL1c hL2c hψc hψs t)
      (integrable_pencil_product_multi hL1c hL2c hψc hψs t)
      (fun s _ ↦ integrable_slice_multi hL1c hL2c hψc hψs t s)⟩

end Laplace
