/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.EntropyGapStability

/-!
# Continuity of the rate and of the reconstruction along segments

Between any two finite-rate responses `A, B` the rate is convex along the segment
(`genRate_segment_le_of_ne_top`), and with lower semicontinuity this gives continuity of the rate at
the endpoint, `𝓘((1 − t)A + tB) → 𝓘(B)` as `t ↑ 1` (`tendsto_genRate_segment_of_ne_top`), which
strengthens the special case of the segment from the featureless response. The entropy-gap stability
theorem then gives continuity of the reconstruction along every such segment for bounded observables
(`tendsto_integral_responseProjection_segment_of_ne_top`), boundary endpoints included.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **Convexity of the rate between finite-rate responses**:
`𝓘((1 − t)A + tB) ≤ (1 − t)𝓘(A) + t 𝓘(B)` for `0 < t < 1`. -/
theorem genRate_segment_le_of_ne_top {A B : J → ℝ} (hA : genRate ν S A ≠ ⊤)
    (hB : genRate ν S B ≠ ⊤) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    genRate ν S ((1 - t) • A + t • B) ≤
      ENNReal.ofReal (1 - t) * genRate ν S A + ENNReal.ofReal t * genRate ν S B := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, a = ⟨1 - t, by linarith⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, b = ⟨t, ht0.le⟩ := ⟨_, rfl⟩
  have haR : (a : ℝ) = 1 - t := by rw [ha]; rfl
  have hbR : (b : ℝ) = t := by rw [hb]; rfl
  have hab : a + b = 1 := by
    ext
    rw [NNReal.coe_add, haR, hbR, NNReal.coe_one]
    ring
  have ha0 : a ≠ 0 := by
    intro h
    have := congrArg NNReal.toReal h
    rw [haR, NNReal.coe_zero] at this
    linarith
  have hb0 : b ≠ 0 := by
    intro h
    have := congrArg NNReal.toReal h
    rw [hbR, NNReal.coe_zero] at this
    linarith
  have hgap := genRate_mixture_gap hS ν hA hB hab ha0 hb0
  have haE : (a : ℝ≥0∞) = ENNReal.ofReal (1 - t) := by rw [ENNReal.coe_nnreal_eq, haR]
  have hbE : (b : ℝ≥0∞) = ENNReal.ofReal t := by rw [ENNReal.coe_nnreal_eq, hbR]
  rw [haR, hbR, haE, hbE] at hgap
  rw [hgap]
  exact le_self_add

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
set_option linter.unusedSectionVars false in
/-- The segment converges to its endpoint. -/
theorem tendsto_segment_nhdsLT (A B : J → ℝ) :
    Tendsto (fun t : ℝ ↦ (1 - t) • A + t • B) (𝓝[<] (1 : ℝ)) (𝓝 B) := by
  have hc : Continuous fun t : ℝ ↦ (1 - t) • A + t • B := by fun_prop
  have h := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
  simpa using h

/-- **Continuity of the rate along segments between finite-rate responses**:
`𝓘((1 − t)A + tB) → 𝓘(B)` as `t ↑ 1`. -/
theorem tendsto_genRate_segment_of_ne_top {A B : J → ℝ} (hA : genRate ν S A ≠ ⊤)
    (hB : genRate ν S B ≠ ⊤) :
    Tendsto (fun t : ℝ ↦ genRate ν S ((1 - t) • A + t • B)) (𝓝[<] (1 : ℝ))
      (𝓝 (genRate ν S B)) := by
  refine tendsto_order.2 ⟨fun y hy ↦ (tendsto_segment_nhdsLT A B).eventually
    (lowerSemicontinuous_genRate ν S B y hy), fun y hy ↦ ?_⟩
  have hup : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (1 - t) * genRate ν S A +
      ENNReal.ofReal t * genRate ν S B) (𝓝[<] (1 : ℝ)) (𝓝 (genRate ν S B)) := by
    have h1 : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (1 - t) * genRate ν S A) (𝓝[<] (1 : ℝ))
        (𝓝 (ENNReal.ofReal (1 - 1) * genRate ν S A)) :=
      ENNReal.Tendsto.mul_const ((ENNReal.continuous_ofReal.tendsto _).comp
        (((continuous_const.sub continuous_id).tendsto 1).mono_left nhdsWithin_le_nhds))
        (Or.inr hA)
    have h2 : Tendsto (fun t : ℝ ↦ ENNReal.ofReal t * genRate ν S B) (𝓝[<] (1 : ℝ))
        (𝓝 (ENNReal.ofReal 1 * genRate ν S B)) :=
      ENNReal.Tendsto.mul_const ((ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_id.mono_left nhdsWithin_le_nhds)) (Or.inr hB)
    have := h1.add h2
    simpa using this
  filter_upwards [hup.eventually (Iio_mem_nhds hy), Ioo_mem_nhdsLT zero_lt_one] with t ht hmem
  exact lt_of_le_of_lt (genRate_segment_le_of_ne_top hS ν hA hB hmem.1 hmem.2) ht

/-- **Continuity of the reconstruction along segments between finite-rate responses**, for bounded
observables: `E_{Π((1−t)A + tB)}F → E_{Π(B)}F` as `t ↑ 1`, boundary endpoints included. -/
theorem tendsto_integral_responseProjection_segment_of_ne_top {A B : J → ℝ}
    (hA : genRate ν S A ≠ ⊤) (hB : genRate ν S B ≠ ⊤) {F : X → ℝ} (hF : Bdd F) :
    Tendsto (fun t : ℝ ↦ ∫ x, F x ∂responseProjection hS ν ((1 - t) • A + t • B))
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ x, F x ∂responseProjection hS ν B)) := by
  refine tendsto_integral_responseProjection_of_tendsto_genRate hS ν hB ?_
    (tendsto_segment_nhdsLT A B) (tendsto_genRate_segment_of_ne_top hS ν hA hB) hF
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB⟩)
    (genRate_segment_le_of_ne_top hS ν hA hB ht.1 ht.2)

end Laplace.Multi
