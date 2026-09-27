/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseAttainableChamber

/-!
# The chamber-classifier form of the resolution floor

`ResponseAttainableChamber` bounds every test between `n` samples of a data law `D` and of its
least-information alternative `D_{a/√n}` along an attainable direction. To conclude that the
**chambers** of the two means cannot be classified one needs, in addition, that the two population
means receive different labels: with that hypothesis every measurable two-label classifier `c` has
`P_{D_{a/√n}}(c ≠ ℓ₁) + P_D(c ≠ ℓ₀) ≥ 2 L_n` where `ℓ₀ ≠ ℓ₁` are the labels of `m_D` and of
`m_{D_{a/√n}}` (`chamber_classifier_error_ge`), and `2 L_n → 1 − √(a² ⟨e, Σ_D⁺ e⟩/2)`. If both
means lie in the same chamber, classification can be perfect while the laws remain hard to
distinguish; the separation hypothesis is what turns the testing floor into a classification floor.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Classifier

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D]
include hS

/-- The least-information score of an annihilated displacement. -/
local notation "hE" he => dirLoss S (dataDualSing hS ν D he : J → ℝ)

omit [Nonempty J] [IsProbabilityMeasure ν] in
/-- **THE CHAMBER-CLASSIFIER FLOOR**: if the two population means receive different labels
`ℓ₀ ≠ ℓ₁`, every measurable two-label classifier of `n` samples has total error at least `2 L_n`,
`P_{D_{a/√n}}(c ≠ ℓ₁) + P_D(c ≠ ℓ₀) ≥ 2 L_n`, with `2 L_n → 1 − √(a² ⟨e, Σ_D⁺ e⟩/2)`. -/
theorem chamber_classifier_error_ge {e : J → ℝ}
    (he : ∀ u ∈ dataKer hS ν D, dotJ (u : J → ℝ) e = 0) {a : ℝ} (ha : 0 < a) :
    ∃ L : ℕ → ℝ,
      Tendsto (fun n ↦ 2 * L n) atTop (𝓝 (1 - √(a ^ 2 *
        dataBilin hS ν D (dataDualSing hS ν D he) (dataDualSing hS ν D he) / 2))) ∧
      ∀ n : ℕ, ∀ c : (Fin n → X) → Bool, Measurable c → ∀ ℓ₀ ℓ₁ : Bool, ℓ₀ ≠ ℓ₁ →
        2 * L n ≤ (Measure.pi fun _ : Fin n ↦ D.tilted fun x ↦ (a / Real.sqrt n) * (hE he) x).real
            {z | c z ≠ ℓ₁} + (Measure.pi fun _ : Fin n ↦ D).real {z | c z ≠ ℓ₀} := by
  obtain ⟨L, hL, hbound⟩ := chamber_resolution_floor hS ν D he ha
  refine ⟨L, ?_, fun n c hc ℓ₀ ℓ₁ hℓ ↦ ?_⟩
  · have := hL.const_mul 2
    rwa [show 2 * ((1 - √(a ^ 2 * dataBilin hS ν D (dataDualSing hS ν D he)
      (dataDualSing hS ν D he) / 2)) / 2) = 1 - √(a ^ 2 * dataBilin hS ν D
      (dataDualSing hS ν D he) (dataDualSing hS ν D he) / 2) by ring] at this
  · have hDs : IsProbabilityMeasure (D.tilted fun x ↦ (a / Real.sqrt n) * (hE he) x) :=
      isProbabilityMeasure_tilted (integrable_exp_of_bdd D ((bdd_dirLoss hS _).const_mul _))
    have hmeas : MeasurableSet {z : Fin n → X | c z = ℓ₀} := hc (measurableSet_singleton ℓ₀)
    -- the test "declare the label of `D`"
    have h := hbound n ({z | c z = ℓ₀}.indicator 1) (measurable_const.indicator hmeas)
      (fun z ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) z)
      (fun z ↦ Set.indicator_le_self' (fun _ _ ↦ zero_le_one) z)
    have e1 : ∫ z, ({z | c z = ℓ₀}.indicator 1 : (Fin n → X) → ℝ) z
        ∂(Measure.pi fun _ : Fin n ↦ D.tilted fun x ↦ (a / Real.sqrt n) * (hE he) x) =
        (Measure.pi fun _ : Fin n ↦ D.tilted fun x ↦ (a / Real.sqrt n) * (hE he) x).real
          {z | c z ≠ ℓ₁} := by
      rw [integral_indicator_one hmeas]
      congr 1
      ext z
      simp only [Set.mem_ofPred_eq]
      cases hcz : c z <;> cases ℓ₀ <;> cases ℓ₁ <;> simp_all
    have e2 : ∫ z, (1 - ({z | c z = ℓ₀}.indicator 1 : (Fin n → X) → ℝ) z)
        ∂(Measure.pi fun _ : Fin n ↦ D) = (Measure.pi fun _ : Fin n ↦ D).real {z | c z ≠ ℓ₀} := by
      have hc' : {z : Fin n → X | c z ≠ ℓ₀} = {z | c z = ℓ₀}ᶜ := by
        ext z
        simp
      rw [integral_sub (integrable_const 1) ((integrable_const 1).indicator hmeas),
        integral_const, integral_indicator_one hmeas, probReal_univ, smul_eq_mul, mul_one, hc',
        measureReal_compl hmeas, probReal_univ]
    rw [e1, e2] at h
    linarith
end Classifier

end Laplace.Multi
