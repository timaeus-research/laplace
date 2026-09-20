/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AbelianTransferLog

/-!
# The Abelian transfer on a cube

The transfer theorems of `AbelianTransfer` and `AbelianTransferLog` specialised
to Lebesgue measure on a compact box `Icc a b ⊆ ℝ^ι`, with the sublevel
hypotheses stated directly on the volumes `vol{w ∈ Icc a b : K w ≤ ε}` and the
conclusion on `∫_{Icc a b} e^{-tK}`. This is the shape in which resolution of
singularities delivers its sublevel-volume bounds, so a future bridge to the
hironaka seabed plugs in here with no further measure theory.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- Lebesgue measure restricted to a box is finite. -/
instance (a b : ι → ℝ) : IsFiniteMeasure (volume.restrict (Icc a b)) :=
  isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne

/-- The sublevel mass of the restricted measure is the volume of the sublevel
set inside the box. -/
theorem sublevelMass_restrict_Icc {K : (ι → ℝ) → ℝ} (hK : Measurable K) (a b : ι → ℝ) (ε : ℝ) :
    sublevelMass (volume.restrict (Icc a b)) K ε = volume.real {w | w ∈ Icc a b ∧ K w ≤ ε} := by
  unfold sublevelMass
  rw [measureReal_restrict_apply (measurableSet_le hK measurable_const)]
  congr 1
  ext w
  simp only [mem_inter_iff, mem_ofPred_eq]
  exact and_comm

/-- The Boltzmann mass of the restricted measure is the set integral. -/
theorem boltzmannMass_restrict_Icc (K : (ι → ℝ) → ℝ) (a b : ι → ℝ) (t : ℝ) :
    boltzmannMass (volume.restrict (Icc a b)) K t = ∫ w in Icc a b, Real.exp (-(t * K w)) := rfl

/-- **Power-case transfer on a box.** -/
theorem integral_Icc_exp_power_transfer {K : (ι → ℝ) → ℝ} (hK : Measurable K)
    (hK0 : ∀ w, 0 ≤ K w) (a b : ι → ℝ)
    {lam ε₀ c₁ c₂ : ℝ} (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      c₁ * ε ^ lam ≤ volume.real {w | w ∈ Icc a b ∧ K w ≤ ε})
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      volume.real {w | w ∈ Icc a b ∧ K w ≤ ε} ≤ c₂ * ε ^ lam) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ t : ℝ in atTop,
      C₁ * t ^ (-lam) ≤ ∫ w in Icc a b, Real.exp (-(t * K w)) ∧
      (∫ w in Icc a b, Real.exp (-(t * K w))) ≤ C₂ * t ^ (-lam) := by
  have h := boltzmannMass_power_transfer (volume.restrict (Icc a b)) K hK hK0 hlam hε₀ hc₁ hc₂
    (fun ε hε hεle ↦ by rw [sublevelMass_restrict_Icc hK]; exact hlower ε hε hεle)
    (fun ε hε hεle ↦ by rw [sublevelMass_restrict_Icc hK]; exact hupper ε hε hεle)
  simpa only [boltzmannMass_restrict_Icc] using h

/-- **Log-multiplicity transfer on a box.** -/
theorem integral_Icc_exp_log_transfer {K : (ι → ℝ) → ℝ} (hK : Measurable K)
    (hK0 : ∀ w, 0 ≤ K w) (a b : ι → ℝ) {lam ε₀ c₁ c₂ : ℝ} (k : ℕ)
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      c₁ * ε ^ lam * (Real.log ε⁻¹) ^ k ≤ volume.real {w | w ∈ Icc a b ∧ K w ≤ ε})
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      volume.real {w | w ∈ Icc a b ∧ K w ≤ ε} ≤ c₂ * ε ^ lam * (Real.log ε⁻¹) ^ k) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ t : ℝ in atTop,
      C₁ * t ^ (-lam) * (Real.log t) ^ k ≤ ∫ w in Icc a b, Real.exp (-(t * K w)) ∧
      (∫ w in Icc a b, Real.exp (-(t * K w))) ≤ C₂ * t ^ (-lam) * (Real.log t) ^ k := by
  have h := boltzmannMass_log_transfer (volume.restrict (Icc a b)) K hK hK0 k hlam hε₀ hε₀1 hc₁
    hc₂ (fun ε hε hεle ↦ by rw [sublevelMass_restrict_Icc hK]; exact hlower ε hε hεle)
    (fun ε hε hεle ↦ by rw [sublevelMass_restrict_Icc hK]; exact hupper ε hε hεle)
  simpa only [boltzmannMass_restrict_Icc] using h

end Laplace
