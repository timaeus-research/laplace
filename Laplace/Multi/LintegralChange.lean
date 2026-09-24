/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# Lebesgue-integral changes of variables

Two bookkeeping lemmas for the active-truth assembly in `lintegral` form: the Fubini split of a
coordinate sum `ι₁ ⊕ ι₂` (`lintegral_sum_split`) and the affine change of variables
`∫⁻ y, G(My + b) = |det M|⁻¹ ∫⁻ G` on `Fin n → ℝ` (`lintegral_comp_mulVec_add`), both without
integrability side conditions.
-/

open MeasureTheory Set
open scoped ENNReal Matrix

namespace Laplace.Multi

/-- Fubini for a coordinate sum: `∫⁻ z, F z = ∫⁻ x, ∫⁻ y, F (Sum.elim x y)`. -/
theorem lintegral_sum_split {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {F : (ι₁ ⊕ ι₂ → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z = ∫⁻ x : ι₁ → ℝ, ∫⁻ y : ι₂ → ℝ, F (Sum.elim x y) := by
  have hmp : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ ↦ ℝ))
      volume volume := volume_measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ ↦ ℝ)
  rw [← hmp.symm.lintegral_comp_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ ↦ ℝ)).symm.measurableEmbedding,
    Measure.volume_eq_prod]
  have hmeas : Measurable fun a : (ι₁ → ℝ) × (ι₂ → ℝ) ↦
      F ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ ↦ ℝ)).symm a) :=
    hF.comp (MeasurableEquiv.measurable _)
  rw [lintegral_prod _ hmeas.aemeasurable]
  rfl

/-- The affine change of variables `y ↦ My + b`, `det M ≠ 0`:
`∫⁻ y, G(My + b) = |det M|⁻¹ ∫⁻ u, G u`. -/
theorem lintegral_comp_mulVec_add {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0)
    (b : Fin n → ℝ) {G : (Fin n → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G (M *ᵥ y + b) = ENNReal.ofReal |M.det|⁻¹ * ∫⁻ u, G u := by
  have hlin : LinearMap.det (Matrix.toLin' M) ≠ 0 := by rwa [LinearMap.det_toLin']
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hlin
  rw [LinearMap.det_toLin'] at hmap
  have hmeas : Measurable fun y : Fin n → ℝ ↦ M *ᵥ y :=
    (Matrix.toLin' M).toContinuousLinearMap.continuous.measurable
  have hG' : Measurable fun u : Fin n → ℝ ↦ G (u + b) := hG.comp (measurable_id.add_const b)
  have h1 : ∫⁻ y, G (M *ᵥ y + b) = ∫⁻ u, G (u + b) ∂(Measure.map (fun y ↦ M *ᵥ y) volume) := by
    rw [lintegral_map hG' hmeas]
  have h2 : (Measure.map (Matrix.toLin' M) volume : Measure (Fin n → ℝ)) =
      Measure.map (fun y ↦ M *ᵥ y) volume := rfl
  rw [h1, ← h2, hmap, lintegral_smul_measure, lintegral_add_right_eq_self, abs_inv, smul_eq_mul]

end Laplace.Multi
