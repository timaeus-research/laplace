/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.HeadlineAmplitude

/-!
# Peeling the first coordinate of a Bochner box integral

The `ℝ≥0∞` peel `lintegral_unitBox_succ` (unit 174) has a Bochner counterpart for an arbitrary
one-dimensional measurable factor `S` and an integrable integrand:

  `∫ x in S^{d+1}, F x = ∫ a in S, ∫ b in S^d, F (Fin.cons a b)`

(`integral_pi_box_succ`), via `measurePreserving_piFinSuccAbove` at `0` and Fubini. The symmetric
box `[-1,1]^d` (interior normal coordinates) and the unit box are both instances.
-/

open MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- The box `S^d` in `Fin d → ℝ`. -/
def piBox (d : ℕ) (S : Set ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => S

theorem measurableSet_piBox (d : ℕ) (S : Set ℝ) (hS : MeasurableSet S) :
    MeasurableSet (piBox d S) :=
  MeasurableSet.univ_pi fun _ => hS

theorem restrict_piBox (d : ℕ) (S : Set ℝ) :
    (volume : Measure (Fin d → ℝ)).restrict (piBox d S) =
      Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict S := by
  rw [piBox, volume_pi, Measure.restrict_pi_pi]

theorem piBox_zero_eq_univ (S : Set ℝ) : piBox 0 S = univ := by
  ext x
  simp [piBox]

/-- Box integrals over `S^0` evaluate the integrand at the unique point. -/
theorem integral_piBox_zero (S : Set ℝ) (F : (Fin 0 → ℝ) → ℝ) :
    ∫ x in piBox 0 S, F x = F isEmptyElim := by
  rw [restrict_piBox, Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℝ).restrict S),
    integral_dirac]

/-- **Bochner peel of the first coordinate**. -/
theorem integral_pi_box_succ (d : ℕ) (S : Set ℝ) (F : (Fin (d + 1) → ℝ) → ℝ)
    (hF : IntegrableOn F (piBox (d + 1) S)) :
    ∫ x in piBox (d + 1) S, F x = ∫ a in S, ∫ b in piBox d S, F (Fin.cons a b) := by
  set μ : Fin (d + 1) → Measure ℝ := fun _ => (volume : Measure ℝ).restrict S with hμ
  have hmp := measurePreserving_piFinSuccAbove μ 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
  have hsymm : ∀ y : ℝ × (Fin d → ℝ), e.symm y = Fin.cons y.1 y.2 := by
    intro y
    change Fin.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 y.1 y.2 = _
    exact Fin.insertNth_zero' y.1 y.2
  unfold IntegrableOn at hF
  rw [restrict_piBox] at hF ⊢
  rw [← (hmp.symm e).integral_comp e.symm.measurableEmbedding F]
  change ∫ y, F (e.symm y) ∂((volume : Measure ℝ).restrict S).prod
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict S) = _
  have hint : Integrable (fun y => F (e.symm y)) (((volume : Measure ℝ).restrict S).prod
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict S)) :=
    ((hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hF
  rw [integral_prod _ hint, ← restrict_piBox]
  simp only [hsymm]

end Laplace.Grammar
