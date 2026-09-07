/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.ProductDensity
import Laplace.Grammar.WeightedPowerSubstitution

/-!
# The `Fin d` monomial box bridge

Step 4 of the general-`d` equal-ratio monomial milestone. The recursive `productIntegral` of
`ProductDensity.lean` integrates one coordinate at a time; the paper writes the monomial integral
over the genuine box `(0,1]^d ⊆ ℝ^d`. This file identifies the two in the `ENNReal` setting:

* `lintegral_box_succ` peels the first coordinate of a box integral on `Fin (d+1) → ℝ`
  (`measurePreserving_piFinSuccAbove` at `0`, Tonelli, `Fin.insertNth_zero'`);
* `weightedBoxIntegral d w g = ∫_{(0,1]^d} ∏ tᵢ^{wᵢ} g(∏ tᵢ) dt` satisfies the same recursion as
  `productIntegral`, hence agrees with it for constant weights `wᵢ = λ − 1`;
* `monomialBoxIntegral d h k g = ∫_{(0,1]^d} ∏ xᵢ^{hᵢ} g(∏ xᵢ^{2kᵢ}) dx` reduces, by the
  coordinatewise substitution `tᵢ = xᵢ^{2kᵢ}` of `WeightedPowerSubstitution.lean`, to the weighted
  box integral with weights `(hᵢ+1)/(2kᵢ) − 1` and Jacobian `∏ 1/(2kᵢ)` — with **no** equal-ratio
  hypothesis.

Together with unit 172 this expresses the equal-ratio monomial box integral through the single
weighted integral `∫₀¹ z^{λ-1} (-log z)^{d-1} g(z) dz / (d-1)!`.
-/

open MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- The unit box `(0,1]^d` in `Fin d → ℝ`. -/
def unitBox (d : ℕ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Ioc (0 : ℝ) 1

theorem measurableSet_unitBox (d : ℕ) : MeasurableSet (unitBox d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem restrict_unitBox (d : ℕ) :
    (volume : Measure (Fin d → ℝ)).restrict (unitBox d) =
      Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 1) := by
  rw [unitBox, volume_pi, Measure.restrict_pi_pi]

/-- Box integrals over `(0,1]^0` evaluate the integrand at the unique point. -/
theorem lintegral_unitBox_zero (F : (Fin 0 → ℝ) → ENNReal) :
    ∫⁻ x in unitBox 0, F x = F isEmptyElim := by
  rw [restrict_unitBox, Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℝ).restrict (Ioc 0 1)),
    lintegral_dirac]

/-- **Peeling the first coordinate** of a box integral on `Fin (d+1) → ℝ`. -/
theorem lintegral_unitBox_succ (d : ℕ) (F : (Fin (d + 1) → ℝ) → ENNReal) (hF : Measurable F) :
    ∫⁻ x in unitBox (d + 1), F x =
      ∫⁻ a in Ioc (0 : ℝ) 1, ∫⁻ b in unitBox d, F (Fin.cons a b) := by
  set μ : Fin (d + 1) → Measure ℝ := fun _ => (volume : Measure ℝ).restrict (Ioc 0 1) with hμ
  have hmp := measurePreserving_piFinSuccAbove μ 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
  have hsymm : ∀ y : ℝ × (Fin d → ℝ), e.symm y = Fin.cons y.1 y.2 := by
    intro y
    change Fin.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 y.1 y.2 = _
    exact Fin.insertNth_zero' y.1 y.2
  rw [restrict_unitBox, ← (hmp.symm e).lintegral_comp_emb e.symm.measurableEmbedding F]
  change ∫⁻ y, F (e.symm y) ∂((volume : Measure ℝ).restrict (Ioc 0 1)).prod
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 1)) = _
  rw [lintegral_prod (fun y => F (e.symm y)) (hF.comp e.symm.measurable).aemeasurable,
    ← restrict_unitBox]
  simp only [hsymm]

/-- The weighted box integral `∫_{(0,1]^d} ∏ tᵢ^{wᵢ} g(∏ tᵢ) dt`. -/
noncomputable def weightedBoxIntegral (d : ℕ) (w : Fin d → ℝ) (g : ℝ → ENNReal) : ENNReal :=
  ∫⁻ t in unitBox d, (∏ i, ENNReal.ofReal (t i ^ w i)) * g (∏ i, t i)

/-- The monomial box integral `∫_{(0,1]^d} ∏ xᵢ^{hᵢ} g(∏ xᵢ^{2kᵢ}) dx`. -/
noncomputable def monomialBoxIntegral (d : ℕ) (h k : Fin d → ℕ) (g : ℝ → ENNReal) : ENNReal :=
  ∫⁻ x in unitBox d, (∏ i, ENNReal.ofReal (x i ^ h i)) * g (∏ i, x i ^ (2 * k i))

theorem weightedBoxIntegral_zero (w : Fin 0 → ℝ) (g : ℝ → ENNReal) :
    weightedBoxIntegral 0 w g = g 1 := by
  rw [weightedBoxIntegral, lintegral_unitBox_zero]
  simp

theorem monomialBoxIntegral_zero (h k : Fin 0 → ℕ) (g : ℝ → ENNReal) :
    monomialBoxIntegral 0 h k g = g 1 := by
  rw [monomialBoxIntegral, lintegral_unitBox_zero]
  simp

theorem measurable_weightedBox_integrand (d : ℕ) (w : Fin d → ℝ) (g : ℝ → ENNReal)
    (hg : Measurable g) :
    Measurable fun t : Fin d → ℝ => (∏ i, ENNReal.ofReal (t i ^ w i)) * g (∏ i, t i) :=
  (Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp ((measurable_pi_apply i).pow_const _)).mul
    (hg.comp (Finset.measurable_prod _ fun i _ => measurable_pi_apply i))

theorem measurable_monomialBox_integrand (d : ℕ) (h k : Fin d → ℕ) (g : ℝ → ENNReal)
    (hg : Measurable g) :
    Measurable fun x : Fin d → ℝ =>
      (∏ i, ENNReal.ofReal (x i ^ h i)) * g (∏ i, x i ^ (2 * k i)) :=
  (Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp ((measurable_pi_apply i).pow_const _)).mul
    (hg.comp (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _))

/-- **Recursion for the weighted box integral**: the same recursion that defines
`productIntegral`. -/
theorem weightedBoxIntegral_succ (d : ℕ) (w : Fin (d + 1) → ℝ) (g : ℝ → ENNReal)
    (hg : Measurable g) :
    weightedBoxIntegral (d + 1) w g =
      ∫⁻ a in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (a ^ w 0) * weightedBoxIntegral d (Fin.tail w) (fun z => g (a * z)) := by
  rw [weightedBoxIntegral, lintegral_unitBox_succ d _ (measurable_weightedBox_integrand (d + 1) w g hg)]
  refine setLIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
  rw [weightedBoxIntegral, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_unitBox d) fun b _ => ?_
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
  ring

/-- Constant weights `λ − 1` recover the recursive product integral. -/
theorem weightedBoxIntegral_const_eq_productIntegral (l : ℝ) :
    ∀ (d : ℕ) (g : ℝ → ENNReal), Measurable g →
      weightedBoxIntegral d (fun _ => l - 1) g = productIntegral l d g := by
  intro d
  induction d with
  | zero =>
    intro g _
    rw [weightedBoxIntegral_zero, productIntegral_zero]
  | succ d ih =>
    intro g hg
    rw [weightedBoxIntegral_succ d _ g hg, productIntegral_succ]
    refine setLIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
    exact congrArg _ (ih (fun z => g (a * z)) (hg.comp (measurable_id.const_mul a)))

/-- **Coordinatewise power substitution**: the monomial box integral is the weighted box integral
with weights `(hᵢ+1)/(2kᵢ) − 1` and Jacobian `∏ 1/(2kᵢ)` (no equal-ratio hypothesis). -/
theorem monomialBoxIntegral_eq_weighted :
    ∀ (d : ℕ) (h k : Fin d → ℕ), (∀ i, 0 < k i) → ∀ g : ℝ → ENNReal, Measurable g →
      monomialBoxIntegral d h k g =
        ENNReal.ofReal (∏ i, 1 / (2 * (k i : ℝ))) *
          weightedBoxIntegral d (fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1) g := by
  intro d
  induction d with
  | zero =>
    intro h k _ g _
    rw [monomialBoxIntegral_zero, weightedBoxIntegral_zero]
    simp
  | succ d ih =>
    intro h k hk g hg
    have hP : 0 ≤ ∏ i : Fin d, 1 / (2 * (k i.succ : ℝ)) :=
      Finset.prod_nonneg fun i _ => by positivity
    rw [monomialBoxIntegral, lintegral_unitBox_succ d _ (measurable_monomialBox_integrand (d + 1) h k g hg)]
    have hinner : ∀ a : ℝ, (∫⁻ b in unitBox d,
        (∏ i, ENNReal.ofReal ((Fin.cons a b : Fin (d + 1) → ℝ) i ^ h i)) *
          g (∏ i, (Fin.cons a b : Fin (d + 1) → ℝ) i ^ (2 * k i))) =
        ENNReal.ofReal (a ^ h 0) * (ENNReal.ofReal (∏ i : Fin d, 1 / (2 * (k i.succ : ℝ))) *
          weightedBoxIntegral d (fun i => ((h i.succ : ℝ) + 1) / (2 * (k i.succ : ℝ)) - 1)
            (fun z => g (a ^ (2 * k 0) * z))) := by
      intro a
      have hih := ih (Fin.tail h) (Fin.tail k) (fun i => hk i.succ) (fun z => g (a ^ (2 * k 0) * z))
        (hg.comp (measurable_id.const_mul _))
      simp only [Fin.tail] at hih
      rw [← hih, monomialBoxIntegral, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun (measurableSet_unitBox d) fun b _ => ?_
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      ring
    simp only [hinner]
    rw [lintegral_weighted_power_subst (h 0) (k 0) (hk 0)
      (fun t => ENNReal.ofReal (∏ i : Fin d, 1 / (2 * (k i.succ : ℝ))) *
        weightedBoxIntegral d (fun i => ((h i.succ : ℝ) + 1) / (2 * (k i.succ : ℝ)) - 1)
          (fun z => g (t * z))),
      weightedBoxIntegral_succ d _ g hg, Fin.prod_univ_succ, ENNReal.ofReal_mul (by positivity),
      mul_assoc]
    congr 1
    conv_rhs => rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    have htail : Fin.tail (fun i : Fin (d + 1) => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1) =
        fun i : Fin d => ((h i.succ : ℝ) + 1) / (2 * (k i.succ : ℝ)) - 1 := rfl
    rw [htail]
    ring

end Laplace.Grammar
