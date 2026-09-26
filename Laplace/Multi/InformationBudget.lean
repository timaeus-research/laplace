/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.VisibleBudget

/-!
# The complete information budget of the journey from the featureless law to the data

For a data law `D` of finite information `KL(D ‖ ν) < ∞`, with response `M_D = E_D S`, the three
quantities of the information decomposition are all integrated Fisher energies along the bridge
from the featureless law to the data:

* the total information, `KL(D ‖ ν) = ∫₀¹ (1 − s) 𝓕_D(s) ds` (data Fisher information of the
  mixture path, `DataFisherBudget`);
* the visible information, `𝓘(M_D) = ∫₀¹ (1 − s) κ(s) ds` (dual-Fisher energy of the canonical
  bridge, `VisibleBudget`);
* and therefore the invisible information,

  `KL(D ‖ Π(M_D)) = ∫₀¹ (1 − s) [𝓕_D(s) − κ(s)] ds`   (`klDiv_projection_eq_integral_budget`),

as a real integral of an integrable function over `Ioo 0 1`. The response atlas thus separates
the information required to move the observed responses from the information remaining within
their fibres, and gives an exact integrated curvature budget for both. The bracket is not
pointwise nonnegative in general: the two Fisher quantities live under different laws, `D_s` and
`Π(M_s)`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D]

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure D] in
/-- The data Fisher information is measurable in the bridge parameter. -/
theorem measurable_dataFisher : Measurable (dataFisher ν D) := by
  have hf : Measurable fun p : ℝ × X ↦ (D.rnDeriv ν p.2).toReal :=
    (Measure.measurable_rnDeriv D ν).ennreal_toReal.comp measurable_snd
  have hs : Measurable fun p : ℝ × X ↦ p.1 := measurable_fst
  have h : Measurable fun p : ℝ × X ↦ ENNReal.ofReal (((D.rnDeriv ν p.2).toReal - 1) ^ 2 /
      (1 - p.1 + p.1 * (D.rnDeriv ν p.2).toReal)) :=
    Measurable.ennreal_ofReal (by fun_prop)
  exact h.lintegral_prod_right'

include hS

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure D] in
/-- The weighted data Fisher information is measurable. -/
theorem measurable_dataFisher_weighted :
    Measurable fun s : ℝ ↦ ENNReal.ofReal (1 - s) * dataFisher ν D s :=
  (measurable_const.sub measurable_id).ennreal_ofReal.mul (measurable_dataFisher ν D)

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The total information in Lebesgue form over the open bridge. -/
theorem klDiv_eq_lintegral_dataFisher_Ioo (hDkl : klDiv D ν ≠ ⊤) :
    klDiv D ν = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - s) * dataFisher ν D s := by
  have hDν : D ≪ ν := (klDiv_ne_top_iff.1 hDkl).1
  rw [klDiv_eq_lintegral_dataFisher ν D hDν, setLIntegral_congr Ioo_ae_eq_Ioc]

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The data Fisher information is finite for almost every bridge parameter. -/
theorem dataFisher_ae_ne_top (hDkl : klDiv D ν ≠ ⊤) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1), dataFisher ν D s ≠ ⊤ := by
  have hfinite : ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - s) * dataFisher ν D s ≠ ⊤ := by
    rw [← klDiv_eq_lintegral_dataFisher_Ioo ν D hDkl]
    exact hDkl
  have h := ae_lt_top' (measurable_dataFisher_weighted ν D).aemeasurable hfinite
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with s hs hs1
  have h0 : ENNReal.ofReal (1 - s) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith [hs1.2]
  rw [ENNReal.mul_lt_top_iff] at hs
  rcases hs with ⟨-, h2⟩ | h | h
  · exact h2.ne
  · exact absurd h h0
  · rw [h]
    exact ENNReal.zero_ne_top

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- **The total information as a real integral over the bridge**, for a data law of finite
information: `KL(D ‖ ν) = ∫₀¹ (1 − s) 𝓕_D(s) ds`. -/
theorem toReal_klDiv_eq_integral_dataFisher (hDkl : klDiv D ν ≠ ⊤) :
    (klDiv D ν).toReal = ∫ s in Ioo (0 : ℝ) 1, (1 - s) * (dataFisher ν D s).toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun s ↦ (1 - s) * (dataFisher ν D s).toReal := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    exact mul_nonneg (by linarith [hs.2]) ENNReal.toReal_nonneg
  have hsm : AEStronglyMeasurable (fun s ↦ (1 - s) * (dataFisher ν D s).toReal)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((measurable_const.sub measurable_id).mul
      (measurable_dataFisher ν D).ennreal_toReal).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn hsm, klDiv_eq_lintegral_dataFisher_Ioo ν D hDkl]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [dataFisher_ae_ne_top ν D hDkl, ae_restrict_mem measurableSet_Ioo] with s hs hs1
  rw [ENNReal.ofReal_mul (by linarith [hs1.2]), ENNReal.ofReal_toReal hs]

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The weighted data Fisher information is integrable over the bridge. -/
theorem integrableOn_dataFisher_weighted (hDkl : klDiv D ν ≠ ⊤) :
    IntegrableOn (fun s ↦ (1 - s) * (dataFisher ν D s).toReal) (Ioo (0 : ℝ) 1) := by
  have hfinite : ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - s) * dataFisher ν D s ≠ ⊤ := by
    rw [← klDiv_eq_lintegral_dataFisher_Ioo ν D hDkl]
    exact hDkl
  have h := integrable_toReal_of_lintegral_ne_top
    (measurable_dataFisher_weighted ν D).aemeasurable hfinite
  refine h.congr ?_
  filter_upwards [dataFisher_ae_ne_top ν D hDkl, ae_restrict_mem measurableSet_Ioo] with s hs hs1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [hs1.2])]

/-- **The complete information budget**: for a data law of finite information,
`KL(D ‖ Π(M_D)) = ∫₀¹ (1 − s) [𝓕_D(s) − κ(s)] ds` — the invisible information is the integrated
difference between the data Fisher information of the mixture path and the dual-Fisher energy of
the canonical bridge. -/
theorem klDiv_projection_eq_integral_budget (hDkl : klDiv D ν ≠ ⊤)
    (hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤) :
    (klDiv D (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D))).toReal =
      ∫ s in Ioo (0 : ℝ) 1,
        ((1 - s) * (dataFisher ν D s).toReal - (1 - s) * atlasCurv hS ν hfin s) := by
  have hdec := information_decomposition hS ν D hfin
  have hDP : klDiv D (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)) ≠ ⊤ := by
    intro h
    rw [h, add_top] at hdec
    exact hDkl hdec
  have h1 : (klDiv D (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D))).toReal =
      (klDiv D ν).toReal - (genRate ν S (fun i ↦ ∫ x, S i x ∂D)).toReal := by
    rw [hdec, ENNReal.toReal_add hfin hDP]
    ring
  rw [h1, toReal_klDiv_eq_integral_dataFisher ν D hDkl,
    genRate_toReal_eq_integral_atlasCurv hS ν hfin,
    integral_sub (integrableOn_dataFisher_weighted ν D hDkl)
      (integrableOn_atlasCurv_weighted hS ν hfin)]

end Laplace.Multi
