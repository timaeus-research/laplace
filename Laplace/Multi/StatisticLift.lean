/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ProjectionPythagoras

/-!
# The statistic lift and the residual-information split

For a statistic `S : X → Y` and laws `D ≪ ν`, the **statistic lift** of `D` is
`D↑ = ν.withDensity (d(S_*D)/d(S_*ν) ∘ S)`: the law with the same `S`-distribution as `D` whose
density with respect to `ν` is a function of `S`. It satisfies (`map_statisticLift`,
`absolutelyContinuous_statisticLift`): `S_*D↑ = S_*D`, `D↑ ≪ ν`, `D ≪ D↑`.

* **The base split** (`klDiv_eq_klDiv_statisticLift_add_map`): for `KL(D‖ν) < ∞`,
  `KL(D ‖ ν) = KL(D ‖ D↑) + KL(S_*D ‖ S_*ν)`.
* **The lift carries exactly the information visible through `S`**
  (`klDiv_statisticLift_eq_map`): `KL(D↑ ‖ ν) = KL(S_*D ‖ S_*ν)`, with no finiteness hypothesis.
* **The lift is the least informative realisation of the statistic law**
  (`klDiv_statisticLift_le`, `eq_statisticLift_of_klDiv_eq`): among finite-information laws `D'`
  with `S_*D' = S_*D`, `KL(D' ‖ ν) ≥ KL(D↑ ‖ ν)`, with equality only for `D' = D↑`.
* **The residual split for bounded tilts** (`klDiv_tilted_comp_eq_statisticLift_add_map`): for
  `P = ν.tilted (f ∘ S)` with `f` bounded,
  `KL(D ‖ P) = KL(D ‖ D↑) + KL(S_*D ‖ S_*P)`.

Applied to the response projection `P = Π_ν(M_D)` (a tilt by a function of `S`), the invisible
information `KL(D ‖ Π_ν(M_D))` splits into the **fibre part** `KL(D ‖ D↑)`, the information in `D`
that is not a function of `S` at all (independent of the tilt), and the **marginal part**
`KL(S_*D ‖ S_*Π_ν(M_D))`, the information in the distribution of `S` beyond its mean. Equal means
of `S` are much weaker than equal distributions of `S`, so the marginal part is not zero in general.
No conditional kernels or standard-Borel hypotheses are needed.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Lift

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν D : Measure X) (S : X → Y)
  [IsFiniteMeasure ν] [IsFiniteMeasure D]

/-- **The statistic lift** `D↑ = ν.withDensity (d(S_*D)/d(S_*ν) ∘ S)`. -/
noncomputable def statisticLift : Measure X :=
  ν.withDensity fun x ↦ (D.map S).rnDeriv (ν.map S) (S x)

variable (hS : Measurable S)
include hS

omit [IsFiniteMeasure ν] [IsFiniteMeasure D] in
theorem measurable_liftDensity : Measurable fun x ↦ (D.map S).rnDeriv (ν.map S) (S x) :=
  (Measure.measurable_rnDeriv _ _).comp hS

omit D [IsFiniteMeasure ν] in
/-- Pushing a density that is a function of `S` along `S`. -/
theorem map_withDensity_comp {g : Y → ℝ≥0∞} (hg : Measurable g) :
    (ν.withDensity fun x ↦ g (S x)).map S = (ν.map S).withDensity g := by
  ext B hB
  rw [Measure.map_apply hS hB, withDensity_apply _ (hS hB), withDensity_apply _ hB,
    setLIntegral_map hB hg hS]

variable (hD : D ≪ ν)
include hD

omit [IsFiniteMeasure ν] [IsFiniteMeasure D] in
theorem map_absolutelyContinuous : D.map S ≪ ν.map S := by
  refine Measure.AbsolutelyContinuous.mk fun B hB h0 ↦ ?_
  rw [Measure.map_apply hS hB] at h0 ⊢
  exact hD h0

/-- `S_* D↑ = S_* D`. -/
theorem map_statisticLift : (statisticLift ν D S).map S = D.map S := by
  unfold statisticLift
  rw [map_withDensity_comp ν S hS (Measure.measurable_rnDeriv _ _),
    Measure.withDensity_rnDeriv_eq _ _ (map_absolutelyContinuous ν D S hS hD)]

theorem isProbabilityMeasure_statisticLift [IsProbabilityMeasure D] :
    IsProbabilityMeasure (statisticLift ν D S) := by
  constructor
  have h : (statisticLift ν D S).map S univ = D.map S univ := by
    rw [map_statisticLift ν D S hS hD]
  rw [Measure.map_apply hS MeasurableSet.univ, Measure.map_apply hS MeasurableSet.univ,
    Set.preimage_univ] at h
  rw [h]
  exact measure_univ

omit hS hD [IsFiniteMeasure ν] [IsFiniteMeasure D] in
theorem statisticLift_absolutelyContinuous : statisticLift ν D S ≪ ν :=
  withDensity_absolutelyContinuous _ _

/-- The lift density vanishes only on a `D`-null set. -/
theorem measure_liftDensity_eq_zero : D {x | (D.map S).rnDeriv (ν.map S) (S x) = 0} = 0 := by
  have hB : MeasurableSet {y | (D.map S).rnDeriv (ν.map S) y = 0} :=
    measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const
  have e : {x | (D.map S).rnDeriv (ν.map S) (S x) = 0} =
      S ⁻¹' {y | (D.map S).rnDeriv (ν.map S) y = 0} := rfl
  have hlam := Measure.withDensity_rnDeriv_eq _ _ (map_absolutelyContinuous ν D S hS hD)
  have key : ((ν.map S).withDensity ((D.map S).rnDeriv (ν.map S)))
      {y | (D.map S).rnDeriv (ν.map S) y = 0} = 0 := by
    rw [withDensity_apply _ hB, setLIntegral_congr_fun (g := fun _ ↦ 0) hB (fun y hy ↦ hy)]
    exact lintegral_zero
  rw [hlam] at key
  rw [e, ← Measure.map_apply hS hB]
  exact key

/-- `D ≪ D↑`. -/
theorem absolutelyContinuous_statisticLift : D ≪ statisticLift ν D S := by
  refine Measure.AbsolutelyContinuous.mk fun A hA h0 ↦ ?_
  unfold statisticLift at h0
  rw [withDensity_apply_eq_zero (measurable_liftDensity ν D S hS)] at h0
  have h1 : D ({x | (D.map S).rnDeriv (ν.map S) (S x) ≠ 0} ∩ A) = 0 := hD h0
  have h2 := measure_liftDensity_eq_zero ν D S hS hD
  refine le_antisymm ?_ zero_le
  calc D A ≤ D (({x | (D.map S).rnDeriv (ν.map S) (S x) ≠ 0} ∩ A) ∪
        {x | (D.map S).rnDeriv (ν.map S) (S x) = 0}) := by
        refine measure_mono fun x hx ↦ ?_
        by_cases h : (D.map S).rnDeriv (ν.map S) (S x) = 0
        · exact Or.inr h
        · exact Or.inl ⟨h, hx⟩
    _ ≤ D ({x | (D.map S).rnDeriv (ν.map S) (S x) ≠ 0} ∩ A) +
        D {x | (D.map S).rnDeriv (ν.map S) (S x) = 0} := measure_union_le _ _
    _ = 0 := by rw [h1, h2, add_zero]

end Lift

section Split

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν D : Measure X)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : X → Y) (hS : Measurable S) (hD : D ≪ ν)
include hS hD

/-- **The lift carries exactly the information visible through `S`**:
`KL(D↑ ‖ ν) = KL(S_*D ‖ S_*ν)`. -/
theorem klDiv_statisticLift_eq_map :
    klDiv (statisticLift ν D S) ν = klDiv (D.map S) (ν.map S) := by
  have hPlam : IsProbabilityMeasure (D.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hPmu : IsProbabilityMeasure (ν.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hPL := isProbabilityMeasure_statisticLift ν D S hS hD
  rw [klDiv_eq_lintegral_klFun_of_ac (statisticLift_absolutelyContinuous ν D S),
    klDiv_eq_lintegral_klFun_of_ac (map_absolutelyContinuous ν D S hS hD)]
  have hm : Measurable fun y ↦ ENNReal.ofReal (klFun ((D.map S).rnDeriv (ν.map S) y).toReal) :=
    (by fun_prop : Measurable fun y ↦ klFun ((D.map S).rnDeriv (ν.map S) y).toReal).ennreal_ofReal
  rw [lintegral_map hm hS]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity ν (measurable_liftDensity ν D S hS)] with x hx
  unfold statisticLift
  rw [hx]

/-- **The base entropy split**: `KL(D ‖ ν) = KL(D ‖ D↑) + KL(S_*D ‖ S_*ν)` for `KL(D ‖ ν) < ∞`. -/
theorem klDiv_eq_klDiv_statisticLift_add_map (hfin : klDiv D ν ≠ ⊤) :
    klDiv D ν = klDiv D (statisticLift ν D S) + klDiv (D.map S) (ν.map S) := by
  obtain ⟨-, hint⟩ := klDiv_ne_top_iff.1 hfin
  have hlm : D.map S ≪ ν.map S := map_absolutelyContinuous ν D S hS hD
  have hmapfin : klDiv (D.map S) (ν.map S) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (klDiv_map_le (μ := D) (ν := ν) hS)
  have hintY : Integrable (llr (D.map S) (ν.map S)) (D.map S) := (klDiv_ne_top_iff.1 hmapfin).2
  have hPlam : IsProbabilityMeasure (D.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hPmu : IsProbabilityMeasure (ν.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hPL := isProbabilityMeasure_statisticLift ν D S hS hD
  have hDL := absolutelyContinuous_statisticLift ν D S hS hD
  have hr_comp_int : Integrable (fun x ↦ llr (D.map S) (ν.map S) (S x)) D :=
    (integrable_map_measure hintY.aestronglyMeasurable hS.aemeasurable).1 hintY
  -- the log-likelihood ratio of the lift, `D`-almost everywhere
  have hae : llr D (statisticLift ν D S) =ᵐ[D]
      fun x ↦ llr D ν x - llr (D.map S) (ν.map S) (S x) := by
    have hchain := Measure.rnDeriv_mul_rnDeriv (κ := ν) hDL
    have hdens : (statisticLift ν D S).rnDeriv ν =ᵐ[ν]
        fun x ↦ (D.map S).rnDeriv (ν.map S) (S x) :=
      Measure.rnDeriv_withDensity ν (measurable_liftDensity ν D S hS)
    have hpos := Measure.rnDeriv_pos hDL
    have hr_ne : ∀ᵐ x ∂D, (D.map S).rnDeriv (ν.map S) (S x) ≠ 0 := by
      rw [ae_iff]
      simpa using measure_liftDensity_eq_zero ν D S hS hD
    have hr_top : ∀ᵐ x ∂D, (D.map S).rnDeriv (ν.map S) (S x) ≠ ⊤ :=
      hD.ae_le (ae_of_ae_map hS.aemeasurable (Measure.rnDeriv_ne_top (D.map S) (ν.map S)))
    have hLtop := hDL.ae_le (Measure.rnDeriv_ne_top D (statisticLift ν D S))
    filter_upwards [hD.ae_le hchain, hD.ae_le hdens, hpos, hr_ne, hr_top, hLtop]
      with x hc hd hp hr0 hrt hlt
    rw [Pi.mul_apply, hd] at hc
    simp only [llr]
    rw [← hc, ENNReal.toReal_mul,
      Real.log_mul (ENNReal.toReal_pos hp.ne' hlt).ne' (ENNReal.toReal_pos hr0 hrt).ne']
    ring
  have hint' : Integrable (llr D (statisticLift ν D S)) D :=
    (hint.sub hr_comp_int).congr hae.symm
  -- the three real quantities
  have ha : (klDiv D (statisticLift ν D S)).toReal = ∫ x, llr D (statisticLift ν D S) x ∂D := by
    rw [toReal_klDiv hDL hint', probReal_univ, probReal_univ, add_sub_cancel_right]
  have hb : (klDiv (D.map S) (ν.map S)).toReal = ∫ y, llr (D.map S) (ν.map S) y ∂D.map S := by
    rw [toReal_klDiv hlm hintY, probReal_univ, probReal_univ, add_sub_cancel_right]
  have hc : (klDiv D ν).toReal = ∫ x, llr D ν x ∂D := by
    rw [toReal_klDiv hD hint, probReal_univ, probReal_univ, add_sub_cancel_right]
  have hsum : ∫ x, llr D ν x ∂D = (∫ x, llr D (statisticLift ν D S) x ∂D) +
      ∫ y, llr (D.map S) (ν.map S) y ∂D.map S := by
    rw [integral_congr_ae hae, integral_sub hint hr_comp_int,
      integral_map hS.aemeasurable hintY.aestronglyMeasurable]
    ring
  have hfin' : klDiv D (statisticLift ν D S) ≠ ⊤ := by
    rw [klDiv_of_ac_of_integrable hDL hint']
    exact ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hfin', ← ENNReal.ofReal_toReal hmapfin,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg, hc, ha, hb, hsum]

/-- **The lift is the least informative realisation of the statistic law**: every finite-information
law with the same `S`-distribution carries at least the information of the lift. -/
theorem klDiv_statisticLift_le (D' : Measure X) [IsProbabilityMeasure D'] (hD' : D' ≪ ν)
    (hmap : D'.map S = D.map S) (hfin : klDiv D' ν ≠ ⊤) :
    klDiv (statisticLift ν D S) ν ≤ klDiv D' ν := by
  have hlift : statisticLift ν D' S = statisticLift ν D S := by
    unfold statisticLift
    rw [hmap]
  rw [klDiv_statisticLift_eq_map ν D S hS hD,
    klDiv_eq_klDiv_statisticLift_add_map ν D' S hS hD' hfin, hmap]
  exact le_add_self

/-- **Uniqueness**: a finite-information law with the same `S`-distribution and the same information
as the lift is the lift. -/
theorem eq_statisticLift_of_klDiv_eq (D' : Measure X) [IsProbabilityMeasure D'] (hD' : D' ≪ ν)
    (hmap : D'.map S = D.map S) (hfin : klDiv D' ν ≠ ⊤)
    (heq : klDiv D' ν = klDiv (statisticLift ν D S) ν) : D' = statisticLift ν D S := by
  have hlift : statisticLift ν D' S = statisticLift ν D S := by
    unfold statisticLift
    rw [hmap]
  have hPL := isProbabilityMeasure_statisticLift ν D S hS hD
  have h := klDiv_eq_klDiv_statisticLift_add_map ν D' S hS hD' hfin
  rw [hlift, hmap, heq, klDiv_statisticLift_eq_map ν D S hS hD] at h
  have hmapfin : klDiv (D.map S) (ν.map S) ≠ ⊤ := by
    rw [← klDiv_statisticLift_eq_map ν D S hS hD, ← heq]
    exact hfin
  have h0 : klDiv D' (statisticLift ν D S) = 0 := by
    refine (ENNReal.add_left_inj hmapfin).1 ?_
    rw [zero_add]
    exact h.symm
  exact klDiv_eq_zero_iff.1 h0

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure D] hD in
/-- Pushing a bounded tilt by a function of `S` along `S`. -/
theorem map_tilted_comp {f : Y → ℝ} (hf : Bdd f) :
    (ν.tilted fun x ↦ f (S x)).map S = (ν.map S).tilted f := by
  have hZ : ∫ x, Real.exp (f (S x)) ∂ν = ∫ y, Real.exp (f y) ∂ν.map S :=
    (integral_map hS.aemeasurable (hf.1.exp.aestronglyMeasurable)).symm
  have hg : Measurable fun y ↦ ENNReal.ofReal (Real.exp (f y) / ∫ y, Real.exp (f y) ∂ν.map S) :=
    (hf.1.exp.div_const _).ennreal_ofReal
  have h := map_withDensity_comp ν S hS hg
  unfold Measure.tilted
  rw [hZ]
  exact h

/-- **The residual-information split for bounded tilts**: for `P = ν.tilted (f ∘ S)` with `f`
bounded and `KL(D ‖ ν) < ∞`, `KL(D ‖ P) = KL(D ‖ D↑) + KL(S_*D ‖ S_*P)`. -/
theorem klDiv_tilted_comp_eq_statisticLift_add_map {f : Y → ℝ} (hf : Bdd f)
    (hfin : klDiv D ν ≠ ⊤) :
    klDiv D (ν.tilted fun x ↦ f (S x)) =
      klDiv D (statisticLift ν D S) + klDiv (D.map S) ((ν.tilted fun x ↦ f (S x)).map S) := by
  obtain ⟨hfm, L, hL⟩ := hf
  have hfS : Bdd fun x ↦ f (S x) := ⟨hfm.comp hS, L, fun x ↦ hL (S x)⟩
  have hlm : D.map S ≪ ν.map S := map_absolutelyContinuous ν D S hS hD
  have hmapfin : klDiv (D.map S) (ν.map S) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (klDiv_map_le (μ := D) (ν := ν) hS)
  have hPlam : IsProbabilityMeasure (D.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hPmu : IsProbabilityMeasure (ν.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hPL := isProbabilityMeasure_statisticLift ν D S hS hD
  have hbase := klDiv_eq_klDiv_statisticLift_add_map ν D S hS hD hfin
  have hfinL : klDiv D (statisticLift ν D S) ≠ ⊤ := by
    intro h
    rw [h, top_add] at hbase
    exact hfin hbase
  rw [map_tilted_comp ν S hS ⟨hfm, L, hL⟩, klDiv_tilted_right_eq ν D hD hfin hfS,
    klDiv_tilted_right_eq (ν.map S) (D.map S) hlm hmapfin ⟨hfm, L, hL⟩,
    ← ENNReal.ofReal_toReal hfinL, ← ENNReal.ofReal_add ENNReal.toReal_nonneg ?_]
  · congr 1
    have hbase' : (klDiv D ν).toReal =
        (klDiv D (statisticLift ν D S)).toReal + (klDiv (D.map S) (ν.map S)).toReal := by
      rw [hbase, ENNReal.toReal_add hfinL hmapfin]
    rw [hbase', integral_map hS.aemeasurable hfm.aestronglyMeasurable,
      integral_map hS.aemeasurable hfm.exp.aestronglyMeasurable]
    ring
  · rw [← toReal_klDiv_tilted_right (ν.map S) (D.map S) hlm hmapfin ⟨hfm, L, hL⟩]
    exact ENNReal.toReal_nonneg

end Split

end Laplace.Multi
