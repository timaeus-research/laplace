/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolyhedralRetraction

/-!
# Rigidity I: an extreme mean forces concentration on its statistic fibre

If a `ν`-dominated probability law has mean `e` and `e` is an **extreme point** of the moment body,
then the law is carried by the fibre `{S = e}` (`ae_statPoint_eq_of_mean_extreme`): otherwise the
law splits along a coordinate half-space into two feasible laws whose means are distinct points of
the moment body with `e` in the open segment between them. Consequences: every extreme point that
carries a feasible density is charged (`statFibre_pos_of_mean_extreme`), and feasible densities
over distinct extreme points are at `L¹`-distance exactly `2` (`norm_sub_eq_two_of_mean_extreme`).
No entropy minimisation is involved.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Split

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem faceMeasure_absolutelyContinuous_of {D : Measure X} (hD : D ≪ ν) (A : Set X) :
    faceMeasure D A ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 ↦ ?_
  rw [faceMeasure, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
    hD (measure_mono_null inter_subset_left h0), mul_zero]

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- The mean of any `ν`-dominated probability law lies in the moment body. -/
theorem mean_mem_momentBody_of_ac (D : Measure X) [IsProbabilityMeasure D] (hD : D ≪ ν) :
    (fun i ↦ ∫ x, S i x ∂D) ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S :=
  momentBody_subset_of_absolutelyContinuous hS ν hD (mean_mem_momentBody_general hS D)

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The mean splits along a set and its complement into the conditional means. -/
theorem mean_eq_split (D : Measure X) [IsProbabilityMeasure D] {A : Set X}
    (hA : MeasurableSet A) (hA0 : D A ≠ 0) (hAc : D Aᶜ ≠ 0) :
    (fun i ↦ ∫ x, S i x ∂D) =
      D.real A • (fun i ↦ ∫ x, S i x ∂faceMeasure D A) +
        D.real Aᶜ • (fun i ↦ ∫ x, S i x ∂faceMeasure D Aᶜ) := by
  have hA0' : D.real A ≠ 0 := (ENNReal.toReal_pos hA0 (measure_ne_top _ _)).ne'
  have hAc' : D.real Aᶜ ≠ 0 := (ENNReal.toReal_pos hAc (measure_ne_top _ _)).ne'
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_faceMeasure, integral_faceMeasure, mul_inv_cancel_left₀ hA0',
    mul_inv_cancel_left₀ hAc',
    integral_add_compl₀ hA.nullMeasurableSet (integrable_of_bdd_prob D (hS j))]

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **Extremality forces equal conditional means**: if the mean is an extreme point, the
conditional mean on any set of positive, non-full mass is the mean itself. -/
theorem conditional_mean_eq_of_extreme (D : Measure X) [IsProbabilityMeasure D] (hD : D ≪ ν)
    {e : J → ℝ} (he : e ∈ (momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ)
    (hmean : (fun i ↦ ∫ x, S i x ∂D) = e) {A : Set X} (hA : MeasurableSet A) (hA0 : D A ≠ 0)
    (hAc : D Aᶜ ≠ 0) : (fun i ↦ ∫ x, S i x ∂faceMeasure D A) = e := by
  have hPA := isProbabilityMeasure_faceMeasure D hA0
  have hPAc := isProbabilityMeasure_faceMeasure D hAc
  have h1 := mean_mem_momentBody_of_ac hS ν (faceMeasure D A)
    (faceMeasure_absolutelyContinuous_of ν hD A)
  have h2 := mean_mem_momentBody_of_ac hS ν (faceMeasure D Aᶜ)
    (faceMeasure_absolutelyContinuous_of ν hD Aᶜ)
  have hsum : D.real A + D.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hA, probReal_univ]
  refine ((mem_extremePoints.1 he).2 _ h1 _ h2 ⟨D.real A, D.real Aᶜ,
    ENNReal.toReal_pos hA0 (measure_ne_top _ _), ENNReal.toReal_pos hAc (measure_ne_top _ _),
    hsum, ?_⟩).1
  rw [← hmean, mean_eq_split hS D hA hA0 hAc]

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
/-- A law carried by `{e_j < S_j}` has `j`-th mean strictly above `e_j`. -/
theorem lt_integral_of_carried (D : Measure X) [IsProbabilityMeasure D] (j : J) {c : ℝ}
    (hc : D {x | c < S j x}ᶜ = 0) (hpos : D {x | c < S j x} ≠ 0) : c < ∫ x, S j x ∂D := by
  have hint : Integrable (fun x ↦ S j x - c) D := (integrable_of_bdd_prob D (hS j)).sub
    (integrable_const c)
  have hnn : 0 ≤ᵐ[D] fun x ↦ S j x - c := by
    rw [Filter.EventuallyLE, ae_iff]
    refine measure_mono_null (fun x hx ↦ ?_) hc
    simp only [Pi.zero_apply, mem_ofPred_eq, not_le] at hx
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
    linarith
  have hpos' : 0 < ∫ x, (S j x - c) ∂D := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 hpos) (measure_mono fun x hx ↦ ?_)
    simp only [mem_ofPred_eq] at hx
    simp only [Function.mem_support]
    linarith
  rw [integral_sub (integrable_of_bdd_prob D (hS j)) (integrable_const c), integral_const,
    probReal_univ, one_smul] at hpos'
  linarith

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
/-- A law carried by `{S_j < e_j}` has `j`-th mean strictly below `e_j`. -/
theorem integral_lt_of_carried (D : Measure X) [IsProbabilityMeasure D] (j : J) {c : ℝ}
    (hc : D {x | S j x < c}ᶜ = 0) (hpos : D {x | S j x < c} ≠ 0) : ∫ x, S j x ∂D < c := by
  have hint : Integrable (fun x ↦ c - S j x) D := (integrable_const c).sub
    (integrable_of_bdd_prob D (hS j))
  have hnn : 0 ≤ᵐ[D] fun x ↦ c - S j x := by
    rw [Filter.EventuallyLE, ae_iff]
    refine measure_mono_null (fun x hx ↦ ?_) hc
    simp only [Pi.zero_apply, mem_ofPred_eq, not_le] at hx
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
    linarith
  have hpos' : 0 < ∫ x, (c - S j x) ∂D := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 hpos) (measure_mono fun x hx ↦ ?_)
    simp only [mem_ofPred_eq] at hx
    simp only [Function.mem_support]
    linarith
  rw [integral_sub (integrable_const c) (integrable_of_bdd_prob D (hS j)), integral_const,
    probReal_univ, one_smul] at hpos'
  linarith

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- No mass strictly above an extreme mean, coordinatewise. -/
theorem measure_gt_eq_zero_of_mean_extreme (D : Measure X) [IsProbabilityMeasure D] (hD : D ≪ ν)
    {e : J → ℝ} (he : e ∈ (momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ)
    (hmean : (fun i ↦ ∫ x, S i x ∂D) = e) (j : J) : D {x | e j < S j x} = 0 := by
  by_contra hA0
  have hA : MeasurableSet {x | e j < S j x} := measurableSet_lt measurable_const (hS j).1
  by_cases hAc : D {x | e j < S j x}ᶜ = 0
  · have := lt_integral_of_carried hS D j hAc hA0
    rw [congrFun hmean j] at this
    exact lt_irrefl _ this
  · have hcond := conditional_mean_eq_of_extreme hS ν D hD he hmean hA hA0 hAc
    have hPA := isProbabilityMeasure_faceMeasure D hA0
    have hcA : faceMeasure D {x | e j < S j x} {x | e j < S j x}ᶜ = 0 := by
      rw [faceMeasure, Measure.smul_apply, Measure.restrict_apply hA.compl, compl_inter_self,
        measure_empty, smul_zero]
    have hpA : faceMeasure D {x | e j < S j x} {x | e j < S j x} ≠ 0 := by
      rw [faceMeasure, Measure.smul_apply, Measure.restrict_apply hA, inter_self, smul_eq_mul,
        ENNReal.inv_mul_cancel hA0 (measure_ne_top _ _)]
      exact one_ne_zero
    have := lt_integral_of_carried hS (faceMeasure D _) j hcA hpA
    rw [congrFun hcond j] at this
    exact lt_irrefl _ this

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- No mass strictly below an extreme mean, coordinatewise. -/
theorem measure_lt_eq_zero_of_mean_extreme (D : Measure X) [IsProbabilityMeasure D] (hD : D ≪ ν)
    {e : J → ℝ} (he : e ∈ (momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ)
    (hmean : (fun i ↦ ∫ x, S i x ∂D) = e) (j : J) : D {x | S j x < e j} = 0 := by
  by_contra hA0
  have hA : MeasurableSet {x | S j x < e j} := measurableSet_lt (hS j).1 measurable_const
  by_cases hAc : D {x | S j x < e j}ᶜ = 0
  · have := integral_lt_of_carried hS D j hAc hA0
    rw [congrFun hmean j] at this
    exact lt_irrefl _ this
  · have hcond := conditional_mean_eq_of_extreme hS ν D hD he hmean hA hA0 hAc
    have hPA := isProbabilityMeasure_faceMeasure D hA0
    have hcA : faceMeasure D {x | S j x < e j} {x | S j x < e j}ᶜ = 0 := by
      rw [faceMeasure, Measure.smul_apply, Measure.restrict_apply hA.compl, compl_inter_self,
        measure_empty, smul_zero]
    have hpA : faceMeasure D {x | S j x < e j} {x | S j x < e j} ≠ 0 := by
      rw [faceMeasure, Measure.smul_apply, Measure.restrict_apply hA, inter_self, smul_eq_mul,
        ENNReal.inv_mul_cancel hA0 (measure_ne_top _ _)]
      exact one_ne_zero
    have := integral_lt_of_carried hS (faceMeasure D _) j hcA hpA
    rw [congrFun hcond j] at this
    exact lt_irrefl _ this

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **An extreme mean forces concentration on its fibre**: a `ν`-dominated law with extreme mean
`e` is carried by `{S = e}`. -/
theorem ae_statPoint_eq_of_mean_extreme (D : Measure X) [IsProbabilityMeasure D] (hD : D ≪ ν)
    {e : J → ℝ} (he : e ∈ (momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ)
    (hmean : (fun i ↦ ∫ x, S i x ∂D) = e) : ∀ᵐ x ∂D, statPoint S x = e := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx ↦ ?_) (measure_iUnion_null_iff.2 fun j ↦
    measure_union_null_iff.2 ⟨measure_gt_eq_zero_of_mean_extreme hS ν D hD he hmean j,
      measure_lt_eq_zero_of_mean_extreme hS ν D hD he hmean j⟩)
  simp only [mem_ofPred_eq] at hx
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  refine mem_iUnion.2 ⟨j, ?_⟩
  rcases lt_or_gt_of_ne hj with h | h
  · exact Or.inr h
  · exact Or.inl h

end Split

section L1

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The law of an `L¹` probability density. -/
theorem isProbabilityMeasure_withDensity_of_mem_probL1 {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (f x)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn f) hf.1, hf.2, ENNReal.ofReal_one]

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem mean_withDensity_eq_meanL1 {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    (fun i ↦ ∫ x, S i x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (f x))) = meanL1 hS ν f := by
  funext j
  rw [meanL1_apply hS ν, integral_withDensity_eq_integral_toReal_smul₀
    (Lp.aestronglyMeasurable f).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hf.1] with x hx
  rw [Pi.zero_apply] at hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **An `L¹` density with extreme mean vanishes off the fibre.** -/
theorem ae_eq_zero_off_fibre_of_mean_extreme {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) {e : J → ℝ}
    (he : e ∈ (momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ) (hmean : meanL1 hS ν f = e) :
    ∀ᵐ x ∂ν, statPoint S x ≠ e → f x = 0 := by
  have hP := isProbabilityMeasure_withDensity_of_mem_probL1 ν hf
  have h := ae_statPoint_eq_of_mean_extreme hS ν _ (withDensity_absolutelyContinuous _ _) he
    ((mean_withDensity_eq_meanL1 hS ν hf).trans hmean)
  have hm : MeasurableSet {a | ¬statPoint S a = e} :=
    (measurableSet_eq_fun (measurable_statPoint hS) measurable_const).compl
  rw [ae_iff, withDensity_apply _ hm, lintegral_eq_zero_iff'
    (Lp.aestronglyMeasurable f).aemeasurable.ennreal_ofReal.restrict] at h
  have h' : ∀ᵐ x ∂ν.restrict {a | ¬statPoint S a = e}, ENNReal.ofReal (f x) = 0 := h
  rw [ae_restrict_iff' hm] at h'
  filter_upwards [h', hf.1] with x hx hfx hne
  rw [Pi.zero_apply] at hfx
  have := hx hne
  rw [ENNReal.ofReal_eq_zero] at this
  exact le_antisymm this hfx

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **Every extreme point carrying a feasible density is charged.** -/
theorem statFibre_pos_of_mean_extreme {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) {e : J → ℝ}
    (he : e ∈ (momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ) (hmean : meanL1 hS ν f = e) :
    0 < ν.real (statFibre S e) := by
  by_contra h0
  have hnull : ν (statFibre S e) = 0 := by
    have h1 : ν.real (statFibre S e) = 0 := le_antisymm (not_lt.1 h0) measureReal_nonneg
    rwa [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h1
  have hzero : ∀ᵐ x ∂ν, f x = 0 := by
    have hoff := ae_eq_zero_off_fibre_of_mean_extreme hS ν hf he hmean
    have hin : ∀ᵐ x ∂ν, statPoint S x ≠ e := by
      rw [ae_iff]
      simpa [statFibre] using hnull
    filter_upwards [hoff, hin] with x h1 h2
    exact h1 h2
  have := hf.2
  rw [integral_congr_ae hzero, integral_zero] at this
  exact zero_ne_one this

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **Feasible densities over distinct extreme points are at `L¹`-distance exactly `2`.** -/
theorem norm_sub_eq_two_of_mean_extreme {f g : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) (hg : g ∈ probL1 ν)
    {e e' : J → ℝ} (he : e ∈ (momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ)
    (he' : e' ∈ (momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ) (hne : e ≠ e')
    (hmf : meanL1 hS ν f = e) (hmg : meanL1 hS ν g = e') : ‖f - g‖ = 2 := by
  rw [L1.norm_eq_integral_norm]
  have hae : (fun x ↦ ‖(f - g) x‖) =ᵐ[ν] fun x ↦ f x + g x := by
    filter_upwards [Lp.coeFn_sub f g, hf.1, hg.1,
      ae_eq_zero_off_fibre_of_mean_extreme hS ν hf he hmf,
      ae_eq_zero_off_fibre_of_mean_extreme hS ν hg he' hmg] with x hx hfx hgx hf0 hg0
    rw [Pi.zero_apply] at hfx hgx
    rw [hx, Pi.sub_apply, Real.norm_eq_abs]
    by_cases hxe : statPoint S x = e
    · have : statPoint S x ≠ e' := hxe ▸ hne
      rw [hg0 this, sub_zero, add_zero, abs_of_nonneg hfx]
    · rw [hf0 hxe, zero_sub, abs_neg, zero_add, abs_of_nonneg hgx]
  rw [integral_congr_ae hae, integral_add (L1.integrable_coeFn f) (L1.integrable_coeFn g),
    hf.2, hg.2]
  norm_num

end L1

end Laplace.Multi
