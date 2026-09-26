/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.NaturalParameterTaylor

/-!
# Polyhedral completion I: vertex witnesses

For a general probability space `(X, ν)` with bounded features `S`, suppose the moment body is a
polytope `conv V` (`V` a finite set of vertices) and every vertex is **charged**:
`ν{S = v} > 0`. The **vertex laws** `L(a) = Σ_v a_v ν(· | S = v)`, `a` in the simplex on `V`,
are `ν`-dominated probability laws with bounded densities, mean `Σ_v a_v v`, and finite relative
entropy. Consequently **every point of the polytope has finite rate**
(`genRate_ne_top_of_mem_momentBody_polytope`): the response projection `q_M` exists on the whole
closed moment body, not only in its relative interior.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Fibre

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (S : J → X → ℝ)

omit [MeasurableSpace X] [Fintype J] in
/-- The fibre `{S = v}` of the statistic. -/
def statFibre (v : J → ℝ) : Set X := {x | statPoint S x = v}

variable {S}

omit [Fintype J] in
theorem measurableSet_statFibre [Finite J] (hS : ∀ j, Bdd (S j)) (v : J → ℝ) :
    MeasurableSet (statFibre S v) := by
  cases nonempty_fintype J
  exact measurableSet_eq_fun (measurable_statPoint hS) measurable_const

omit [MeasurableSpace X] [Fintype J] in
theorem stat_eq_of_mem_statFibre {v : J → ℝ} {x : X} (hx : x ∈ statFibre S v) (j : J) :
    S j x = v j := congrFun hx j

omit [MeasurableSpace X] [Fintype J] in
theorem statFibre_disjoint {v w : J → ℝ} (hvw : v ≠ w) : Disjoint (statFibre S v) (statFibre S w) :=
  Set.disjoint_left.2 fun _ hv hw ↦ hvw (hv.symm.trans hw)

end Fibre

section Vertex

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Finite J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] (V : Finset (J → ℝ))
include hS

omit [Finite J] hS [IsProbabilityMeasure ν] in
variable (S) in
/-- The vertex density `h_a = Σ_v a_v 1_{S=v} / ν{S=v}`. -/
noncomputable def vertexDensity (a : V → ℝ) (x : X) : ℝ :=
  ∑ v : V, (statFibre S (v : J → ℝ)).indicator (fun _ ↦ a v / ν.real (statFibre S (v : J → ℝ))) x

omit [Finite J] hS [IsProbabilityMeasure ν] in
variable (S) in
/-- The vertex law `L(a) = Σ_v a_v ν(· | S = v)`. -/
noncomputable def vertexLaw (a : V → ℝ) : Measure X :=
  ν.withDensity fun x ↦ ENNReal.ofReal (vertexDensity S ν V a x)

omit [IsProbabilityMeasure ν] in
theorem measurable_vertexDensity (a : V → ℝ) : Measurable (vertexDensity S ν V a) :=
  Finset.measurable_sum _ fun v _ ↦ measurable_const.indicator (measurableSet_statFibre hS v)

variable (hV : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hV

omit [Finite J] hS [IsProbabilityMeasure ν] in
theorem vertexDensity_nonneg {a : V → ℝ} (ha : ∀ v, 0 ≤ a v) (x : X) :
    0 ≤ vertexDensity S ν V a x :=
  Finset.sum_nonneg fun v _ ↦
    Set.indicator_nonneg (fun _ _ ↦ div_nonneg (ha v) (hV v v.2).le) x

omit [Finite J] hS [IsProbabilityMeasure ν] in
/-- The coarse uniform bound `h_a ≤ Σ_v 1/ν{S=v}` for weights `≤ 1`. -/
theorem vertexDensity_le {a : V → ℝ} (ha1 : ∀ v, a v ≤ 1) (x : X) :
    vertexDensity S ν V a x ≤ ∑ v : V, (ν.real (statFibre S (v : J → ℝ)))⁻¹ := by
  refine Finset.sum_le_sum fun v _ ↦ ?_
  refine Set.indicator_apply_le' (fun _ ↦ ?_) fun _ ↦ inv_nonneg.2 (hV v v.2).le
  rw [div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.2 (hV v v.2).le) (ha1 v)

omit [Finite J] hS hV [IsProbabilityMeasure ν] in
/-- On the fibre `{S = v}` the vertex density is `a_v / ν{S = v}`. -/
theorem vertexDensity_of_mem (a : V → ℝ) (v : V) {x : X} (hx : x ∈ statFibre S (v : J → ℝ)) :
    vertexDensity S ν V a x = a v / ν.real (statFibre S (v : J → ℝ)) := by
  unfold vertexDensity
  rw [Finset.sum_eq_single v (fun w _ hw ↦ ?_) (fun h ↦ absurd (Finset.mem_univ v) h)]
  · rw [Set.indicator_of_mem hx]
  · refine Set.indicator_of_notMem ?_ _
    intro hxw
    exact hw (Subtype.ext (hxw.symm.trans hx))

omit hV [IsProbabilityMeasure ν] in
theorem integral_indicator_statFibre (v : J → ℝ) (c : ℝ) :
    ∫ x, (statFibre S v).indicator (fun _ ↦ c) x ∂ν = ν.real (statFibre S v) * c := by
  rw [integral_indicator (measurableSet_statFibre hS v), setIntegral_const, smul_eq_mul]

omit hV in
theorem integrable_vertexDensity (a : V → ℝ) : Integrable (vertexDensity S ν V a) ν :=
  integrable_finsetSum _ fun v _ ↦ (integrable_const _).indicator (measurableSet_statFibre hS v)

/-- The vertex law has mass `Σ_v a_v`. -/
theorem integral_vertexDensity (a : V → ℝ) : ∫ x, vertexDensity S ν V a x ∂ν = ∑ v : V, a v := by
  unfold vertexDensity
  rw [integral_finsetSum _ fun v _ ↦ (integrable_const _).indicator (measurableSet_statFibre hS _)]
  exact Finset.sum_congr rfl fun v _ ↦ by
    rw [integral_indicator_statFibre hS ν, mul_div_cancel₀ _ (hV v v.2).ne']

/-- The vertex law has mean `Σ_v a_v v`. -/
theorem integral_stat_mul_vertexDensity (a : V → ℝ) (j : J) :
    ∫ x, S j x * vertexDensity S ν V a x ∂ν = ∑ v : V, a v * (v : J → ℝ) j := by
  have e : ∀ x, S j x * vertexDensity S ν V a x = ∑ v : V,
      (statFibre S (v : J → ℝ)).indicator
        (fun _ ↦ (v : J → ℝ) j * (a v / ν.real (statFibre S (v : J → ℝ)))) x := fun x ↦ by
    unfold vertexDensity
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    by_cases hx : x ∈ statFibre S (v : J → ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, stat_eq_of_mem_statFibre hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  simp_rw [e]
  rw [integral_finsetSum _ fun v _ ↦ (integrable_const _).indicator (measurableSet_statFibre hS _)]
  exact Finset.sum_congr rfl fun v _ ↦ by
    rw [integral_indicator_statFibre hS ν]
    field_simp [(hV v v.2).ne']

omit [IsProbabilityMeasure ν] in
/-- Integrals against the vertex law (no integrability needed). -/
theorem integral_vertexLaw {a : V → ℝ} (ha : ∀ v, 0 ≤ a v) (f : X → ℝ) :
    ∫ x, f x ∂vertexLaw S ν V a = ∫ x, vertexDensity S ν V a x * f x ∂ν := by
  unfold vertexLaw
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (measurable_vertexDensity hS ν V a).ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) f]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (vertexDensity_nonneg ν V hV ha x), smul_eq_mul]

theorem isProbabilityMeasure_vertexLaw {a : V → ℝ} (ha : a ∈ stdSimplex ℝ V) :
    IsProbabilityMeasure (vertexLaw S ν V a) := by
  refine ⟨?_⟩
  unfold vertexLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_vertexDensity hS ν V a)
      (Eventually.of_forall (vertexDensity_nonneg ν V hV ha.1)),
    integral_vertexDensity hS ν V hV, ha.2, ENNReal.ofReal_one]

theorem integral_stat_vertexLaw {a : V → ℝ} (ha : ∀ v, 0 ≤ a v) (j : J) :
    ∫ x, S j x ∂vertexLaw S ν V a = ∑ v : V, a v * (v : J → ℝ) j := by
  rw [integral_vertexLaw hS ν V hV ha, ← integral_stat_mul_vertexDensity hS ν V hV a j]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)

omit [Finite J] hS hV [IsProbabilityMeasure ν] in
theorem vertexLaw_absolutelyContinuous (a : V → ℝ) : vertexLaw S ν V a ≪ ν :=
  withDensity_absolutelyContinuous _ _

/-- The log-likelihood ratio of the vertex law is `log h_a`, `ν`-a.e. -/
theorem llr_vertexLaw_ae {a : V → ℝ} (ha : ∀ v, 0 ≤ a v) :
    llr (vertexLaw S ν V a) ν =ᵐ[ν] fun x ↦ Real.log (vertexDensity S ν V a x) := by
  have h := Measure.rnDeriv_withDensity ν (measurable_vertexDensity hS ν V a).ennreal_ofReal
  filter_upwards [h] with x hx
  unfold llr
  rw [show (vertexLaw S ν V a).rnDeriv ν x = ENNReal.ofReal (vertexDensity S ν V a x) from hx,
    ENNReal.toReal_ofReal (vertexDensity_nonneg ν V hV ha x)]

/-- The vertex law has finite relative entropy (bounded density). -/
theorem klDiv_vertexLaw_ne_top {a : V → ℝ} (ha : a ∈ stdSimplex ℝ V) :
    klDiv (vertexLaw S ν V a) ν ≠ ⊤ := by
  refine klDiv_ne_top (vertexLaw_absolutelyContinuous ν V a) ?_
  have hm := measurable_vertexDensity hS ν V a
  change Integrable _ (ν.withDensity fun x ↦ ENNReal.ofReal (vertexDensity S ν V a x))
  rw [integrable_withDensity_iff_integrable_smul₀' hm.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have ha1 : ∀ v, a v ≤ 1 := fun v ↦ by
    rw [← ha.2]
    exact Finset.single_le_sum (fun w _ ↦ ha.1 w) (Finset.mem_univ v)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ))
    (b := ∑ v : V, (ν.real (statFibre S (v : J → ℝ)))⁻¹)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hbdd : Bdd fun x ↦ vertexDensity S ν V a x * Real.log (vertexDensity S ν V a x) :=
    ⟨hm.mul (Real.measurable_log.comp hm), C, fun x ↦ by
      rw [← Real.norm_eq_abs]
      exact hC _ ⟨vertexDensity_nonneg ν V hV ha.1 x, vertexDensity_le ν V hV ha1 x⟩⟩
  refine (integrable_of_bdd_prob ν hbdd).congr ?_
  filter_upwards [llr_vertexLaw_ae hS ν V hV ha.1] with x hx
  rw [hx, ENNReal.toReal_ofReal (vertexDensity_nonneg ν V hV ha.1 x), smul_eq_mul]

end Vertex

section Polytope

variable {J : Type*} (V : Finset (J → ℝ))

/-- Membership in the polytope `conv V` is a simplex combination of the vertices. -/
theorem mem_convexHull_iff_exists_vertexWeights (M : J → ℝ) :
    M ∈ convexHull ℝ (V : Set (J → ℝ)) ↔
      ∃ a ∈ stdSimplex ℝ V, ∑ v : V, a v • (v : J → ℝ) = M := by
  classical
  rw [Finset.mem_convexHull']
  constructor
  · rintro ⟨w, hw0, hw1, hwM⟩
    refine ⟨fun v ↦ w v, ⟨fun v ↦ hw0 v v.2, ?_⟩, ?_⟩
    · rw [← hw1, ← Finset.sum_coe_sort V w]
    · rw [← hwM, ← Finset.sum_coe_sort V (fun y ↦ w y • y)]
  · rintro ⟨a, ⟨ha0, ha1⟩, haM⟩
    refine ⟨fun y ↦ if h : y ∈ V then a ⟨y, h⟩ else 0, fun y hy ↦ ?_, ?_, ?_⟩
    · beta_reduce
      rw [dif_pos hy]
      exact ha0 _
    · rw [← ha1, ← Finset.sum_coe_sort V]
      exact Finset.sum_congr rfl fun v _ ↦ by rw [dif_pos v.2]
    · rw [← haM, ← Finset.sum_coe_sort V]
      exact Finset.sum_congr rfl fun v _ ↦ by
        beta_reduce
        rw [dif_pos v.2]

end Polytope

section Rate

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (hV : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hV

omit [Nonempty X] [Nonempty J] in
/-- **Every point of a charged polytope has finite rate.** -/
theorem genRate_ne_top_of_mem_convexHull_vertices {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) : genRate ν S M ≠ ⊤ := by
  obtain ⟨a, ha, haM⟩ := (mem_convexHull_iff_exists_vertexWeights V M).1 hM
  have hP := isProbabilityMeasure_vertexLaw hS ν V hV ha
  refine ne_top_of_le_ne_top (klDiv_vertexLaw_ne_top hS ν V hV ha)
    (genRate_le_klDiv ν hS (vertexLaw S ν V a) ?_)
  funext j
  rw [integral_stat_vertexLaw hS ν V hV ha.1, ← haM, Finset.sum_apply]
  exact Finset.sum_congr rfl fun v _ ↦ by rw [Pi.smul_apply, smul_eq_mul]

omit [Nonempty X] [Nonempty J] in
/-- **Finite rate on the whole moment body** when it is a polytope with charged vertices. -/
theorem genRate_ne_top_of_mem_momentBody_polytope
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ))) {M : J → ℝ}
    (hM : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S) : genRate ν S M ≠ ⊤ :=
  genRate_ne_top_of_mem_convexHull_vertices hS ν V hV (hpoly ▸ hM)

end Rate

end Laplace.Multi
