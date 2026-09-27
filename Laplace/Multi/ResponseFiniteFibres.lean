/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseBoundaryJourney
import Laplace.Multi.FiniteMinimalFace

/-!
# The response atlas as a quotient: what the response forgets

For a finite space with charged atoms the barycentre map `p ↦ ∑_x p_x S(x)` is a **quotient map**
from the probability simplex onto the moment polytope (`isQuotientMap_momentMapSimplex`), with the
entropy projection `q*` as a continuous section (`continuous_entropySection`,
`momentMapSimplex_entropySection`): the response atlas is literally the quotient of the space of
data laws by their feature means, `Δ(X)/∼ ≅ conv S(X)`, and the response is the canonical
entropy-minimising section.

Each fibre is an affine slice of the simplex whose direction space is
`F₀ = {v : ∑ v_x = 0, ∑ v_x S(x) = 0}` (`fibreDirection`, `mem_fibreDirection_iff`), of
dimension **`|X| − 1 − dim W`** (`finrank_fibreDirection_add`): the direction space `W` of the
moment body is the image of the sum-zero hyperplane under the moment map
(`dirSpan_eq_vectorSpan`, `map_momentMap_sumZero`). Over an interior mean the fibre contains the
strictly positive entropy response, so its affine span has exactly this direction
(`direction_affineSpan_fibre`, `finrank_direction_affineSpan_fibre`). This is a precise
description of what the response forgets: `|X| − 1 − dim W` dimensions of data law per mean.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Linear

variable {X : Type*} [Fintype X] {J : Type*} (S : J → X → ℝ)

/-- The moment map `p ↦ ∑_x p_x S(x)` as a linear map. -/
noncomputable def momentMap : (X → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun := vecMoment S
  map_add' := vecMoment_add S
  map_smul' := vecMoment_smul S

theorem momentMap_apply (p : X → ℝ) : momentMap S p = vecMoment S p := rfl

variable (X) in
/-- The sum functional `v ↦ ∑_x v_x`. -/
noncomputable def sumFunctional : (X → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ x, v x
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

theorem sumFunctional_apply (v : X → ℝ) : sumFunctional X v = ∑ x, v x := rfl

variable (X) in
/-- The sum-zero hyperplane. -/
noncomputable def sumZero : Submodule ℝ (X → ℝ) := LinearMap.ker (sumFunctional X)

theorem mem_sumZero_iff (v : X → ℝ) : v ∈ sumZero X ↔ ∑ x, v x = 0 := Iff.rfl

/-- **The direction space of the fibres**: `{v : ∑ v_x = 0, ∑ v_x S(x) = 0}`. -/
noncomputable def fibreDirection : Submodule ℝ (X → ℝ) :=
  LinearMap.ker (momentMap S) ⊓ sumZero X

theorem mem_fibreDirection_iff (v : X → ℝ) :
    v ∈ fibreDirection S ↔ vecMoment S v = 0 ∧ ∑ x, v x = 0 := Iff.rfl

theorem range_sumFunctional_eq_top [Nonempty X] : LinearMap.range (sumFunctional X) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro r
  refine ⟨fun _ ↦ r / Fintype.card X, ?_⟩
  rw [sumFunctional_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem finrank_sumZero [Nonempty X] : Module.finrank ℝ (sumZero X) = Fintype.card X - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumFunctional X)
  rw [range_sumFunctional_eq_top, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at h
  unfold sumZero
  omega

/-- `S(x) − S(y)` is the moment of a difference of two vertices. -/
theorem statPoint_sub_statPoint_mem_map (x y : X) :
    statPoint S x - statPoint S y ∈ Submodule.map (momentMap S) (sumZero X) := by
  classical
  refine ⟨deltaVec x - deltaVec y, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_sumZero_iff]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    have h1 : ∑ z, deltaVec (X := X) x z = 1 := by simp [deltaVec]
    have h2 : ∑ z, deltaVec (X := X) y z = 1 := by simp [deltaVec]
    rw [h1, h2, sub_self]
  · rw [map_sub, momentMap_apply, momentMap_apply, vecMoment_deltaVec, vecMoment_deltaVec]

/-- **The image of the sum-zero hyperplane under the moment map is the direction of the feature
set**: `momentMap(sumZero) = vectorSpan (range S)`. -/
theorem map_momentMap_sumZero [Nonempty X] :
    Submodule.map (momentMap S) (sumZero X) = vectorSpan ℝ (range (statPoint S)) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv
    rw [Submodule.mem_comap, momentMap_apply, vecMoment_eq_sum_smul]
    obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
    rw [vectorSpan_eq_span_vsub_set_right ℝ (mem_range_self x₀)]
    have e : ∑ x, v x • statPoint S x = ∑ x, v x • (statPoint S x -ᵥ statPoint S x₀) := by
      simp only [vsub_eq_sub, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
      rw [mem_sumZero_iff] at hv
      rw [hv, zero_smul, sub_zero]
    rw [e]
    exact Submodule.sum_mem _ fun x _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨statPoint S x, mem_range_self x, rfl⟩)
  · rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, rfl⟩
    exact statPoint_sub_statPoint_mem_map S x y

/-- The rank–nullity count of the fibre directions. -/
theorem finrank_fibreDirection_add_finrank_vectorSpan [Nonempty X] :
    Module.finrank ℝ (fibreDirection S) +
      Module.finrank ℝ (vectorSpan ℝ (range (statPoint S))) = Fintype.card X - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((momentMap S).comp (sumZero X).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, map_momentMap_sumZero, LinearMap.ker_comp,
    finrank_sumZero] at h
  have hcomap : Submodule.comap (sumZero X).subtype (LinearMap.ker (momentMap S)) =
      Submodule.comap (sumZero X).subtype (fibreDirection S) := by
    unfold fibreDirection
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  have hle : fibreDirection S ≤ sumZero X := inf_le_right
  rw [hcomap, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h
  omega

end Linear

section Fibres

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

omit [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The direction space of the moment body is the direction of the feature set.** -/
theorem dirSpan_eq_vectorSpan : 𝕍 = vectorSpan ℝ (range (statPoint S)) := by
  unfold dirSpan
  rw [momentBody_eq_convexHull hS ν hν, affineSpan_convexHull, direction_affineSpan]

omit [MeasurableSingletonClass X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **What the response forgets**: `dim F₀ + dim W = |X| − 1`. -/
theorem finrank_fibreDirection_add :
    Module.finrank ℝ (fibreDirection S) + Module.finrank ℝ 𝕍 = Fintype.card X - 1 := by
  rw [dirSpan_eq_vectorSpan hS ν hν]
  exact finrank_fibreDirection_add_finrank_vectorSpan S

variable (S) in
omit hS hν [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J]
  [IsProbabilityMeasure ν] in
/-- The barycentre map on the simplex, landing in the moment polytope. -/
noncomputable def momentMapSimplex (p : stdSimplex ℝ X) : hull :=
  ⟨vecMoment S p, vecMoment_mem_convexHull p.2⟩

variable (S) in
omit hS hν [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J]
  [IsProbabilityMeasure ν] in
theorem continuous_momentMapSimplex : Continuous (momentMapSimplex S) :=
  ((continuous_vecMoment S).comp continuous_subtype_val).subtype_mk _

/-- **The entropy section** `M ↦ q*(M)` of the barycentre map. -/
noncomputable def entropySection (M : hull) : stdSimplex ℝ X :=
  ⟨qStarVec hS ν M, qStarVec_mem_stdSimplex hS ν (genRate_ne_top_of_mem_convexHull hS ν hν M.2)⟩

theorem continuous_entropySection : Continuous (entropySection hS ν hν) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuousOn_iff_continuous_domRestrict.1 (continuousOn_qStarVec hS ν hν))

theorem momentMapSimplex_entropySection (M : hull) :
    momentMapSimplex S (entropySection hS ν hν M) = M :=
  Subtype.ext (vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν M.2))

/-- **The response atlas is a quotient**: the barycentre map is a quotient map of the simplex
onto the moment polytope, with the entropy projection as a continuous section. -/
theorem isQuotientMap_momentMapSimplex :
    Topology.IsQuotientMap (momentMapSimplex S) :=
  Topology.IsQuotientMap.of_inverse (continuous_entropySection hS ν hν)
    (continuous_momentMapSimplex S) (momentMapSimplex_entropySection hS ν hν)

variable (S) in
omit hS hν [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J]
  [IsProbabilityMeasure ν] in
/-- The fibre of the barycentre map over a mean `M`. -/
def fibre (M : J → ℝ) : Set (X → ℝ) := {p | p ∈ stdSimplex ℝ X ∧ vecMoment S p = M}

theorem qStarVec_mem_fibre {M : J → ℝ} (hM : M ∈ hull) : qStarVec hS ν M ∈ fibre S M :=
  ⟨qStarVec_mem_stdSimplex hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM),
    vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM)⟩

omit hS hν [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Fintype J] [Nonempty J]
  [IsProbabilityMeasure ν] in
/-- Differences of fibre points lie in the fibre direction. -/
theorem sub_mem_fibreDirection_of_mem_fibre {M : J → ℝ} {p q : X → ℝ} (hp : p ∈ fibre S M)
    (hq : q ∈ fibre S M) : p - q ∈ fibreDirection S := by
  rw [mem_fibreDirection_iff, ← momentMap_apply, map_sub, momentMap_apply, momentMap_apply,
    hp.2, hq.2, sub_self]
  refine ⟨rfl, ?_⟩
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, hp.1.2, hq.1.2, sub_self]

/-- **The entropy response of an interior mean is strictly positive.** -/
theorem qStarVec_pos_of_mem_intrinsicInterior {M : J → ℝ} (hM : M ∈ intrinsicInterior ℝ hull)
    (x : X) : 0 < qStarVec hS ν M x := by
  rw [← intrinsicInterior_momentBody_eq_polytope hS ν hν] at hM
  rw [← atomMass_responseTheta_eq_qStarVec hS ν hM]
  exact atomMass_pos hS ν (fun x ↦ (hν x).ne') _ x

/-- **The fibre over an interior mean is full in every fibre direction** at the entropy response:
`q*(M) + t v` stays in the fibre for small `t`. -/
theorem eventually_add_smul_mem_fibre {M : J → ℝ} (hM : M ∈ intrinsicInterior ℝ hull) {v : X → ℝ}
    (hv : v ∈ fibreDirection S) :
    ∀ᶠ t : ℝ in 𝓝 0, qStarVec hS ν M + t • v ∈ fibre S M := by
  have hM' : M ∈ hull := intrinsicInterior_subset hM
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, 0 ≤ qStarVec hS ν M x + t * v x := by
    rw [eventually_all]
    intro x
    have hc : Continuous fun t : ℝ ↦ qStarVec hS ν M x + t * v x := by fun_prop
    have h0 : 0 < qStarVec hS ν M x + (0 : ℝ) * v x := by
      rw [zero_mul, add_zero]; exact qStarVec_pos_of_mem_intrinsicInterior hS ν hν hM x
    exact (hc.tendsto 0).eventually (lt_mem_nhds h0) |>.mono fun t ht ↦ ht.le
  filter_upwards [hpos] with t ht
  rw [mem_fibreDirection_iff] at hv
  refine ⟨⟨fun x ↦ by simpa using ht x, ?_⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hv.2, mul_zero, add_zero]
    exact (qStarVec_mem_stdSimplex hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM')).2
  · rw [← momentMap_apply, map_add, map_smul, momentMap_apply, momentMap_apply, hv.1, smul_zero,
      add_zero]
    exact vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM')

/-- **The affine span of a fibre over an interior mean has direction `F₀`.** -/
theorem direction_affineSpan_fibre {M : J → ℝ} (hM : M ∈ intrinsicInterior ℝ hull) :
    (affineSpan ℝ (fibre S M)).direction = fibreDirection S := by
  rw [direction_affineSpan]
  refine le_antisymm ?_ fun v hv ↦ ?_
  · rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨p, hp, q, hq, rfl⟩
    exact sub_mem_fibreDirection_of_mem_fibre hp hq
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (eventually_add_smul_mem_fibre hS ν hν hM hv)
    have hmem : qStarVec hS ν M + (ε / 2) • v ∈ fibre S M := hball (by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith)
    have h := vsub_mem_vectorSpan ℝ hmem
      (qStarVec_mem_fibre hS ν hν (intrinsicInterior_subset hM))
    rw [vsub_eq_sub, add_sub_cancel_left] at h
    exact (Submodule.smul_mem_iff _ (by positivity : (ε / 2 : ℝ) ≠ 0)).1 h

/-- **What the response forgets, at every interior mean**: the fibre over `M` is an affine slice of
the simplex of dimension `|X| − 1 − dim W`. -/
theorem finrank_direction_affineSpan_fibre {M : J → ℝ} (hM : M ∈ intrinsicInterior ℝ hull) :
    Module.finrank ℝ (affineSpan ℝ (fibre S M)).direction + Module.finrank ℝ 𝕍 =
      Fintype.card X - 1 := by
  rw [direction_affineSpan_fibre hS ν hν hM]
  exact finrank_fibreDirection_add hS ν hν

end Fibres

end Laplace.Multi
