/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFaceCalculus

/-!
# Data laws are carried by the minimal face of their mean

Csiszár's support theorem says that the support of the entropy response `q*(M)` is the largest
support among all probability vectors with mean `M`. Consequently **every data law `D` is carried by
the atoms `A = supp q*(m_D)` of the minimal face of its mean**
(`measure_singleton_eq_zero_of_notMem_supportSet`, `measure_compl_supportSet_dataMean`): a law
whose mean lies on a face of the polytope never charges an atom outside that face. Samples from `D`
therefore lie in `A`, and every empirical mean lies in the face polytope `conv S(A)`.

The exact face restriction of `ResponseFaceRestriction` extends from the point `M` to the whole
face polytope: for every mean `N` of the face `conv S(A)`, `A = supp q*(M)`, the entropy response
relative to the conditioned law `ν_A` is the entropy response relative to `ν`
(`responseProjection_faceMeasure_of_supportSet_subset`,
`responseProjection_faceMeasure_of_mem_carriedResponses`). Together: the statistics of the plug-in
estimator at any data law are the statistics of the plug-in estimator of the face law `ν_A`, for
which the data mean is an interior point.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Carried

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- **Face restriction on the whole face polytope**: if the support of `q*(N)` lies in `A`, the
entropy response of `N` relative to `ν_A` is its entropy response relative to `ν`. -/
theorem responseProjection_faceMeasure_of_supportSet_subset {N : J → ℝ} (hN : N ∈ hull)
    {A : Set X} (hsub : supportSet hS ν N ⊆ A) :
    responseProjection hS (faceMeasure ν A) N = responseProjection hS ν N := by
  have hAm : MeasurableSet A := (Set.toFinite A).measurableSet
  have hp : 0 < ν.real A :=
    (measureReal_supportSet_pos hS ν hν hN).trans_le (measureReal_mono hsub)
  have hA0 : ν A ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hνA : IsProbabilityMeasure (faceMeasure ν A) := isProbabilityMeasure_faceMeasure ν hA0
  have hAν : faceMeasure ν A ≪ ν := by
    rw [faceMeasure_eq_withDensity ν hAm]
    exact withDensity_absolutelyContinuous _ _
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hN
  obtain ⟨hP, hmean, hkl, hpyth⟩ := responseProjection_spec hS ν hfin
  have hRν := responseProjection_absolutelyContinuous hS ν hfin
  have hRA : responseProjection hS ν N ≪ faceMeasure ν A :=
    absolutelyContinuous_faceMeasure ν hAm hRν
      (measure_mono_null (compl_subset_compl.2 hsub)
        (responseProjection_compl_supportSet hS ν hν hN))
  have hRkl : klDiv (responseProjection hS ν N) ν ≠ ⊤ := hkl ▸ hfin
  have hchainR := klDiv_eq_klDiv_faceMeasure_add ν hAm hp (responseProjection hS ν N) hRA
  have hRAkl : klDiv (responseProjection hS ν N) (faceMeasure ν A) ≠ ⊤ := by
    rw [hchainR] at hRkl
    exact (ENNReal.add_ne_top.1 hRkl).1
  have hfinA : genRate (faceMeasure ν A) S N ≠ ⊤ := by
    rw [← entropyProj_eq_genRate hS (faceMeasure ν A) N]
    exact ne_top_of_le_ne_top hRAkl (entropyProj_le_klDiv (faceMeasure ν A) _ hmean)
  obtain ⟨hP', hmean', hkl', -⟩ := responseProjection_spec hS (faceMeasure ν A) hfinA
  have hR'A := responseProjection_absolutelyContinuous hS (faceMeasure ν A) hfinA
  have hchainR' := klDiv_eq_klDiv_faceMeasure_add ν hAm hp
    (responseProjection hS (faceMeasure ν A) N) hR'A
  have hmin : klDiv (responseProjection hS (faceMeasure ν A) N) (faceMeasure ν A) ≤
      klDiv (responseProjection hS ν N) (faceMeasure ν A) := by
    rw [hkl', ← entropyProj_eq_genRate hS (faceMeasure ν A) N]
    exact entropyProj_le_klDiv (faceMeasure ν A) _ hmean
  have hmin' : klDiv (responseProjection hS (faceMeasure ν A) N) ν ≤
      klDiv (responseProjection hS ν N) ν := by
    rw [hchainR', hchainR]
    exact add_le_add hmin le_rfl
  have hpy := hpyth _ hP' hmean'
  rw [hpy, hkl] at hmin'
  have hzero : klDiv (responseProjection hS (faceMeasure ν A) N) (responseProjection hS ν N) = 0 :=
    nonpos_iff_eq_zero.1
      (ENNReal.le_of_add_le_add_right hfin (hmin'.trans_eq (zero_add _).symm))
  have := hP
  have := hP'
  exact klDiv_eq_zero_iff.1 hzero

/-- **Face restriction on the face polytope of `M`**: for every `N` in the face polytope of
`A = supp q*(M)`, `Π^{ν_A}(N) = Π^ν(N)`. -/
theorem responseProjection_faceMeasure_of_mem_carriedResponses {M N : J → ℝ} (hM : M ∈ hull)
    (hN : N ∈ carriedResponses S (supportSet hS ν M)) :
    responseProjection hS (faceMeasure ν (supportSet hS ν M)) N = responseProjection hS ν N :=
  responseProjection_faceMeasure_of_supportSet_subset hS ν hν
    (carriedResponses_subset_hull (S := S) _ hN)
    (supportSet_subset_of_mem_carriedResponses hS ν hν hM hN)

variable (D : Measure X) [IsProbabilityMeasure D]

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

omit [Nonempty X] [Nonempty J] hS hν [IsProbabilityMeasure ν] in
/-- The atom vector of a probability law on a finite alphabet is a probability vector. -/
theorem atomVec_mem_stdSimplex : (fun x ↦ D.real {x}) ∈ stdSimplex ℝ X :=
  ⟨fun _ ↦ measureReal_nonneg, by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]⟩

omit [Nonempty X] [Fintype J] [Nonempty J] hν [IsProbabilityMeasure ν] in
/-- The mean of a data law is the response of its atom vector. -/
theorem dataMean_eq_vecMoment_atomVec : mD = vecMoment S (fun x ↦ D.real {x}) := by
  funext j
  rw [integral_fintype (μ := D) (f := S j) (integrable_of_bdd_prob D (hS j))]
  simp [vecMoment]

/-- **Csiszár's support theorem for data laws**: a data law charges no atom outside the support
of the entropy response of its mean. -/
theorem measure_singleton_eq_zero_of_notMem_supportSet {x : X} (hx : x ∉ supportSet hS ν mD) :
    D {x} = 0 := by
  have hw := atomVec_mem_stdSimplex D
  have hM : mD ∈ hull := dataLawMean_mem_polytope hS ν hν D
  have hq := qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM
  by_contra h0
  have hpos : 0 < D.real {x} := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  refine hx (support_absorb hS ν hν hM hq (fun y hy ↦ qStarVec_eq_zero_of_notMem hS ν hν hM hy)
    hw ?_ hpos)
  rw [vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM),
    dataMean_eq_vecMoment_atomVec hS D]

/-- **Data laws are carried by the minimal face of their mean.** -/
theorem measure_compl_supportSet_dataMean : D (supportSet hS ν mD)ᶜ = 0 := by
  rw [← (Set.toFinite (supportSet hS ν mD)ᶜ).coe_toFinset, ← sum_measure_singleton]
  exact Finset.sum_eq_zero fun x hx ↦
    measure_singleton_eq_zero_of_notMem_supportSet hS ν hν D ((Set.Finite.mem_toFinset _).1 hx)

/-- The data law is absolutely continuous with respect to the face law of its mean. -/
theorem absolutelyContinuous_faceMeasure_dataMean : D ≪ faceMeasure ν (supportSet hS ν mD) :=
  absolutelyContinuous_faceMeasure ν (Set.toFinite _).measurableSet
    (absolutelyContinuous_of_full_support hν D) (measure_compl_supportSet_dataMean hS ν hν D)

end Carried

end Laplace.Multi
