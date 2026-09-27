/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFacewiseRegression
import Laplace.Multi.ConditioningChainRule

/-!
# Exact face restriction of the entropy response

Every finite data law lives statistically inside its minimal moment face, even when that face lies
on the boundary of the polytope: for a mean `M` of the closed polytope with support `A = supp q*(M)`
(the atoms charged by the entropy response), the entropy response of `M` relative to the base law
`ν` is the entropy response of `M` relative to the **face law** `ν_A = ν(· | A)`,

`Π^{ν_A}(M) = Π^ν(M)`   (`responseProjection_faceMeasure_supportSet`).

The proof is entropy minimisation under the information chain rule of conditioning: the
`ν`-response is carried by `A` (`responseProjection_compl_supportSet`), every law carried by `A`
has `KL(Q ‖ ν) = KL(Q ‖ ν_A) − log ν(A)`, so the two constrained minimisation problems differ by a
constant on the constraint set and have the same minimiser; formally the `ν`-Pythagorean identity
applied to the `ν_A`-response forces `KL(Π^{ν_A}(M) ‖ Π^ν(M)) = 0`. Consequently the interior
response calculus of the face family applies at every boundary mean: the response map is stratified
by the faces of the polytope, and each stratum is an interior problem for the conditioned base law.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Restriction

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The support of the entropy response is charged by the base law. -/
theorem measureReal_supportSet_pos {M : J → ℝ} (hM : M ∈ hull) :
    0 < ν.real (supportSet hS ν M) := by
  have hq := qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, 0 < qStarVec hS ν M x₀ := by
    by_contra hne
    push Not at hne
    have : ∑ x, qStarVec hS ν M x = 0 :=
      Finset.sum_eq_zero fun x _ ↦ le_antisymm (hne x) (hq.1 x)
    rw [hq.2] at this
    exact one_ne_zero this
  have h1 : 0 < ν.real {x₀} := ENNReal.toReal_pos (hν x₀).ne' (measure_ne_top _ _)
  exact h1.trans_le (measureReal_mono (singleton_subset_iff.2 hx₀))

/-- The entropy response is carried by its support. -/
theorem responseProjection_compl_supportSet {M : J → ℝ} (hM : M ∈ hull) :
    responseProjection hS ν M (supportSet hS ν M)ᶜ = 0 := by
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
  rw [← vecMeasure_qStarVec hS ν hfin, ← (Set.toFinite (supportSet hS ν M)ᶜ).coe_toFinset,
    ← sum_measure_singleton]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  rw [vecMeasure_apply_singleton,
    qStarVec_eq_zero_of_notMem hS ν hν hM ((Set.Finite.mem_toFinset _).1 hx), ENNReal.ofReal_zero]

/-- **EXACT FACE RESTRICTION**: the entropy response of a mean relative to the base law is its
entropy response relative to the face law of its support, `Π^{ν_A}(M) = Π^ν(M)`. -/
theorem responseProjection_faceMeasure_supportSet {M : J → ℝ} (hM : M ∈ hull) :
    responseProjection hS (faceMeasure ν (supportSet hS ν M)) M = responseProjection hS ν M := by
  set A := supportSet hS ν M with hAdef
  have hAm : MeasurableSet A := (Set.toFinite A).measurableSet
  have hp : 0 < ν.real A := measureReal_supportSet_pos hS ν hν hM
  have hA0 : ν A ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hνA : IsProbabilityMeasure (faceMeasure ν A) := isProbabilityMeasure_faceMeasure ν hA0
  have hAν : faceMeasure ν A ≪ ν := by
    rw [faceMeasure_eq_withDensity ν hAm]
    exact withDensity_absolutelyContinuous _ _
  -- the base-`ν` response
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
  obtain ⟨hP, hmean, hkl, hpyth⟩ := responseProjection_spec hS ν hfin
  have hRν := responseProjection_absolutelyContinuous hS ν hfin
  have hRA : responseProjection hS ν M ≪ faceMeasure ν A :=
    absolutelyContinuous_faceMeasure ν hAm hRν (responseProjection_compl_supportSet hS ν hν hM)
  have hRkl : klDiv (responseProjection hS ν M) ν ≠ ⊤ := hkl ▸ hfin
  have hchainR := klDiv_eq_klDiv_faceMeasure_add ν hAm hp (responseProjection hS ν M) hRA
  have hRAkl : klDiv (responseProjection hS ν M) (faceMeasure ν A) ≠ ⊤ := by
    rw [hchainR] at hRkl
    exact (ENNReal.add_ne_top.1 hRkl).1
  -- finite rate for the face law and the base-`ν_A` response
  have hfinA : genRate (faceMeasure ν A) S M ≠ ⊤ := by
    rw [← entropyProj_eq_genRate hS (faceMeasure ν A) M]
    exact ne_top_of_le_ne_top hRAkl (entropyProj_le_klDiv (faceMeasure ν A) _ hmean)
  obtain ⟨hP', hmean', hkl', -⟩ := responseProjection_spec hS (faceMeasure ν A) hfinA
  have hR'A := responseProjection_absolutelyContinuous hS (faceMeasure ν A) hfinA
  have hR'ν : responseProjection hS (faceMeasure ν A) M ≪ ν := hR'A.trans hAν
  have hchainR' := klDiv_eq_klDiv_faceMeasure_add ν hAm hp
    (responseProjection hS (faceMeasure ν A) M) hR'A
  -- minimality at the face law transfers to the base law
  have hmin : klDiv (responseProjection hS (faceMeasure ν A) M) (faceMeasure ν A) ≤
      klDiv (responseProjection hS ν M) (faceMeasure ν A) := by
    rw [hkl', ← entropyProj_eq_genRate hS (faceMeasure ν A) M]
    exact entropyProj_le_klDiv (faceMeasure ν A) _ hmean
  have hmin' : klDiv (responseProjection hS (faceMeasure ν A) M) ν ≤
      klDiv (responseProjection hS ν M) ν := by
    rw [hchainR', hchainR]
    exact add_le_add hmin le_rfl
  -- the Pythagorean identity at `ν` forces the two responses to coincide
  have hpy := hpyth _ hP' hmean'
  rw [hpy, hkl] at hmin'
  have hzero : klDiv (responseProjection hS (faceMeasure ν A) M) (responseProjection hS ν M) = 0 :=
    nonpos_iff_eq_zero.1
      (ENNReal.le_of_add_le_add_right hfin (hmin'.trans_eq (zero_add _).symm))
  have := hP
  have := hP'
  exact klDiv_eq_zero_iff.1 hzero

end Restriction

end Laplace.Multi
