/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ConditioningChainRule
import Laplace.Multi.EntropyProjection
import Laplace.Multi.FibreOrthogonality
import Laplace.Multi.FiniteResponse
import Laplace.Multi.PathEnergy
import Laplace.Multi.BoundaryRayFormula

/-!
# The boundary information projection: KL Pythagoras on a face

Let `A = {⟨u,S⟩ = β}` be a charged exposed face event (`⟨u,S⟩ ≤ β` a.e., `ν(A) > 0`) and
`Q_M = P^A_v = e^{−⟨v,S⟩} ν_A / Z_A(v)` a member of the face exponential family, with mean
`M = m_A(v)`. For every probability law `Q ≪ ν` with mean `M`,

`D(Q ‖ ν) = D(Q ‖ Q_M) + D(Q_M ‖ ν)`,

so `Q_M` is the unique relative-entropy minimiser among laws with mean `M`. The proof runs
the two existing exact identities in sequence: a law whose mean lies on the supporting
hyperplane is carried by the face (`compl_eq_zero_of_mean_face`), so the conditioning chain
rule gives `D(Q‖ν) = D(Q‖ν_A) − log ν(A)`, and the interior Pythagoras of the face family on
`ν_A` splits `D(Q‖ν_A) = D(Q‖Q_M) + D(Q_M‖ν_A)`; the same chain rule for `Q_M` reassembles
`D(Q_M‖ν)`. Everything is in `ℝ≥0∞`, so `D(Q‖ν) = ∞` needs no separate treatment. This is
the **variational response law at a boundary mean**, which exists whether or not the mean is
Fisher-accessible.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {u : J → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) {A : Set X}
  (hA : A = {x | dirLoss S u x = β}) (hp : 0 < ν.real A)
include hS hA hp

/-- The face exponential family `P^A_v = e^{−⟨v,S⟩} ν_A / Z_A(v)`. -/
local notation "Qface" => familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty X] [Fintype J] hS hA in
theorem isProbabilityMeasure_faceMeasure_of_real_pos : IsProbabilityMeasure (faceMeasure ν A) :=
  isProbabilityMeasure_faceMeasure ν (ENNReal.toReal_pos_iff.1 hp).1.ne'

omit hA in
/-- The face family is carried by the face. -/
theorem faceFamily_absolutelyContinuous (v : J → ℝ) : Qface v ≪ faceMeasure ν A := by
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν hp
  rw [familyMeasure_one_zero_eq_tilted hS]
  exact tilted_absolutelyContinuous _ _

omit [Nonempty X] [IsProbabilityMeasure ν] hp in
theorem measurableSet_of_eq_faceFibre : MeasurableSet A := by
  rw [hA]
  exact measurableSet_faceFibre hS u β

/-- The face family's mean lies on the supporting hyperplane: `⟨u, m_A(v)⟩ = β`. -/
theorem dotJ_meanMap_faceFamily (v : J → ℝ) :
    dotJ u (meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 v) = β := by
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν hp
  have hQ := isProbabilityMeasure_family hS (faceMeasure ν A) v
  rw [← mean_familyMeasure_one_zero hS (faceMeasure ν A) v, dotJ_integral_eq _ hS u]
  have hae : ∀ᵐ x ∂Qface v, dirLoss S u x = β :=
    (faceFamily_absolutelyContinuous hS ν hp v).ae_le
      ((ae_mem_faceMeasure ν (measurableSet_of_eq_faceFibre hS hA)).mono fun x hx ↦ by
        rw [hA] at hx
        exact hx)
  rw [integral_congr_ae (hae.mono fun x hx ↦ hx), integral_const, probReal_univ, one_smul]

include hβ

/-- **Boundary KL Pythagoras**: for every probability law `Q ≪ ν` whose mean is the face-family
mean `m_A(v)`, `D(Q ‖ ν) = D(Q ‖ P^A_v) + D(P^A_v ‖ ν)`. -/
theorem klDiv_eq_add_faceFamily (v : J → ℝ) (Q : Measure X) [IsProbabilityMeasure Q] (hQν : Q ≪ ν)
    (hQM : (fun i ↦ ∫ x, S i x ∂Q) =
      meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 v) :
    klDiv Q ν = klDiv Q (Qface v) + klDiv (Qface v) ν := by
  have hAm := measurableSet_of_eq_faceFibre hS hA
  have hνA := isProbabilityMeasure_faceMeasure_of_real_pos ν hp
  have hQf := isProbabilityMeasure_family hS (faceMeasure ν A) v
  -- `Q` is carried by the face
  have hQA : Q Aᶜ = 0 := by
    rw [hA]
    exact compl_eq_zero_of_mean_face ν hS Q hQν hβ
      (by rw [hQM]; exact dotJ_meanMap_faceFamily hS ν hA hp v)
  have hQF : Q ≪ faceMeasure ν A := absolutelyContinuous_faceMeasure ν hAm hQν hQA
  -- the interior Pythagoras of the face family on `ν_A`
  have hpy := klDiv_eq_add_of_mean measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos (faceMeasure ν A)) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS one_pos
    v Q hQM
  rw [familyMeasure_zero_eq hS (faceMeasure ν A)] at hpy
  -- the chain rules
  have h1 := klDiv_eq_klDiv_faceMeasure_add ν hAm hp Q hQF
  have h2 := klDiv_eq_klDiv_faceMeasure_add ν hAm hp (Qface v)
    (faceFamily_absolutelyContinuous hS ν hp v)
  rw [h1, h2, hpy, add_assoc]

omit hβ in
/-- The face family member has finite information. -/
theorem klDiv_faceFamily_ne_top (v : J → ℝ) : klDiv (Qface v) ν ≠ ⊤ := by
  have hAm := measurableSet_of_eq_faceFibre hS hA
  have hνA := isProbabilityMeasure_faceMeasure_of_real_pos ν hp
  have hQf := isProbabilityMeasure_family hS (faceMeasure ν A) v
  rw [klDiv_eq_klDiv_faceMeasure_add ν hAm hp (Qface v)
    (faceFamily_absolutelyContinuous hS ν hp v)]
  exact ENNReal.add_ne_top.2
    ⟨klDiv_familyMeasure_ne_top hS (faceMeasure ν A) v, ENNReal.ofReal_ne_top⟩

/-- **The face family member is the information projection**: `D(P^A_v ‖ ν) ≤ D(Q ‖ ν)` for every
law `Q ≪ ν` with the same mean. -/
theorem klDiv_faceFamily_le (v : J → ℝ) (Q : Measure X) [IsProbabilityMeasure Q] (hQν : Q ≪ ν)
    (hQM : (fun i ↦ ∫ x, S i x ∂Q) =
      meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 v) :
    klDiv (Qface v) ν ≤ klDiv Q ν := by
  rw [klDiv_eq_add_faceFamily hS ν hβ hA hp v Q hQν hQM]
  exact le_add_self

/-- **Uniqueness of the boundary information projection**: equality of informations forces
`Q = P^A_v`. -/
theorem eq_faceFamily_of_klDiv_eq (v : J → ℝ) (Q : Measure X) [IsProbabilityMeasure Q]
    (hQν : Q ≪ ν)
    (hQM : (fun i ↦ ∫ x, S i x ∂Q) =
      meanMap (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 v)
    (heq : klDiv Q ν = klDiv (Qface v) ν) : Q = Qface v := by
  have hνA := isProbabilityMeasure_faceMeasure_of_real_pos ν hp
  have hQf := isProbabilityMeasure_family hS (faceMeasure ν A) v
  have h := klDiv_eq_add_faceFamily hS ν hβ hA hp v Q hQν hQM
  rw [heq] at h
  have hfin := klDiv_faceFamily_ne_top hS ν hA hp v
  have h0 : klDiv Q (Qface v) = 0 := by
    have key : klDiv (Qface v) ν + 0 = klDiv (Qface v) ν + klDiv Q (Qface v) := by
      rw [add_zero, add_comm]
      exact h
    exact ((ENNReal.add_right_inj hfin).1 key).symm
  exact klDiv_eq_zero_iff.1 h0

end Face

end Laplace.Multi
