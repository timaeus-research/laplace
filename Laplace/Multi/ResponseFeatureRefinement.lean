/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DataResponseMap
import Laplace.Multi.PinskerObservable

/-!
# Nested features: the information ladder from the featureless law to the data

With fixed features the response journey ends at the entropy response `R_D`, not at the data law
`D`; the defect `KL(D‖R_D)` is invisible to the features. Refining the features supplies the rest of
the way, and the accounting is exact.

Let `T : K → X → ℝ` **refine** `S : J → X → ℝ`: every `S`-feature is (`ν`-a.e.) an affine function
of the `T`-features (`Refines`). Then any two laws with the same `T`-means have the same `S`-means
(`integral_eq_of_refines`), so the `T`-response `R_T` of a data law `D` has the `S`-mean of `D`, and
the two Pythagorean identities of the entropy projections combine into

* **the refinement ladder** (`klDiv_data_responseProjection_refine`):
  `KL(D‖R_S) = KL(D‖R_T) + KL(R_T‖R_S)` — the information newly resolved by the richer features is
  exactly the reduction of the invisible information;
* **the acquired information** (`klDiv_responseProjection_refine`):
  `KL(R_T‖ν) = KL(R_S‖ν) + KL(R_T‖R_S)`;
* the finiteness of the coarse rate from the fine one (`genRate_ne_top_of_refines`);
* **the observable certificate** (`sq_integral_sub_responseProjection_refine_le`): for every bounded
  observable and every affine feature predictor `⟨a, S⟩ + c` with `|F − ⟨a,S⟩ − c| ≤ L`,
  `(E_{R_T}F − E_{R_S}F)² ≤ 2 L² KL(R_T‖R_S)` — only the part of an observable that the coarse
  features do not explain can detect the information the refinement resolves.
-/

open MeasureTheory InformationTheory

namespace Laplace.Multi

section Refinement

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {K : Type*} [Fintype K] [Nonempty K] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  {T : K → X → ℝ} (hT : ∀ k, Bdd (T k)) (ν : Measure X) [IsProbabilityMeasure ν]

/-- `T` refines `S`: every `S`-feature is `ν`-a.e. an affine function of the `T`-features. -/
def Refines (S : J → X → ℝ) (T : K → X → ℝ) (ν : Measure X) : Prop :=
  ∀ j, ∃ (b : K → ℝ) (c : ℝ), S j =ᵐ[ν] fun x ↦ dirLoss T b x + c

omit [Nonempty X] [Fintype J] [Nonempty J] [Nonempty K] [IsProbabilityMeasure ν] in
include hT in
/-- Two laws with the same `T`-means have the same `S`-means when `T` refines `S`. -/
theorem integral_eq_of_refines (hST : Refines S T ν) (ρ₁ ρ₂ : Measure X) [IsProbabilityMeasure ρ₁]
    [IsProbabilityMeasure ρ₂] (h₁ : ρ₁ ≪ ν) (h₂ : ρ₂ ≪ ν)
    (hmean : ∀ k, ∫ x, T k x ∂ρ₁ = ∫ x, T k x ∂ρ₂) (j : J) :
    ∫ x, S j x ∂ρ₁ = ∫ x, S j x ∂ρ₂ := by
  obtain ⟨b, c, hbc⟩ := hST j
  have e : ∀ ρ : Measure X, [IsProbabilityMeasure ρ] → ρ ≪ ν →
      ∫ x, S j x ∂ρ = ∑ k, b k * ∫ x, T k x ∂ρ + c := by
    intro ρ _ hρ
    rw [integral_congr_ae (hρ.ae_eq hbc)]
    have hi : Integrable (fun x ↦ dirLoss T b x) ρ := integrable_of_bdd_prob ρ (bdd_dirLoss hT b)
    rw [integral_add hi (integrable_const c), integral_const, probReal_univ, one_smul]
    congr 1
    unfold dirLoss
    rw [integral_finsetSum _ fun k _ ↦ (integrable_of_bdd_prob ρ (hT k)).const_mul (b k)]
    exact Finset.sum_congr rfl fun k _ ↦ integral_const_mul _ _
  rw [e ρ₁ h₁, e ρ₂ h₂]
  simp only [hmean]

variable (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν)
  (hfinT : genRate ν T (fun k ↦ ∫ x, T k x ∂D) ≠ ⊤)

/-- The `T`-mean of the data law. -/
local notation "mT" => (fun k : K ↦ ∫ x, T k x ∂D)

/-- The `S`-mean of the data law. -/
local notation "mS" => (fun j : J ↦ ∫ x, S j x ∂D)

include hT hDν hfinT

omit [IsProbabilityMeasure D] hDν in
/-- The `T`-response is a probability law. -/
theorem isProbabilityMeasure_responseProjection_T :
    IsProbabilityMeasure (responseProjection hT ν mT) :=
  (responseProjection_spec hT ν hfinT).1

omit [IsProbabilityMeasure D] hDν in
/-- The `T`-response is absolutely continuous with respect to the base law. -/
theorem responseProjection_T_absolutelyContinuous : responseProjection hT ν mT ≪ ν := by
  by_contra h
  have := (responseProjection_spec hT ν hfinT).2.2.1
  rw [klDiv_of_not_ac h] at this
  exact hfinT this.symm

omit [Fintype J] [Nonempty J] in
/-- **The `T`-response has the `S`-mean of the data** when `T` refines `S`. -/
theorem mean_S_responseProjection_T (hST : Refines S T ν) :
    (fun j : J ↦ ∫ x, S j x ∂responseProjection hT ν mT) = mS := by
  have := isProbabilityMeasure_responseProjection_T hT ν D hfinT
  funext j
  refine integral_eq_of_refines hT ν hST _ D
    (responseProjection_T_absolutelyContinuous hT ν D hfinT) hDν (fun k ↦ ?_) j
  exact congrFun (responseProjection_spec hT ν hfinT).2.1 k

omit [Nonempty J] in
include hS in
/-- **The coarse rate is finite when the fine rate is**: `𝓘_S(m_S D) ≤ KL(R_T‖ν) = 𝓘_T(m_T D)`. -/
theorem genRate_ne_top_of_refines (hST : Refines S T ν) : genRate ν S mS ≠ ⊤ := by
  have := isProbabilityMeasure_responseProjection_T hT ν D hfinT
  have h := genRate_le_klDiv ν hS (responseProjection hT ν mT)
    (mean_S_responseProjection_T hT ν D hDν hfinT hST)
  rw [(responseProjection_spec hT ν hfinT).2.2.1] at h
  exact ne_top_of_le_ne_top hfinT h

/-- **The acquired information along a refinement**: `KL(R_T‖ν) = KL(R_S‖ν) + KL(R_T‖R_S)`. -/
theorem klDiv_responseProjection_refine (hST : Refines S T ν) :
    klDiv (responseProjection hT ν mT) ν =
      klDiv (responseProjection hS ν mS) ν +
        klDiv (responseProjection hT ν mT) (responseProjection hS ν mS) := by
  have := isProbabilityMeasure_responseProjection_T hT ν D hfinT
  have hfinS := genRate_ne_top_of_refines hS hT ν D hDν hfinT hST
  obtain ⟨_, _, hRS, hpyth⟩ := responseProjection_spec hS ν hfinS
  rw [hpyth _ inferInstance (mean_S_responseProjection_T hT ν D hDν hfinT hST), hRS, add_comm]

/-- **THE REFINEMENT LADDER**: `KL(D‖R_S) = KL(D‖R_T) + KL(R_T‖R_S)` — the information newly
resolved by the richer features is exactly the reduction of the information invisible to the coarse
ones. -/
theorem klDiv_data_responseProjection_refine (hST : Refines S T ν) :
    klDiv D (responseProjection hS ν mS) =
      klDiv D (responseProjection hT ν mT) +
        klDiv (responseProjection hT ν mT) (responseProjection hS ν mS) := by
  have hfinS := genRate_ne_top_of_refines hS hT ν D hDν hfinT hST
  obtain ⟨_, _, hRS, hpythS⟩ := responseProjection_spec hS ν hfinS
  obtain ⟨_, _, hRT, hpythT⟩ := responseProjection_spec hT ν hfinT
  have h1 := hpythS D inferInstance rfl
  have h2 := hpythT D inferInstance rfl
  have h3 := klDiv_responseProjection_refine hS hT ν D hDν hfinT hST
  rw [hRT, hRS] at h3
  -- `KL(D‖R_S) + 𝓘_S = KL(D‖ν) = KL(D‖R_T) + 𝓘_T = KL(D‖R_T) + KL(R_T‖R_S) + 𝓘_S`
  have key : klDiv D (responseProjection hS ν mS) + genRate ν S mS =
      (klDiv D (responseProjection hT ν mT) +
        klDiv (responseProjection hT ν mT) (responseProjection hS ν mS)) +
        genRate ν S mS := by
    rw [← h1, h2, h3]
    ring
  exact WithTop.add_right_cancel hfinS key

/-- **The observable certificate of a refinement**: for a bounded observable and an affine feature
predictor `⟨a, S⟩ + c` with `|F − ⟨a,S⟩ − c| ≤ L`,
`(E_{R_T}F − E_{R_S}F)² / (2L²) ≤ KL(R_T‖R_S)`. -/
theorem sq_integral_sub_responseProjection_refine_le (hST : Refines S T ν) {F : X → ℝ}
    (hF : Bdd F) (a : J → ℝ) {c L : ℝ} (hL : 0 < L)
    (hFc : ∀ x, |F x - dirLoss S a x - c| ≤ L) :
    ENNReal.ofReal (((∫ x, F x ∂responseProjection hT ν mT) -
        ∫ x, F x ∂responseProjection hS ν mS) ^ 2 / (2 * L ^ 2)) ≤
      klDiv (responseProjection hT ν mT) (responseProjection hS ν mS) := by
  have hPT := isProbabilityMeasure_responseProjection_T hT ν D hfinT
  have hfinS := genRate_ne_top_of_refines hS hT ν D hDν hfinT hST
  have hPS : IsProbabilityMeasure (responseProjection hS ν mS) :=
    (responseProjection_spec hS ν hfinS).1
  have hmean := mean_S_responseProjection_T hT ν D hDν hfinT hST
  have hmeanS := (responseProjection_spec hS ν hfinS).2.1
  -- the affine predictor has the same expectation under both responses
  have hpred : ∫ x, dirLoss S a x ∂responseProjection hT ν mT =
      ∫ x, dirLoss S a x ∂responseProjection hS ν mS := by
    unfold dirLoss
    rw [integral_finsetSum _ fun j _ ↦ (integrable_of_bdd_prob _ (hS j)).const_mul (a j),
      integral_finsetSum _ fun j _ ↦ (integrable_of_bdd_prob _ (hS j)).const_mul (a j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_const_mul, integral_const_mul, congrFun hmean j, congrFun hmeanS j]
  have hF' : Bdd fun x ↦ F x - dirLoss S a x := hF.sub (bdd_dirLoss hS a)
  have h := pinsker_observable (responseProjection hT ν mT) (responseProjection hS ν mS)
    hF' hL hFc
  have e : ∀ ρ : Measure X, [IsProbabilityMeasure ρ] →
      ∫ x, (F x - dirLoss S a x) ∂ρ = (∫ x, F x ∂ρ) - ∫ x, dirLoss S a x ∂ρ := fun ρ _ ↦
    integral_sub (integrable_of_bdd_prob ρ hF) (integrable_of_bdd_prob ρ (bdd_dirLoss hS a))
  rw [e, e, hpred] at h
  convert h using 3
  ring

end Refinement

end Laplace.Multi
