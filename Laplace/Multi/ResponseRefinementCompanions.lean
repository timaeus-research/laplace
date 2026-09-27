/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFeatureRefinement
import Laplace.Multi.ResponseFiniteSaturation

/-!
# Companions of the refinement ladder

* `Refines_trans`: refinement is transitive;
* `responseProjection_mean_self`: the entropy projection is idempotent — the response of the
  response of a mean is itself;
* `integral_eq_of_ae_affine`: two laws absolutely continuous with respect to `ν` with the same
  feature means integrate every `ν`-a.e. affine function of the features alike;
* **`responseProjection_eq_self_of_spansAffine`**: for a saturated family (every bounded function
  is `ν`-a.e. affine in the features) the entropy response of a data law `D ≪ ν` of finite rate is
  `D` itself, `R_D = D` — the journey ends at the data, and the refinement ladder terminates.
-/

open MeasureTheory InformationTheory

namespace Laplace.Multi

section Companions

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- Refinement is transitive. -/
theorem Refines_trans {K L : Type*} [Fintype K] [Fintype L] {T : K → X → ℝ} {U : L → X → ℝ}
    (hST : Refines S T ν) (hTU : Refines T U ν) : Refines S U ν := by
  intro j
  obtain ⟨b, c, hbc⟩ := hST j
  choose C d hCd using hTU
  refine ⟨fun l ↦ ∑ k, b k * C k l, c + ∑ k, b k * d k, ?_⟩
  filter_upwards [hbc, Filter.eventually_all.2 hCd] with x hx hx'
  rw [hx]
  simp only [dirLoss, hx', mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring_nf

include hS in
/-- **The entropy projection is idempotent**: the response of the mean of a response is that
response. -/
theorem responseProjection_mean_self {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    responseProjection hS ν (fun i ↦ ∫ x, S i x ∂responseProjection hS ν M) =
      responseProjection hS ν M := by
  rw [(responseProjection_spec hS ν hfin).2.1]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
include hS in
/-- Two laws `≪ ν` with the same feature means integrate every `ν`-a.e. affine function of the
features alike. -/
theorem integral_eq_of_ae_affine (ρ₁ ρ₂ : Measure X) [IsProbabilityMeasure ρ₁]
    [IsProbabilityMeasure ρ₂] (h₁ : ρ₁ ≪ ν) (h₂ : ρ₂ ≪ ν)
    (hmean : ∀ j, ∫ x, S j x ∂ρ₁ = ∫ x, S j x ∂ρ₂) {g : X → ℝ} {b : J → ℝ} {c : ℝ}
    (hg : g =ᵐ[ν] fun x ↦ dirLoss S b x + c) : ∫ x, g x ∂ρ₁ = ∫ x, g x ∂ρ₂ := by
  have e : ∀ ρ : Measure X, [IsProbabilityMeasure ρ] → ρ ≪ ν →
      ∫ x, g x ∂ρ = ∑ j, b j * ∫ x, S j x ∂ρ + c := by
    intro ρ _ hρ
    rw [integral_congr_ae (hρ.ae_eq hg)]
    have hi : Integrable (fun x ↦ dirLoss S b x) ρ := integrable_of_bdd_prob ρ (bdd_dirLoss hS b)
    rw [integral_add hi (integrable_const c), integral_const, probReal_univ, one_smul]
    congr 1
    unfold dirLoss
    rw [integral_finsetSum _ fun j _ ↦ (integrable_of_bdd_prob ρ (hS j)).const_mul (b j)]
    exact Finset.sum_congr rfl fun j _ ↦ integral_const_mul _ _
  rw [e ρ₁ h₁, e ρ₂ h₂]
  simp only [hmean]

include hS in
/-- **Saturation reaches the data**: for a saturated family every data law `D ≪ ν` of finite rate
is its own entropy response, `R_D = D`. -/
theorem responseProjection_eq_self_of_spansAffine (hspan : SpansAffine S ν) (D : Measure X)
    [IsProbabilityMeasure D] (hDν : D ≪ ν)
    (hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤) :
    responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D) = D := by
  obtain ⟨hR, hmean, hkl, -⟩ := responseProjection_spec hS ν hfin
  have hRν : responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D) ≪ ν := by
    by_contra h
    rw [klDiv_of_not_ac h] at hkl
    exact hfin hkl.symm
  refine Measure.ext fun A hA ↦ ?_
  have hind : Bdd (A.indicator (1 : X → ℝ)) :=
    ⟨measurable_const.indicator hA, 1, fun x ↦ by
      classical
      rw [Set.indicator_apply]
      split_ifs <;> simp⟩
  obtain ⟨b, c, hbc⟩ := hspan _ hind
  have h := integral_eq_of_ae_affine hS ν (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)) D hRν
    hDν (fun j ↦ congrFun hmean j) hbc
  rw [integral_indicator_one hA, integral_indicator_one hA, measureReal_def, measureReal_def] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h

end Companions

end Laplace.Multi
