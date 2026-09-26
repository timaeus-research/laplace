/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TargetPythagoras
import Laplace.Multi.PathEnergy

/-!
# Refining the atlas: a coarser affine statistic

Let `S = T S' + b` be an affine image of a finer statistic `S'`. The coarse exponential family sits
inside the fine one (`familyMeasure_coarse_eq_fine`), a fine family member is its own fine
projection (`responseProjection_mean_familyMeasure`), and for a data law `D` of finite information
whose coarse response is interior,

  `KL(D ‖ Π_S(M_D)) = KL(D ‖ Π_{S'}(M'_D)) + KL(Π_{S'}(M'_D) ‖ Π_S(M_D))`
                                                    (`klDiv_responseProjection_coarse_eq`)
  `𝓘_{S'}(M'_D) = 𝓘_S(M_D) + KL(Π_{S'}(M'_D) ‖ Π_S(M_D))`      (`genRate_fine_eq_coarse_add`).

Refining the features never loses visible information, the gain being the divergence between the
two representatives; the total reconstruction error decreases by exactly the same amount. (The
fibre information decreases and the marginal residual has no fixed sign, as the observational tower
`klDiv_statisticLift_tower` shows.)
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Affine

variable {X : Type*} [MeasurableSpace X] {J K : Type*} [Fintype J] [Fintype K]
  {S : J → X → ℝ} {S' : K → X → ℝ} {T : J → K → ℝ} {b : J → ℝ}
  (hT : ∀ j x, S j x = ∑ k, T j k * S' k x + b j)
include hT

omit [MeasurableSpace X] in
/-- The coarse direction loss is a fine direction loss plus a constant. -/
theorem dirLoss_affine_coarse (θ : J → ℝ) (x : X) :
    dirLoss S θ x = dirLoss S' (fun k ↦ ∑ j, θ j * T j k) x + dotJ θ b := by
  simp only [dirLoss, dotJ, hT, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end Affine

section Family

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J K : Type*} [Fintype J] [Nonempty J]
  [Fintype K] [Nonempty K] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) {S' : K → X → ℝ}
  (hS' : ∀ k, Bdd (S' k)) (ν : Measure X) [IsProbabilityMeasure ν] {T : J → K → ℝ} {b : J → ℝ}
  (hT : ∀ j x, S j x = ∑ k, T j k * S' k x + b j)
include hS hS' hT

omit [Nonempty J] [Nonempty K] in
/-- **The coarse family sits inside the fine one**: `P^S_θ = P^{S'}_{Tᵀθ}`. -/
theorem familyMeasure_coarse_eq_fine (θ : J → ℝ) :
    familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ =
      familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 (fun k ↦ ∑ j, θ j * T j k) := by
  rw [familyMeasure_one_zero_eq_tilted hS ν, familyMeasure_one_zero_eq_tilted hS' ν]
  have e : (fun x ↦ -1 * dirLoss S θ x) =
      fun x ↦ -1 * dirLoss S' (fun k ↦ ∑ j, θ j * T j k) x + (-dotJ θ b) := by
    funext x
    rw [dirLoss_affine_coarse hT]
    ring
  rw [e, tilted_add_const]

omit hS hT in
/-- **A fine family member is its own projection**: `Π_{S'}(E_{P'_θ} S') = P'_θ`. -/
theorem responseProjection_mean_familyMeasure (θ : K → ℝ) :
    responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂familyMeasure ν (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S' 1 θ) = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ := by
  rw [mean_familyMeasure_one_zero hS' ν θ]
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ) :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS' (t := 1) θ
  have hfin : genRate ν S' (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ) ≠ ⊤ := by
    have h := genRate_meanMap_neg hS' ν (-θ)
    rw [neg_neg] at h
    rw [h]
    exact ENNReal.ofReal_ne_top
  obtain ⟨hQP, -, -, hpyth⟩ := responseProjection_spec hS' ν hfin
  have h := hpyth (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ) hP
    (mean_familyMeasure_one_zero hS' ν θ)
  -- `KL(P'_θ ‖ ν) = 𝓘(m(θ))`
  have hkl : klDiv (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ) ν =
      genRate ν S' (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ) := by
    rw [klDiv_familyMeasure_featureless hS' ν]
    have h2 := genRate_meanMap_neg hS' ν (-θ)
    rw [neg_neg, dotJ_neg_left] at h2
    rw [h2]
  rw [hkl] at h
  have h0 : klDiv (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ)
      (responseProjection hS' ν (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ)) = 0 := by
    have h' : (0 : ℝ≥0∞) + genRate ν S' (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ) =
        klDiv (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ)
          (responseProjection hS' ν (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ)) +
          genRate ν S' (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ) := by
      rw [zero_add]
      exact h
    exact ((ENNReal.add_left_inj hfin).1 h').symm
  have := hQP
  exact (klDiv_eq_zero_iff.1 h0).symm

/-- **Refinement of the reconstruction error**: for finite-information `D` with interior coarse
response, `KL(D ‖ Π_S(M_D)) = KL(D ‖ Π_{S'}(M'_D)) + KL(Π_{S'}(M'_D) ‖ Π_S(M_D))`. -/
theorem klDiv_responseProjection_coarse_eq (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤)
    (hrel : (fun j ↦ ∫ x, S j x ∂D) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv D (responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D)) =
      klDiv D (responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂D)) +
        klDiv (responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂D))
          (responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D)) := by
  -- the coarse representative is a fine family member
  obtain ⟨θ', hθ'⟩ : ∃ θ' : K → ℝ, responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D) =
      familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S' 1 θ' :=
    ⟨fun k ↦ ∑ j, (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (fun j ↦ ∫ x, S j x ∂D) : J → ℝ) j * T j k, by
      rw [responseProjection_eq_familyMeasure_responseTheta hS ν hrel,
        familyMeasure_coarse_eq_fine hS hS' ν hT]⟩
  -- its fine response `N` is interior and `Π'(N)` is the member
  obtain ⟨N, hN⟩ : ∃ N : K → ℝ, N = fun k ↦ ∫ x, S' k x ∂familyMeasure ν (fun _ ↦ (1 : ℝ))
    (fun _ ↦ (0 : ℝ)) S' 1 θ' := ⟨_, rfl⟩
  have hNrel : N ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S') := by
    rw [hN, mean_familyMeasure_one_zero hS' ν θ', ← range_meanMap_eq_intrinsicInterior_momentBody
      measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS']
    exact ⟨θ', rfl⟩
  have hPN : responseProjection hS' ν N = responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D) := by
    rw [hN, responseProjection_mean_familyMeasure hS' ν θ', hθ']
  have hT' := klDiv_responseProjection_target_eq hS' ν D hDkl hNrel
  have hsplit := klDiv_responseProjection_eq_statisticLift_add_map' hS' ν D hDkl
  rw [hPN] at hT'
  rw [hT', ← hsplit]

/-- **Refinement of the visible information**: `𝓘_{S'}(M'_D) = 𝓘_S(M_D) + KL(Π_{S'}(M'_D) ‖
    Π_S(M_D))`. -/
theorem genRate_fine_eq_coarse_add (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤)
    (hrel : (fun j ↦ ∫ x, S j x ∂D) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (genRate ν S' (fun k ↦ ∫ x, S' k x ∂D)).toReal =
      (genRate ν S (fun j ↦ ∫ x, S j x ∂D)).toReal +
        (klDiv (responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂D))
          (responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D))).toReal := by
  have hfinS : genRate ν S (fun j ↦ ∫ x, S j x ∂D) ≠ ⊤ := fun h ↦
    hDkl (klDiv_eq_top_of_genRate_eq_top hS ν D h)
  have hfinS' : genRate ν S' (fun k ↦ ∫ x, S' k x ∂D) ≠ ⊤ := fun h ↦
    hDkl (klDiv_eq_top_of_genRate_eq_top hS' ν D h)
  obtain ⟨-, -, -, hpS⟩ := responseProjection_spec hS ν hfinS
  obtain ⟨-, -, -, hpS'⟩ := responseProjection_spec hS' ν hfinS'
  have h1 := hpS D inferInstance rfl
  have h2 := hpS' D inferInstance rfl
  have h3 := klDiv_responseProjection_coarse_eq hS hS' ν hT D hDkl hrel
  have hne1 : klDiv D (responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h1
    exact hDkl h1
  have hne2 : klDiv D (responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂D)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h3
    exact hne1 h3
  have hne3 : klDiv (responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂D))
      (responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D)) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at h3
    exact hne1 h3
  have e1 := congrArg ENNReal.toReal h1
  have e2 := congrArg ENNReal.toReal h2
  have e3 := congrArg ENNReal.toReal h3
  rw [ENNReal.toReal_add hne1 hfinS] at e1
  rw [ENNReal.toReal_add hne2 hfinS'] at e2
  rw [ENNReal.toReal_add hne2 hne3] at e3
  linarith

end Family

end Laplace.Multi
