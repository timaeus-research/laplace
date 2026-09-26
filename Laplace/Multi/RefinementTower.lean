/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AtlasRefinement

/-!
# The refinement tower: information resolution

For a data law `D` of finite information, a coarse statistic `S = T S' + b` of a fine statistic
`S'`, and interior coarse response, the four identities

* `KL(D ‖ ν) = KL(D ‖ Π_S(M_D)) + 𝓘_S(M_D)` and `KL(D ‖ ν) = KL(D ‖ Π_{S'}(M'_D)) + 𝓘_{S'}(M'_D)`
  (the base splits into invisible and visible information for each statistic),
* `KL(D ‖ Π_S(M_D)) = KL(D ‖ Π_{S'}(M'_D)) + KL(Π_{S'}(M'_D) ‖ Π_S(M_D))` (refinement of the
  error),
* `𝓘_{S'}(M'_D) = 𝓘_S(M_D) + KL(Π_{S'}(M'_D) ‖ Π_S(M_D))` (refinement of the visible information)

are packaged as `refinement_tower`: refining the features converts invisible information into
visible information, by exactly the divergence between the two reconstructions. This is the fibre-
side complement of the response-side map.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J K : Type*} [Fintype J] [Nonempty J]
  [Fintype K] [Nonempty K] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) {S' : K → X → ℝ}
  (hS' : ∀ k, Bdd (S' k)) (ν : Measure X) [IsProbabilityMeasure ν] {T : J → K → ℝ} {b : J → ℝ}
  (hT : ∀ j x, S j x = ∑ k, T j k * S' k x + b j)
include hS hS' hT

/-- **The refinement tower** (see the module docstring). -/
theorem refinement_tower (D : Measure X) [IsProbabilityMeasure D] (hDkl : klDiv D ν ≠ ⊤)
    (hrel : (fun j ↦ ∫ x, S j x ∂D) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    klDiv D ν = klDiv D (responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D)) +
        genRate ν S (fun j ↦ ∫ x, S j x ∂D) ∧
      klDiv D ν = klDiv D (responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂D)) +
        genRate ν S' (fun k ↦ ∫ x, S' k x ∂D) ∧
      klDiv D (responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D)) =
        klDiv D (responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂D)) +
          klDiv (responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂D))
            (responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D)) ∧
      (genRate ν S' (fun k ↦ ∫ x, S' k x ∂D)).toReal =
        (genRate ν S (fun j ↦ ∫ x, S j x ∂D)).toReal +
          (klDiv (responseProjection hS' ν (fun k ↦ ∫ x, S' k x ∂D))
            (responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D))).toReal := by
  have hfinS : genRate ν S (fun j ↦ ∫ x, S j x ∂D) ≠ ⊤ := fun h ↦
    hDkl (klDiv_eq_top_of_genRate_eq_top hS ν D h)
  have hfinS' : genRate ν S' (fun k ↦ ∫ x, S' k x ∂D) ≠ ⊤ := fun h ↦
    hDkl (klDiv_eq_top_of_genRate_eq_top hS' ν D h)
  obtain ⟨-, -, -, hpythS⟩ := responseProjection_spec hS ν hfinS
  obtain ⟨-, -, -, hpythS'⟩ := responseProjection_spec hS' ν hfinS'
  exact ⟨hpythS D inferInstance rfl, hpythS' D inferInstance rfl,
    klDiv_responseProjection_coarse_eq hS hS' ν hT D hDkl hrel,
    genRate_fine_eq_coarse_add hS hS' ν hT D hDkl hrel⟩

end Laplace.Multi
