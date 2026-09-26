/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CurveLength
import Laplace.Multi.SecondOrderTransport
import Laplace.Multi.DataRetraction

/-!
# Whole-law transport in `L¹`: the Bochner fundamental theorem for the reconstruction

Along a `C¹` curve of interior responses the reconstruction density moves in `L¹(ν)` by the
Bochner integral of its derivative, `[q_{M+γ(1)}] − [q_{M+γ(0)}] = ∫₀¹ Dp_{M+γ(t)} γ'(t) dt`
(`reconstructionL1_curve_sub_eq_integral`), and along the moment atlas from the featureless law,
`[q_{M}] − [q_{m₀}] = ∫₀¹ [q_{M_s} ℓ_{M_s, M − m₀}] ds`
(`reconstructionL1_sub_featureless_eq_integral_atlas`): the law-valued form of the whole-law
transport.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- **The Bochner fundamental theorem for the reconstruction along a `C¹` curve of interior
responses**: `[q_{M+γ(1)}] − [q_{M+γ(0)}] = ∫₀¹ Dp_{M+γ(t)} γ'(t) dt` in `L¹(ν)`. -/
theorem reconstructionL1_curve_sub_eq_integral {M : J → ℝ} {γ γ' : ℝ → 𝕍}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc (0 : ℝ) 1))
    (hint : ∀ t ∈ Icc (0 : ℝ) 1,
      M + (γ t : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    reconstructionL1 hS ν (M + (γ 1 : J → ℝ)) - reconstructionL1 hS ν (M + (γ 0 : J → ℝ)) =
      ∫ t in (0 : ℝ)..1, reconstructionDeriv hS ν (M + (γ t : J → ℝ)) (γ' t) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ reconstructionL1 hS ν (M + (γ s : J → ℝ)))
      (reconstructionDeriv hS ν (M + (γ t : J → ℝ)) (γ' t)) t := fun t ht ↦ by
    rw [uIcc_of_le zero_le_one] at ht
    exact hasDerivAt_reconstructionL1_curve hS ν (hγ t ht) (hint t ht)
  have hγc : ContinuousOn γ (Icc (0 : ℝ) 1) := fun t ht ↦
    (hγ t ht).continuousAt.continuousWithinAt
  have hpath : ContinuousOn (fun t ↦ M + (γ t : J → ℝ)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.add (continuous_subtype_val.comp_continuousOn hγc)
  have hD : ContinuousOn (fun t ↦ reconstructionDeriv hS ν (M + (γ t : J → ℝ))) (Icc (0 : ℝ) 1) :=
    fun t ht ↦ ContinuousWithinAt.comp (g := fun M' ↦ reconstructionDeriv hS ν M')
      (f := fun t ↦ M + (γ t : J → ℝ)) (continuousWithinAt_reconstructionDeriv hS ν (hint t ht))
      (hpath t ht) fun s hs ↦ hint s hs
  have hDγ : ContinuousOn (fun t ↦ reconstructionDeriv hS ν (M + (γ t : J → ℝ)) (γ' t))
      (Icc (0 : ℝ) 1) := hD.clm_apply hγ'
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hDγ.intervalIntegrable_of_Icc zero_le_one)).symm

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- The atlas from the featureless law, as a curve in the direction subspace. -/
theorem hasDerivAt_dirProjL_atlasPath (s : ℝ) :
    HasDerivAt (fun s ↦ dirProjL S ν (atlasPath S ν M s - m₀))
      (atlasInc hS ν (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel)) s := by
  have h := (dirProjL S ν).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_atlasPath ν (S := S) (M := M) s).sub_const m₀)
  refine h.congr_deriv (Subtype.ext ?_)
  rw [atlasInc_coe]
  exact dirProjL_of_mem ν (sub_mem_dirSpan_of_genRate_ne_top hS ν
    (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel))

/-- **Whole-law transport along the atlas, in `L¹`**:
`[q_M] − [q_{m₀}] = ∫₀¹ [q_{M_s} ℓ_{M_s, M − m₀}] ds`. -/
theorem reconstructionL1_sub_featureless_eq_integral_atlas :
    reconstructionL1 hS ν M - reconstructionL1 hS ν m₀ =
      ∫ s in (0 : ℝ)..1, reconstructionDeriv hS ν (atlasPath S ν M s)
        (atlasInc hS ν (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel)) := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  have hcoe : ∀ s, m₀ + (dirProjL S ν (atlasPath S ν M s - m₀) : J → ℝ) = atlasPath S ν M s :=
    fun s ↦ by rw [dirProjL_of_mem ν (atlasPath_sub_mem_dirSpan hS ν hfin s), add_sub_cancel]
  have h := reconstructionL1_curve_sub_eq_integral hS ν (M := m₀)
    (γ := fun s ↦ dirProjL S ν (atlasPath S ν M s - m₀)) (γ' := fun _ ↦ atlasInc hS ν hfin)
    (fun t _ ↦ hasDerivAt_dirProjL_atlasPath hS ν hrel t) continuousOn_const
    (fun t ht ↦ by rw [hcoe]; exact atlas_mem_intrinsicInterior' hS ν hfin hrel ht.1 ht.2)
  rw [hcoe 1, hcoe 0, atlasPath_one, atlasPath_zero] at h
  simp only [hcoe] at h
  exact h

end Laplace.Multi
