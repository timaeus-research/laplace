/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ExtremeMeanSupport

/-!
# Rigidity II: charged polytopes are exactly the compactly liftable moment bodies

If a compact set `K` of `L¹` probability densities has mean image the whole moment body, then the
extreme points of the body are finitely many (distinct extreme means lift to `2`-separated
densities, and a compact set has no infinite `2`-separated subset), each is charged, and by
Krein–Milman the body is their convex hull (`exists_charged_generators_of_compact_mean_lift`).
Together with the polyhedral completion this gives the **characterisation**
(`exists_charged_polytope_iff_exists_compact_mean_lift`): a compact moment body admits a compact
(equivalently, continuous) absolutely-continuous mean section if and only if it is a polytope with
charged vertices. The hypotheses of the completion are therefore necessary, not merely convenient.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Rigidity

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **A compact mean lift forces finitely many extreme points.** -/
theorem finite_extremePoints_of_compact_mean_lift {K : Set (X →₁[ν] ℝ)} (hK : IsCompact K)
    (hKp : K ⊆ probL1 ν) (himage : momentBody ν (fun _ ↦ (1 : ℝ)) S ⊆ meanL1 hS ν '' K) :
    ((momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ).Finite := by
  by_contra hinf
  have hinf' : ((momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ).Infinite := hinf
  obtain ⟨u, hu⟩ : ∃ u : ℕ → (momentBody ν (fun _ ↦ (1 : ℝ)) S).extremePoints ℝ,
      Function.Injective u := ⟨hinf'.natEmbedding _, (hinf'.natEmbedding _).injective⟩
  have hlift : ∀ n, ∃ f ∈ K, meanL1 hS ν f = (u n : J → ℝ) := fun n ↦ by
    obtain ⟨f, hf, hfe⟩ := himage (extremePoints_subset (u n).2)
    exact ⟨f, hf, hfe⟩
  choose g hgK hge using hlift
  have hsep : ∀ n m, n ≠ m → dist (g n) (g m) = 2 := fun n m hnm ↦ by
    rw [dist_eq_norm]
    exact norm_sub_eq_two_of_mean_extreme hS ν (hKp (hgK n)) (hKp (hgK m)) (u n).2 (u m).2
      (fun h ↦ hnm (hu (Subtype.ext h))) (hge n) (hge m)
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hgK
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (1 / 2) (by norm_num)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (by omega)
  have h3 := hsep (φ N) (φ (N + 1)) (hφ.injective.ne (by omega))
  have h4 := dist_triangle (g (φ N)) a (g (φ (N + 1)))
  rw [dist_comm a] at h4
  simp only [Function.comp_apply] at h1 h2
  linarith

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **The extreme points of a compactly lifted body are charged and generate it.** -/
theorem exists_charged_generators_of_compact_mean_lift {K : Set (X →₁[ν] ℝ)} (hK : IsCompact K)
    (hKp : K ⊆ probL1 ν) (himage : momentBody ν (fun _ ↦ (1 : ℝ)) S ⊆ meanL1 hS ν '' K) :
    ∃ V : Finset (J → ℝ), momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)) ∧
      ∀ v ∈ V, 0 < ν.real (statFibre S v) := by
  have hfin := finite_extremePoints_of_compact_mean_lift hS ν hK hKp himage
  refine ⟨hfin.toFinset, ?_, fun v hv ↦ ?_⟩
  · rw [hfin.coe_toFinset]
    have hKM := closure_convexHull_extremePoints
      (isCompact_momentBody (μ := ν) measurable_const (fun _ ↦ one_pos) hS)
      (convex_momentBody (μ := ν) (π := fun _ ↦ (1 : ℝ)) S)
    rw [(hfin.isCompact_convexHull (𝕜 := ℝ)).isClosed.closure_eq] at hKM
    exact hKM.symm
  · rw [hfin.mem_toFinset] at hv
    obtain ⟨f, hf, hfe⟩ := himage (extremePoints_subset hv)
    exact statFibre_pos_of_mean_extreme hS ν (hKp hf) hv hfe

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- A continuous absolutely-continuous mean section on the moment body forces a charged polytope. -/
theorem exists_charged_generators_of_continuous_section (σ : (J → ℝ) → (X →₁[ν] ℝ))
    (hσ : ContinuousOn σ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hσp : ∀ M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, σ M ∈ probL1 ν)
    (hσm : ∀ M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, meanL1 hS ν (σ M) = M) :
    ∃ V : Finset (J → ℝ), momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)) ∧
      ∀ v ∈ V, 0 < ν.real (statFibre S v) :=
  exists_charged_generators_of_compact_mean_lift hS ν
    ((isCompact_momentBody (μ := ν) measurable_const (fun _ ↦ one_pos) hS).image_of_continuousOn hσ)
    (by rintro _ ⟨M, hM, rfl⟩; exact hσp M hM)
    fun M hM ↦ ⟨σ M, mem_image_of_mem σ hM, hσm M hM⟩

set_option linter.unusedFintypeInType false in
/-- **Characterisation**: the moment body admits a compact absolutely-continuous mean lift if and
only if it is a polytope with charged vertices. -/
theorem exists_charged_polytope_iff_exists_compact_mean_lift :
    (∃ V : Finset (J → ℝ), momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)) ∧
        ∀ v ∈ V, 0 < ν.real (statFibre S v)) ↔
      ∃ K : Set (X →₁[ν] ℝ), IsCompact K ∧ K ⊆ probL1 ν ∧
        meanL1 hS ν '' K = momentBody ν (fun _ ↦ (1 : ℝ)) S := by
  constructor
  · rintro ⟨V, hpoly, hV⟩
    have hne : (V : Set (J → ℝ)).Nonempty := by
      have hm := mean_mem_momentBody_general hS ν
      rw [hpoly] at hm
      exact convexHull_nonempty_iff.1 ⟨_, hm⟩
    have : Nonempty V := hne.to_subtype
    refine ⟨completedFamilyL1 hS ν V, isCompact_completedFamilyL1 hS ν V hV,
      completedFamilyL1_subset_probL1 hS ν V hV, ?_⟩
    rw [hpoly]
    ext M
    constructor
    · rintro ⟨_, ⟨M', hM', rfl⟩, rfl⟩
      rw [meanL1_projL1 hS ν (genRate_ne_top_of_mem_convexHull_vertices hS ν V hV hM')]
      exact hM'
    · intro hM
      exact ⟨projL1 hS ν M, ⟨M, hM, rfl⟩,
        meanL1_projL1 hS ν (genRate_ne_top_of_mem_convexHull_vertices hS ν V hV hM)⟩
  · rintro ⟨K, hK, hKp, himage⟩
    exact exists_charged_generators_of_compact_mean_lift hS ν hK hKp himage.symm.subset

end Rigidity

end Laplace.Multi
