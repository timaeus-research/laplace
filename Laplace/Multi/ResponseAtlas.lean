/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolytopeFaceOrder
import Laplace.Multi.HellingerComparison

/-!
# The response atlas of a charged polytope

This is the thin organisational capstone of the charged-polytope programme.  For a reference law
`ν` whose moment body is a polytope `P = conv V` with every vertex fibre charged, the completed
family `M ↦ q_M` (the entropy projections with prescribed response `M`) is described over the whole
body by the structure `ChargedPolytopeAtlas`:

* **strata**: every `M` lies in the relative interior of its minimal face `F_M = conv T_M`, the
  hull of the vertices charged by the vertex section, and `P = ⨆_F ri F`;
* **exposure**: every `F_M` is cut out of `P` by a supporting hyperplane whose fibre is charged;
* **facewise exponential representation**: `q_M` is a bounded exponential tilt of the law
  conditioned on the face fibre;
* **support and incidence**: `q_M ∼ ν|_{S ∈ F_M}` and `q_M ≪ q_N ↔ F_M ⊆ F_N`;
* **topological realisation**: `M ↦ dq_M/dν` is a homeomorphism of `P` onto the compact completed
  family in `L¹`, continuous in Hellinger and in every finite `L^p`, with a uniform density bound;
* **boundary rays**: every `q_M` is the total-variation limit of an explicit natural ray, with the
  exact rate `2B_t/(A + B_t)`.

Rigidity (`CompactMeanLiftRigidity`) says such atlases exist exactly when the moment body carries a
compact absolutely continuous mean lift; `exists_chargedPolytopeAtlas_of_compact_mean_lift` records
this.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Atlas

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]

/-- **Facewise exponential representation**: on a charged polytope every response projection is a
bounded exponential tilt of the reference law conditioned on the fibre of an exposing functional. -/
theorem exists_faceMeasure_tilted_eq_responseProjection
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ∃ u : J → ℝ, ∃ β : ℝ, ∃ θ : J → ℝ, (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u M = β ∧
      0 < ν.real {x | dirLoss S u x = β} ∧
      responseProjection hS ν M =
        (faceMeasure ν {x | dirLoss S u x = β}).tilted fun x ↦ -1 * dirLoss S θ x := by
  obtain ⟨u, β, hV, hMβ, -, hp, hrel, -⟩ := exists_exposing_polytope ν V hcharged hM
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  have hrel' : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) := by
    rwa [momentBody_faceMeasure_eq_of_exposed hS ν V u β hpoly hcharged hV hp]
  obtain ⟨θ, hθ⟩ := responseProjection_eq_tilted hS (faceMeasure ν {x | dirLoss S u x = β}) hrel'
  exact ⟨u, β, θ, hV, hMβ, hp,
    by rw [responseProjection_eq_faceMeasure_of_exposed hS ν V hpoly hcharged hV hp hMβ hrel, hθ]⟩

/-- **The response atlas of a charged polytope.** -/
structure ChargedPolytopeAtlas : Prop where
  /-- Every point lies in the relative interior of its minimal face, a face of the polytope
  contained in every face through the point. -/
  strata : ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)),
    M ∈ intrinsicInterior ℝ (minimalFacePoly V M) ∧
      IsExtreme ℝ (convexHull ℝ (V : Set (J → ℝ))) (minimalFacePoly V M) ∧
      ∀ G, IsExtreme ℝ (convexHull ℝ (V : Set (J → ℝ))) G → M ∈ G → minimalFacePoly V M ⊆ G
  /-- Csiszár's support theorem: a vertex is charged by the vertex section iff it lies on the
  minimal face. -/
  charged_iff : ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)), ∀ v : V,
    0 < vertexSection V M v ↔ (v : J → ℝ) ∈ minimalFacePoly V M
  /-- Every minimal face is exposed by a supporting functional with a charged face fibre. -/
  exposed : ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)), ∃ u : J → ℝ, ∃ β : ℝ,
    (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u M = β ∧ 0 < ν.real {x | dirLoss S u x = β} ∧
      minimalFacePoly V M = convexHull ℝ (V : Set (J → ℝ)) ∩ {y | dotJ u y = β}
  /-- Facewise exponential representation of the projection. -/
  facewise_exponential : ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)),
    ∃ u : J → ℝ, ∃ β : ℝ, ∃ θ : J → ℝ, (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u M = β ∧
      0 < ν.real {x | dirLoss S u x = β} ∧
      responseProjection hS ν M =
        (faceMeasure ν {x | dirLoss S u x = β}).tilted fun x ↦ -1 * dirLoss S θ x
  /-- Support: the projection is equivalent to the reference law on the fibre of its face. -/
  support : ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)),
    responseProjection hS ν M ≪ ν.restrict (minimalFaceFibre V S M) ∧
      ν.restrict (minimalFaceFibre V S M) ≪ responseProjection hS ν M
  /-- Incidence: the face order. -/
  face_order : ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)), ∀ N ∈ convexHull ℝ (V : Set (J → ℝ)),
    responseProjection hS ν M ≪ responseProjection hS ν N ↔
      minimalFacePoly V M ⊆ minimalFacePoly V N
  /-- Uniform density bound. -/
  density_bound : ∃ C : ℝ, 0 < C ∧
    ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)), ∀ᵐ x ∂ν, projDens hS ν M x ≤ C
  /-- Topological realisation in `L¹`. -/
  homeomorph : ∃ e : convexHull ℝ (V : Set (J → ℝ)) ≃ₜ completedFamilyL1 hS ν V,
    ∀ M, (e M : X →₁[ν] ℝ) = projL1 hS ν M
  compact : IsCompact (completedFamilyL1 hS ν V)
  /-- Hellinger continuity along sequences. -/
  hellinger : ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)), ∀ m : ℕ → J → ℝ,
    (∀ n, m n ∈ convexHull ℝ (V : Set (J → ℝ))) → Tendsto m atTop (𝓝 M) →
      Tendsto (fun n ↦ hellingerSq ν (projDens hS ν (m n)) (projDens hS ν M)) atTop (𝓝 0)
  /-- `L^p` continuity along sequences, for every finite `p`. -/
  lp : ∀ p : ℕ, ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)), ∀ m : ℕ → J → ℝ,
    (∀ n, m n ∈ convexHull ℝ (V : Set (J → ℝ))) → Tendsto m atTop (𝓝 M) →
      Tendsto (fun n ↦ ∫ x, |projDens hS ν (m n) x - projDens hS ν M x| ^ (p + 1) ∂ν) atTop
        (𝓝 0)
  /-- Boundary rays with the exact total-variation rate. -/
  ray : ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)), ∃ u : J → ℝ, ∃ β : ℝ, ∃ θ : J → ℝ,
    (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u M = β ∧
      responseProjection hS ν M = ν.withDensity (fun x ↦ ENNReal.ofReal (faceDens S ν θ u β x)) ∧
      (∀ t, ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν =
        2 * offFaceMass S ν θ u β t / (faceMass S ν θ u β + offFaceMass S ν θ u β t)) ∧
      Tendsto (fun t : ℝ ↦ ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν) atTop
        (𝓝 0)

/-- **Every charged polytope carries the response atlas.** -/
theorem chargedPolytopeAtlas
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) : ChargedPolytopeAtlas hS ν V where
  strata M hM := ⟨mem_intrinsicInterior_minimalFacePoly hM, isExtreme_minimalFacePoly hM,
    fun _ hG hMG ↦ minimalFacePoly_subset_of_isExtreme hM hG hMG⟩
  charged_iff M hM v := vertexSection_pos_iff_mem_minimalFacePoly hM v
  exposed M hM := by
    obtain ⟨u, β, hV, hMβ, -, hp, -, hF⟩ := exists_exposing_polytope ν V hcharged hM
    exact ⟨u, β, hV, hMβ, hp, by rw [hF, convexHull_inter_hyperplane V u β hV]⟩
  facewise_exponential M hM :=
    exists_faceMeasure_tilted_eq_responseProjection hS ν V hpoly hcharged hM
  support M hM := ⟨responseProjection_absolutelyContinuous_restrict hS ν V hpoly hcharged hM,
    restrict_minimalFaceFibre_absolutelyContinuous hS ν V hpoly hcharged hM⟩
  face_order M hM N hN := responseProjection_absolutelyContinuous_iff hS ν V hpoly hcharged hM hN
  density_bound := exists_uniform_projDens_bound hS ν V hpoly hcharged
  homeomorph := ⟨completedHomeomorphL1 hS ν V hcharged, fun _ ↦ rfl⟩
  compact := isCompact_completedFamilyL1 hS ν V hcharged
  hellinger M hM m hm hlim := tendsto_hellingerSq_projDens hS ν V hcharged hM hm hlim
  lp p M hM m hm hlim := tendsto_integral_abs_projDens_sub_pow hS ν V hpoly hcharged hM hm hlim p
  ray M hM := by
    obtain ⟨u, β, θ, hV, hMβ, -, hq, hrate, hlim⟩ :=
      exists_ray_tendsto_responseProjection_of_mem_polytope hS ν V hpoly hcharged hM
    exact ⟨u, β, θ, hV, hMβ, hq, hrate, hlim⟩

end Atlas

section Rigidity

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

/-- **Rigidity of the atlas**: a compact absolutely continuous mean lift of the moment body exists
iff the moment body is a charged polytope, which then carries the response atlas. -/
theorem exists_chargedPolytopeAtlas_of_compact_mean_lift
    (h : ∃ K : Set (X →₁[ν] ℝ), IsCompact K ∧ K ⊆ probL1 ν ∧
      meanL1 hS ν '' K = momentBody ν (fun _ ↦ (1 : ℝ)) S) :
    ∃ V : Finset (J → ℝ), ∃ _ : Nonempty V,
      momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)) ∧
        ChargedPolytopeAtlas hS ν V := by
  obtain ⟨V, hpoly, hcharged⟩ := (exists_charged_polytope_iff_exists_compact_mean_lift hS ν).2 h
  have hne : (V : Set (J → ℝ)).Nonempty := by
    by_contra hV
    rw [Set.not_nonempty_iff_eq_empty] at hV
    have hmean := mean_mem_momentBody_general hS ν
    rw [hpoly, hV, convexHull_empty] at hmean
    exact hmean
  obtain ⟨v, hv⟩ := hne
  have : Nonempty V := ⟨⟨v, hv⟩⟩
  exact ⟨V, this, hpoly, chargedPolytopeAtlas hS ν V hpoly hcharged⟩

end Rigidity

end Laplace.Multi
