/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SeedIndependentAtlas
import Laplace.Multi.AccessibleFaceStrata
import Laplace.Multi.CompletionLawEqProjection
import Laplace.Multi.PolytopeFaceCut

/-!
# The accessible-face stratification of the response completion

For a charged polytope model (`momentBody ν = convexHull V`, every vertex fibre charged) the
completion `Ŵ` decomposes into finite face charts.

* **The face moment body is the face polytope** (`momentBody_faceMeasure_eq`): conditioning on the
  exposed face `E = {⟨u,S⟩ = β}` gives `momentBody (ν_E) = conv{v ∈ V : ⟨u,v⟩ = β}` — the tight
  vertices stay charged, and the upper inclusion is the hyperplane cut.
* **The canonical finite face chart** (`faceChart`): seeded at any completion point whose extended
  mean lies in the relative interior of the face body, `j_F(w) = tiltExt (w − v₀) x₀` has law
  `P^F_w` and mean `m_F(w)` (`completionLaw_faceChart`, `meanExt_faceChart`), is injective
  (`faceChart_injective`), is seed-independent (`faceChart_eq`), and its image is exactly the
  stratum `{x : meanExt x ∈ ri F}` (`range_faceChart`, `range_faceChart_eq_ri_face`): one accessible
  point of the face interior fills the whole stratum.
* **The minimal-face partition** (`minimalFacePoly_eq_of_mem_intrinsicInterior`,
  `exists_faceChart_range_eq`): every completion point lies in the relative interior of the minimal
  face of its extended mean, the fibres of `x ↦ minimalFacePoly V (meanExt x)` partition `Ŵ`, and
  every fibre is the image of the canonical chart of that face — the face being accessible by the
  point itself. Hence `Ŵ = ⨆_{F accessible} j_F(W_F)`, a set-theoretic decomposition over the
  accessible faces; no accessibility of every face and no frontier condition are claimed.
-/

open MeasureTheory Filter Topology Set

set_option quotPrecheck false

namespace Laplace.Multi

section Minimal

variable {J : Type*} [Fintype J] [Nonempty J] {V : Finset (J → ℝ)} [Nonempty V]

/-- **A point in the relative interior of a minimal face has that minimal face.** -/
theorem minimalFacePoly_eq_of_mem_intrinsicInterior {M N : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hN : N ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hNM : N ∈ intrinsicInterior ℝ (minimalFacePoly V M)) :
    minimalFacePoly V N = minimalFacePoly V M := by
  apply le_antisymm
  · exact minimalFacePoly_subset_of_isExtreme hN (isExtreme_minimalFacePoly hM)
      (intrinsicInterior_subset hNM)
  · obtain ⟨u, β, hV, hNβ, hF⟩ := exists_minimalFacePoly_eq_inter_hyperplane hN
    rw [hF]
    intro y hy
    refine ⟨minimalFacePoly_subset V M hy, ?_⟩
    have hint := (mem_intrinsicInterior_iff_forall_supporting (K := minimalFacePoly V M)
      (convex_convexHull ℝ _)).1 hNM
    have hle : ∀ y' ∈ minimalFacePoly V M, dotJ u y' ≤ dotJ u N := fun y' hy' ↦ by
      rw [hNβ]
      exact convexHull_min (fun v hv ↦ hV v (Finset.mem_coe.1 hv)) (convex_halfspace_dotJ u β)
        (minimalFacePoly_subset V M hy')
    have := hint.2 u hle y hy
    change dotJ u y = β
    rw [this, hNβ]

/-- **The relative interior of a minimal face is the set of points with that minimal face.** -/
theorem mem_intrinsicInterior_minimalFacePoly_iff {M N : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hN : N ∈ convexHull ℝ (V : Set (J → ℝ))) :
    N ∈ intrinsicInterior ℝ (minimalFacePoly V M) ↔ minimalFacePoly V N = minimalFacePoly V M :=
  ⟨minimalFacePoly_eq_of_mem_intrinsicInterior hM hN, fun h ↦
    h ▸ mem_intrinsicInterior_minimalFacePoly hN⟩

end Minimal

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
  {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V)
  (hz₀β : dotJ u z₀ = β)
include hS hpoly hcharged hV hz₀V hz₀β

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The face law. -/
local notation "νE" => faceMeasure ν {x | dirLoss S u x = β}

/-- The tight vertices. -/
local notation "Vt" => (V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ))

/-- The face direction space. -/
local notation "𝕍E" => dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S

/-- The face family. -/
local notation "Qface" => familyMeasure (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
  (fun _ ↦ (0 : ℝ)) S 1

/-- The face mean map. -/
local notation "meanE" => meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
  (fun _ ↦ (0 : ℝ)) S 1

/-- The relative interior of the face moment body. -/
local notation "riE" => intrinsicInterior ℝ
  (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)

omit [Nonempty X] [Nonempty J] hS [Nonempty V] hpoly hV in
theorem faceFibre_pos' : 0 < ν.real {x | dirLoss S u x = β} :=
  faceFibre_pos_of_charged ν V hcharged hz₀V hz₀β

omit [Nonempty X] [Nonempty J] [Nonempty V] hpoly hV in
theorem faceDirSpan_le : 𝕍E ≤ 𝕍 :=
  dirSpan_faceMeasure_le hS ν _ (measurableSet_faceFibre hS u β)
    (faceFibre_pos' ν V hcharged hz₀V hz₀β)

omit [Nonempty X] [Nonempty J] [Nonempty V] hpoly hV in
/-- Tight vertices stay in the face moment body. -/
theorem tight_vertex_mem_momentBody_faceMeasure {v : J → ℝ} (hvV : v ∈ V) (hvβ : dotJ u v = β) :
    v ∈ momentBody νE (fun _ ↦ (1 : ℝ)) S := by
  refine essRange_subset_momentBody S
    ((mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS).2 fun r hr ↦ ?_)
  refine lt_of_lt_of_le (faceMeasure_statFibre_pos hS ν u β (hcharged v hvV) hvβ
    (faceFibre_pos' ν V hcharged hz₀V hz₀β)) (measure_mono fun x hx ↦ ?_)
  change statPoint S x ∈ Metric.ball v r
  have hx' : statPoint S x = v := hx
  rw [hx']
  exact Metric.mem_ball_self hr

omit [Nonempty X] [Nonempty J] [Nonempty V] in
/-- **The face moment body is the face polytope**: `momentBody (ν_E) = conv(tight vertices)`. -/
theorem momentBody_faceMeasure_eq :
    momentBody νE (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (Vt : Set (J → ℝ)) := by
  have hEm := measurableSet_faceFibre hS u β
  have hp := faceFibre_pos' ν V hcharged hz₀V hz₀β
  apply le_antisymm
  · rw [← convexHull_inter_hyperplane V u β hV, ← hpoly]
    exact subset_inter (momentBody_faceMeasure_subset ν hEm hS hp)
      (momentBody_faceMeasure_subset_hyperplane ν hEm hS hp rfl)
  · refine convexHull_min ?_ (convex_momentBody S)
    intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    exact tight_vertex_mem_momentBody_faceMeasure hS ν V hcharged hz₀V hz₀β hv.1 hv.2

/-- **The seed bridge**: a completion point whose extended mean is a face-interior point `M` has
law `P^F_{θ_F(M)}` — it is an admissible seed for the face chart. -/
theorem completionLaw_eq_faceFamily_faceThetaOf
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})] {x : FisherCompletion hS ν}
    {M : J → ℝ} (hM : M ∈ riE) (hx : meanExt hS ν x = M) :
    completionLaw hS ν x = Qface (faceThetaOf hS ν _ hM : J → ℝ) := by
  have hx' : meanExt hS ν x = meanE (faceThetaOf hS ν _ hM : J → ℝ) := by
    rw [hx, meanMap_faceThetaOf]
  rw [completionLaw_eq_responseProjection hS ν V hpoly hcharged x, hx']
  exact responseProjection_eq_faceFamily hS ν V hpoly hcharged hV hz₀V hz₀β rfl _

/-- **The canonical finite face chart** `j_F : W_F → Ŵ`, seeded at a completion point `x₀` whose
extended mean is a face-interior point. -/
noncomputable def faceChart {x₀ : FisherCompletion hS ν} (hx₀ : meanExt hS ν x₀ ∈ riE)
    (w : 𝕍E) : FisherCompletion hS ν :=
  haveI := isProbabilityMeasure_faceMeasure_of_real_pos ν (faceFibre_pos' ν V hcharged hz₀V hz₀β)
  faceEmbed hS ν νE (faceDirSpan_le hS ν V hcharged hz₀V hz₀β) x₀ (faceThetaOf hS ν _ hx₀) w

/-- The law of a chart point is the face family law `P^F_w`. -/
theorem completionLaw_faceChart {x₀ : FisherCompletion hS ν} (hx₀ : meanExt hS ν x₀ ∈ riE)
    (w : 𝕍E) :
    completionLaw hS ν (faceChart hS ν V hcharged hz₀V hz₀β hx₀ w) = Qface (w : J → ℝ) := by
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν (faceFibre_pos' ν V hcharged hz₀V hz₀β)
  exact completionLaw_faceEmbed hS ν νE _
    (completionLaw_eq_faceFamily_faceThetaOf hS ν V hpoly hcharged hV hz₀V hz₀β hx₀ rfl) w

/-- The extended mean of a chart point is the face mean `m_F(w)`. -/
theorem meanExt_faceChart {x₀ : FisherCompletion hS ν} (hx₀ : meanExt hS ν x₀ ∈ riE) (w : 𝕍E) :
    meanExt hS ν (faceChart hS ν V hcharged hz₀V hz₀β hx₀ w) = meanE (w : J → ℝ) := by
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν (faceFibre_pos' ν V hcharged hz₀V hz₀β)
  exact meanExt_faceEmbed hS ν νE _
    (completionLaw_eq_faceFamily_faceThetaOf hS ν V hpoly hcharged hV hz₀V hz₀β hx₀ rfl) w

theorem meanExt_faceChart_mem {x₀ : FisherCompletion hS ν} (hx₀ : meanExt hS ν x₀ ∈ riE)
    (w : 𝕍E) : meanExt hS ν (faceChart hS ν V hcharged hz₀V hz₀β hx₀ w) ∈ riE := by
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν (faceFibre_pos' ν V hcharged hz₀V hz₀β)
  rw [meanExt_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀ w]
  exact meanMap_faceMeasure_mem_intrinsicInterior hS ν (u := u) (β := β) (w : J → ℝ)

/-- **The completion fibre over a face-interior mean is a single point.** -/
theorem eq_of_meanExt_eq_of_mem_ri {x y : FisherCompletion hS ν} {M : J → ℝ} (hM : M ∈ riE)
    (hx : meanExt hS ν x = M) (hy : meanExt hS ν y = M) : x = y := by
  have hp := faceFibre_pos' ν V hcharged hz₀V hz₀β
  have hAm := measurableSet_faceFibre hS u β
  have hMbody := intrinsicInterior_subset hM
  have hMV : M ∈ convexHull ℝ (V : Set (J → ℝ)) := by
    rw [← hpoly]
    exact momentBody_faceMeasure_subset ν hAm hS hp hMbody
  have hMβ : dotJ u M = β := momentBody_faceMeasure_subset_hyperplane ν hAm hS hp rfl hMbody
  obtain ⟨z, hzV, hzβ, hzF⟩ := exists_charged_vertex_on_face V hV hMV hMβ
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν hp
  exact meanExt_eq_face_unique hS ν V hpoly hcharged hV hzV hzβ hMV hMβ hzF hM hx hy

/-- **The chart image is the stratum**: `j_F(W_F) = {x : meanExt x ∈ ri(momentBody ν_E)}`. -/
theorem range_faceChart {x₀ : FisherCompletion hS ν} (hx₀ : meanExt hS ν x₀ ∈ riE) :
    Set.range (faceChart hS ν V hcharged hz₀V hz₀β hx₀) =
      {x | meanExt hS ν x ∈ riE} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact meanExt_faceChart_mem hS ν V hpoly hcharged hV hz₀V hz₀β hx₀ w
  · intro hx
    have := isProbabilityMeasure_faceMeasure_of_real_pos ν (faceFibre_pos' ν V hcharged hz₀V hz₀β)
    refine ⟨faceThetaOf hS ν _ hx,
      eq_of_meanExt_eq_of_mem_ri hS ν V hpoly hcharged hV hz₀V hz₀β hx ?_ rfl⟩
    rw [meanExt_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀, meanMap_faceThetaOf]

/-- **The chart image is the relative interior of the face polytope.** -/
theorem range_faceChart_eq_ri_face {x₀ : FisherCompletion hS ν} (hx₀ : meanExt hS ν x₀ ∈ riE) :
    Set.range (faceChart hS ν V hcharged hz₀V hz₀β hx₀) =
      {x | meanExt hS ν x ∈ intrinsicInterior ℝ (convexHull ℝ (Vt : Set (J → ℝ)))} := by
  rw [range_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀,
    momentBody_faceMeasure_eq hS ν V hpoly hcharged hV hz₀V hz₀β]

/-- **The chart is injective**: the face mean map is injective on the face direction space. -/
theorem faceChart_injective {x₀ : FisherCompletion hS ν} (hx₀ : meanExt hS ν x₀ ∈ riE) :
    Function.Injective (faceChart hS ν V hcharged hz₀V hz₀β hx₀) := by
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν (faceFibre_pos' ν V hcharged hz₀V hz₀β)
  intro w w' h
  have hm := congrArg (meanExt hS ν) h
  rw [meanExt_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀,
    meanExt_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀] at hm
  exact Subtype.ext (meanMap_injOn_dirSpan measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos _) hS w.2 w'.2 hm)

/-- **Seed independence of the finite chart**: any two accessible points give the same chart. -/
theorem faceChart_eq {x₀ x₀' : FisherCompletion hS ν} (hx₀ : meanExt hS ν x₀ ∈ riE)
    (hx₀' : meanExt hS ν x₀' ∈ riE) :
    faceChart hS ν V hcharged hz₀V hz₀β hx₀ =
      faceChart hS ν V hcharged hz₀V hz₀β hx₀' := by
  funext w
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν (faceFibre_pos' ν V hcharged hz₀V hz₀β)
  exact eq_of_meanExt_eq_of_mem_ri hS ν V hpoly hcharged hV hz₀V hz₀β
    (meanMap_faceMeasure_mem_intrinsicInterior hS ν (u := u) (β := β) (w : J → ℝ))
    (meanExt_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀ w)
    (meanExt_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀' w)

end Face

section Stratification

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- The stratum of a completion point: all points whose extended mean has the same minimal face. -/
def stratum (x : FisherCompletion hS ν) : Set (FisherCompletion hS ν) :=
  {y | minimalFacePoly V (meanExt hS ν y) = minimalFacePoly V (meanExt hS ν x)}

omit hpoly hcharged in
theorem mem_stratum_self (x : FisherCompletion hS ν) : x ∈ stratum hS ν V x := rfl

omit hpoly hcharged in
/-- The strata partition the completion. -/
theorem stratum_eq_or_disjoint (x y : FisherCompletion hS ν) :
    stratum hS ν V x = stratum hS ν V y ∨
      Disjoint (stratum hS ν V x) (stratum hS ν V y) := by
  by_cases h : minimalFacePoly V (meanExt hS ν x) = minimalFacePoly V (meanExt hS ν y)
  · left
    ext z
    change _ = _ ↔ _ = _
    rw [h]
  · right
    rw [Set.disjoint_left]
    intro z hz hz'
    exact h (hz.symm.trans hz')

omit hpoly hcharged in
theorem iUnion_stratum : ⋃ x, stratum hS ν V x = univ :=
  eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨x, mem_stratum_self hS ν V x⟩

/-- **The accessible-face stratification**: every stratum of the completion is the image of the
canonical finite chart of the minimal face of its extended mean, that face being accessible by
the point itself: `Ŵ = ⨆_{F accessible} j_F(W_F)`. -/
theorem exists_faceChart_range_eq (x : FisherCompletion hS ν) :
    ∃ (u : J → ℝ) (β : ℝ) (z₀ : J → ℝ) (hz₀V : z₀ ∈ V) (hz₀β : dotJ u z₀ = β)
      (hx₀ : meanExt hS ν x ∈ intrinsicInterior ℝ
        (momentBody (faceMeasure ν {y | dirLoss S u y = β}) (fun _ ↦ (1 : ℝ)) S)),
      (∀ v ∈ V, dotJ u v ≤ β) ∧
      minimalFacePoly V (meanExt hS ν x) =
        convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) ∧
      Set.range (faceChart hS ν V hcharged hz₀V hz₀β hx₀) = stratum hS ν V x := by
  have hMV := meanExt_mem_polytope hS ν V hpoly x
  obtain ⟨u, β, hV, hMβ, -, hF⟩ := exists_exposing_minimalFacePoly hMV
  obtain ⟨z₀, hz₀V, hz₀β, -⟩ := exists_charged_vertex_on_face V hV hMV hMβ
  have hbody := momentBody_faceMeasure_eq hS ν V hpoly hcharged hV hz₀V hz₀β
  have hx₀ : meanExt hS ν x ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {y | dirLoss S u y = β}) (fun _ ↦ (1 : ℝ)) S) := by
    rw [hbody, ← hF]
    exact mem_intrinsicInterior_minimalFacePoly hMV
  refine ⟨u, β, z₀, hz₀V, hz₀β, hx₀, hV, hF, ?_⟩
  rw [range_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀, hbody, ← hF]
  ext y
  exact mem_intrinsicInterior_minimalFacePoly_iff hMV (meanExt_mem_polytope hS ν V hpoly y)

end Stratification

end Laplace.Multi
