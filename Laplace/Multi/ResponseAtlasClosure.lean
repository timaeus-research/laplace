/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AccessibleFaceStratification
import Laplace.Multi.SharpAffinityTesting
import Laplace.Multi.CanonicalDataJourney

/-!
# Closing the response atlas

The final corollaries of the response-map section.

* **Global injectivity on a charged polytope** (`meanExt_injective`, `completionLaw_injective`):
  two completion points with the same extended mean lie over the same minimal-face interior and
  therefore coincide — the face is accessible by the points themselves, so no accessibility
  hypothesis is needed. Hence the fibre-uniqueness hypotheses of the Hellinger package and of the
  face embeddings are discharged in this setting (`isClosedEmbedding_rootDensExt_polytope`,
  `tendsto_iff_tendsto_rootDensExt_polytope`, `faceEmbedExt_injective_of_charged_face`); the face
  models of a charged polytope model are charged polytope models (`faceMeasure_charged`).
* **The accessible-face union** (`faceStratum`, `Accessible`, `iUnion_faceStratum`,
  `faceStratum_eq_range`): `Ŵ = ⋃_{F accessible} X_F` with `X_F = {x : meanExt x ∈ ri F}`, each
  `X_F` the image of the canonical chart `j_F`.
* **The initial defect of the canonical journey** (`journey_defect_curvature_zero`):
  `Δ''(0) = Var_ν(log q − (log q)_reg)`, what the initial response discards.
* **The closing statement** (`affinityExt_pathEndpoint_ge`, `testing_error_pathEndpoint_ge_sqrt`):
  along a response-family curve with remaining Fisher length `R(t)`, the affinity between the
  present and the limiting law is at least `1 − R(t)²/8`, and every equal-prior test on `n`
  samples has error at least `(1 − √(1 − A_t^{2n}))/2`. These are statements about the
  response-family laws and their completion limits, not about the data laws producing them.
-/

open MeasureTheory Filter Topology Set

set_option quotPrecheck false

namespace Laplace.Multi

section Injective

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- **The extended mean is injective on the completion of a charged polytope model**, with no
accessibility hypothesis. -/
theorem meanExt_injective : Function.Injective (meanExt hS ν) := by
  intro x y hxy
  obtain ⟨u, β, z₀, hz₀V, hz₀β, hx₀, hV, -, -⟩ := exists_faceChart_range_eq hS ν V hpoly hcharged x
  exact eq_of_meanExt_eq_of_mem_ri hS ν V hpoly hcharged hV hz₀V hz₀β hx₀ rfl hxy.symm

/-- **The completion law is injective on a charged polytope model**: `Q_x = Q_y → x = y`. -/
theorem completionLaw_injective : Function.Injective (completionLaw hS ν) := by
  intro x y hxy
  refine meanExt_injective hS ν V hpoly hcharged ?_
  funext i
  rw [← integral_completionLaw_eq_meanExt hS ν, ← integral_completionLaw_eq_meanExt hS ν, hxy]

/-- **The Hellinger package without fibre uniqueness**: on a charged polytope model with compact
completion, the square-root density map is a closed embedding. -/
theorem isClosedEmbedding_rootDensExt_polytope [CompactSpace (FisherCompletion hS ν)] :
    Topology.IsClosedEmbedding (rootDensExt hS ν) :=
  isClosedEmbedding_rootDensExt hS ν fun _ _ h ↦ completionLaw_injective hS ν V hpoly hcharged h

theorem tendsto_iff_tendsto_rootDensExt_polytope [CompactSpace (FisherCompletion hS ν)]
    {α : Type*} {l : Filter α} {x : α → FisherCompletion hS ν} {x₀ : FisherCompletion hS ν} :
    Tendsto x l (𝓝 x₀) ↔
      Tendsto (fun n ↦ rootDensExt hS ν (x n)) l (𝓝 (rootDensExt hS ν x₀)) :=
  tendsto_iff_tendsto_rootDensExt hS ν (fun _ _ h ↦ completionLaw_injective hS ν V hpoly hcharged h)

variable {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V)
  (hz₀β : dotJ u z₀ = β)
include hV hz₀V hz₀β

/-- The face law. -/
local notation "νE" => faceMeasure ν {x | dirLoss S u x = β}

/-- The tight vertices. -/
local notation "Vt" => (V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ))

omit [Nonempty X] [Nonempty J] [Nonempty V] hpoly hV in
/-- **The face model of a charged polytope model is a charged polytope model**: every tight vertex
is charged under the face law. -/
theorem faceMeasure_charged : ∀ v ∈ Vt, 0 < (νE).real (statFibre S v) := by
  intro v hv
  rw [Finset.mem_filter] at hv
  have := isProbabilityMeasure_faceMeasure_of_real_pos ν (faceFibre_pos' ν V hcharged hz₀V hz₀β)
  exact ENNReal.toReal_pos (faceMeasure_statFibre_pos hS ν u β (hcharged v hv.1) hv.2
    (faceFibre_pos' ν V hcharged hz₀V hz₀β)).ne' (measure_ne_top _ _)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] [Nonempty V] hpoly hcharged hV in
theorem nonempty_tight : Nonempty Vt := ⟨⟨z₀, Finset.mem_filter.2 ⟨hz₀V, hz₀β⟩⟩⟩

omit [Nonempty V] in
/-- **The face law is injective on the face completion.** -/
theorem completionLaw_faceMeasure_injective
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})] :
    Function.Injective (completionLaw hS νE) := by
  have hne := nonempty_tight V hz₀V hz₀β
  exact completionLaw_injective hS νE Vt
    (momentBody_faceMeasure_eq hS ν V hpoly hcharged hV hz₀V hz₀β)
    (faceMeasure_charged hS ν V hcharged hz₀V hz₀β)

omit [Nonempty V] in
/-- **The extended face embedding of a charged face is injective**, with no uniqueness
hypothesis. -/
theorem faceEmbedExt_injective_of_charged_face
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})] {x₀ : FisherCompletion hS ν}
    {v₀ : dirSpan νE (fun _ ↦ (1 : ℝ)) S}
    (hx₀ : completionLaw hS ν x₀ = familyMeasure νE (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (v₀ : J → ℝ)) :
    Function.Injective (faceEmbedExt hS ν νE (faceDirSpan_le hS ν V hcharged hz₀V hz₀β) x₀ v₀) :=
  faceEmbedExt_injective hS ν νE _ hx₀ fun _ _ h ↦
    completionLaw_faceMeasure_injective hS ν V hpoly hcharged hV hz₀V hz₀β h

end Injective

section Union

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS

/-- The stratum of the exposed face `{⟨u,S⟩ = β}`: completion points whose extended mean lies in
the relative interior of the face moment body. -/
def faceStratum (u : J → ℝ) (β : ℝ) : Set (FisherCompletion hS ν) :=
  {x | meanExt hS ν x ∈ intrinsicInterior ℝ
    (momentBody (faceMeasure ν {y | dirLoss S u y = β}) (fun _ ↦ (1 : ℝ)) S)}

/-- An exposed face is accessible when its stratum is nonempty. -/
def Accessible (u : J → ℝ) (β : ℝ) : Prop := (faceStratum hS ν u β).Nonempty

include hpoly hcharged

/-- **The accessible-face union**: every completion point lies in the stratum of an exposed face
with a tight vertex. -/
theorem iUnion_faceStratum :
    ⋃ (u : J → ℝ) (β : ℝ) (_ : ∀ v ∈ V, dotJ u v ≤ β) (_ : ∃ z₀ ∈ V, dotJ u z₀ = β)
      (_ : Accessible hS ν u β), faceStratum hS ν u β = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨u, β, z₀, hz₀V, hz₀β, hx₀, hV, -, -⟩ := exists_faceChart_range_eq hS ν V hpoly hcharged x
  simp only [mem_iUnion]
  exact ⟨u, β, hV, ⟨z₀, hz₀V, hz₀β⟩, ⟨x, hx₀⟩, hx₀⟩

/-- **Each accessible stratum is the image of its canonical chart.** -/
theorem faceStratum_eq_range {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ}
    (hz₀V : z₀ ∈ V) (hz₀β : dotJ u z₀ = β) {x₀ : FisherCompletion hS ν}
    (hx₀ : x₀ ∈ faceStratum hS ν u β) :
    faceStratum hS ν u β = Set.range (faceChart hS ν V hcharged hz₀V hz₀β hx₀) :=
  (range_faceChart hS ν V hpoly hcharged hV hz₀V hz₀β hx₀).symm

end Union

section Defect

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {q : X → ℝ} (hh : Bdd (logDens q))
include hS hh

/-- **The initial defect of the canonical journey**: `Δ''(0) = Var_ν(log q − (log q)_reg)`, the
part of `log q` the statistics cannot see. -/
theorem journey_defect_curvature_zero :
    deriv (deriv (responseDefect S ν (logDens q))) 0 =
      lawCov ν (fun x ↦ logDens q x - regressor hS ν hh x)
        (fun x ↦ logDens q x - regressor hS ν hh x) :=
  deriv_deriv_responseDefect_zero_eq_residual hS ν hh

end Defect

section Closing

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {η η' : ℝ → J → ℝ} (hη : ∀ s, η s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
  (hd : ∀ s, HasDerivAt η (η' s) s) (hd' : Continuous η')
  (hint : IntegrableOn (fun s ↦ fisherNorm S ν (η s) (η' s)) (Ioi 0))
include hS hη hd hd' hint

/-- **The affinity between the present and the limiting law is at least `1 − R(t)²/8`.** -/
theorem affinityExt_pathEndpoint_ge {t : ℝ} (ht : 0 ≤ t) :
    1 - (∫ s in Ioi t, fisherNorm S ν (η s) (η' s)) ^ 2 / 8 ≤
      affinityExt hS ν (pathCompletion hS ν hη t) (pathEndpoint hS ν hη hd hd' hint) := by
  refine le_trans ?_ (affinityExt_ge hS ν _ _)
  have h := dist_pathEndpoint_le_tail hS ν hη hd hd' hint ht
  have h0 : (0 : ℝ) ≤ dist (pathCompletion hS ν hη t) (pathEndpoint hS ν hη hd hd' hint) :=
    dist_nonneg
  have := pow_le_pow_left₀ h0 h 2
  linarith

/-- **The closing statement: finite samples cannot uniformly resolve a finite-length tail.**
Every equal-prior test on `n` samples between the present law and the limiting law has error at
least `(1 − √(1 − A_t^{2n}))/2`, with `A_t ≥ 1 − R(t)²/8`. -/
theorem testing_error_pathEndpoint_ge_sqrt (n : ℕ) (t : ℝ) {φ : (Fin n → X) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(1 - (affinityExt hS ν (pathCompletion hS ν hη t)
        (pathEndpoint hS ν hη hd hd' hint) ^ n) ^ 2)) / 2 ≤
      ((∫ z, φ z ∂sampleLaw hS ν n (pathCompletion hS ν hη t)) +
        ∫ z, (1 - φ z) ∂sampleLaw hS ν n (pathEndpoint hS ν hη hd hd' hint)) / 2 :=
  testing_error_sampleLaw_ge_sqrt hS ν n _ _ hφm hφ0 hφ1

end Closing

end Laplace.Multi
