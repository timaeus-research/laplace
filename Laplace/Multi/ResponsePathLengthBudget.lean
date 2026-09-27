/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherCauchyRealisation
import Laplace.Multi.FacetCompletionUnique
import Laplace.Multi.CompletionLawEqProjection

/-!
# The length budget: finite Fisher length reaches the completion

A locally `C¹` path `η : [0,∞) → W` with **integrable Fisher speed** `s(t) = |η'(t)|_{F,η(t)}`
has a well-defined endpoint in the Fisher completion `Ŵ`:

* `d_F(η(a), η(b)) ≤ ∫_a^b s` (`dist_pathCompletion_le`);
* the path is Cauchy at infinity (`cauchy_map_pathCompletion`), hence converges to
  `pathEndpoint ∈ Ŵ` (`tendsto_pathEndpoint`);
* the **tail estimate** `d̂(η(t), pathEndpoint) ≤ ∫_t^∞ s` (`dist_pathEndpoint_le_tail`);
* the means converge to the extended mean of the endpoint (`tendsto_meanMap_pathEndpoint`), and
  the law of the endpoint is the variational response at the limiting mean
  (`completionLaw_pathEndpoint_eq`).

This is the bridge from paths through data to endpoints in the stratified response atlas: any
motion of the truth whose pulled-back response speed is integrable ends at a definite structural
point, whose law is `Π` of the limiting structural coordinate. Finite *length* on `[0,∞)` is the
right hypothesis; finite energy is not enough.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Budget

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

variable {η η' : ℝ → J → ℝ} (hη : ∀ s, η s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
  (hd : ∀ s, HasDerivAt η (η' s) s) (hd' : Continuous η')
include hη hd hd'

/-- The path in the completion. -/
noncomputable def pathCompletion (t : ℝ) : FisherCompletion hS ν :=
  ((⟨⟨η t, hη t⟩⟩ : FisherPoint hS ν) : FisherCompletion hS ν)

/-- The Fisher speed of the path. -/
local notation "spd" => fun s ↦ fisherNorm S ν (η s) (η' s)

/-- The tail length `∫_t^∞ s`. -/
local notation "tail" t => ∫ s in Ioi t, fisherNorm S ν (η s) (η' s)

omit hd hd' in
theorem meanExt_pathCompletion (t : ℝ) :
    meanExt hS ν (pathCompletion hS ν hη t) = mean (η t) := by
  rw [pathCompletion, meanExt_coe]

/-- **The completion distance is bounded by the Fisher length.** -/
theorem dist_pathCompletion_le {a b : ℝ} (hab : a ≤ b) :
    dist (pathCompletion hS ν hη a) (pathCompletion hS ν hη b) ≤
      ∫ s in a..b, fisherNorm S ν (η s) (η' s) := by
  rw [pathCompletion, pathCompletion, UniformSpace.Completion.dist_eq, FisherPoint.dist_eq]
  exact fisherDist_le_integral hS ν hη hd hd' hab

variable (hint : IntegrableOn (fun s ↦ fisherNorm S ν (η s) (η' s)) (Ioi 0))
include hint

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hη hd hd' in
theorem intervalIntegral_speed_le_tail {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, fisherNorm S ν (η s) (η' s) ≤ tail a := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mono_set (hint.mono_set (Ioi_subset_Ioi ha))
    (Eventually.of_forall fun s ↦ Real.sqrt_nonneg _) (Eventually.of_forall Ioc_subset_Ioi_self)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hη hd hd' in
/-- **The tail length vanishes at infinity.** -/
theorem tendsto_tail : Tendsto (fun t ↦ tail t) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := volume)
    (f := fun s ↦ fisherNorm S ν (η s) (η' s)) (s := fun a : ℝ ↦ Ioi a)
    (fun _ ↦ measurableSet_Ioi) (fun a b hab ↦ Ioi_subset_Ioi hab) ⟨0, hint⟩
  have he : (⋂ n : ℝ, Ioi n) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false]
    intro hx
    exact lt_irrefl x (hx x)
  rwa [he, Measure.restrict_empty, integral_zero_measure] at h

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hη hd hd' hint in
theorem tail_nonneg (t : ℝ) : 0 ≤ tail t :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ ↦ Real.sqrt_nonneg _

/-- **The path is Cauchy at infinity.** -/
theorem cauchy_map_pathCompletion : Cauchy (map (pathCompletion hS ν hη) atTop) := by
  refine Metric.cauchy_iff.2 ⟨map_neBot, fun ε hε ↦ ?_⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (((tendsto_tail ν hint).eventually (Iio_mem_nhds (half_pos hε))).and (eventually_ge_atTop 0))
  refine ⟨pathCompletion hS ν hη '' Ici T, image_mem_map (Ici_mem_atTop T), ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have key : ∀ a b : ℝ, T ≤ a → a ≤ b →
      dist (pathCompletion hS ν hη a) (pathCompletion hS ν hη b) < ε := fun a b ha hab ↦ by
    obtain ⟨hlt, ha0⟩ := hT a ha
    calc dist (pathCompletion hS ν hη a) (pathCompletion hS ν hη b) ≤
          ∫ s in a..b, fisherNorm S ν (η s) (η' s) := dist_pathCompletion_le hS ν hη hd hd' hab
      _ ≤ tail a := intervalIntegral_speed_le_tail ν hint ha0 hab
      _ < ε / 2 := hlt
      _ < ε := half_lt_self hε
  rcases le_total a b with hab | hba
  · exact key a b ha hab
  · rw [dist_comm]
    exact key b a hb hba

/-- **The endpoint of a finite-length path in the completion.** -/
noncomputable def pathEndpoint : FisherCompletion hS ν :=
  Classical.choose (CompleteSpace.complete (cauchy_map_pathCompletion hS ν hη hd hd' hint))

theorem tendsto_pathEndpoint :
    Tendsto (pathCompletion hS ν hη) atTop (𝓝 (pathEndpoint hS ν hη hd hd' hint)) :=
  Classical.choose_spec (CompleteSpace.complete (cauchy_map_pathCompletion hS ν hη hd hd' hint))

/-- **The tail estimate**: `d̂(η(t), endpoint) ≤ ∫_t^∞ s`. -/
theorem dist_pathEndpoint_le_tail {t : ℝ} (ht : 0 ≤ t) :
    dist (pathCompletion hS ν hη t) (pathEndpoint hS ν hη hd hd' hint) ≤ tail t := by
  refine le_of_tendsto (tendsto_const_nhds.dist (tendsto_pathEndpoint hS ν hη hd hd' hint)) ?_
  filter_upwards [eventually_ge_atTop t] with b hb
  exact (dist_pathCompletion_le hS ν hη hd hd' hb).trans
    (intervalIntegral_speed_le_tail ν hint ht hb)

/-- **The means converge to the extended mean of the endpoint.** -/
theorem tendsto_meanMap_pathEndpoint :
    Tendsto (fun t ↦ mean (η t)) atTop (𝓝 (meanExt hS ν (pathEndpoint hS ν hη hd hd' hint))) := by
  have h := ((continuous_meanExt hS ν).tendsto _).comp (tendsto_pathEndpoint hS ν hη hd hd' hint)
  refine h.congr fun t ↦ ?_
  simp only [Function.comp, meanExt_pathCompletion]

/-- **The law of the endpoint is the variational response at the limiting mean.** -/
theorem completionLaw_pathEndpoint_eq (V : Finset (J → ℝ)) [Nonempty V]
    (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
    (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v)) {M : J → ℝ}
    (hM : Tendsto (fun t ↦ mean (η t)) atTop (𝓝 M)) :
    completionLaw hS ν (pathEndpoint hS ν hη hd hd' hint) = responseProjection hS ν M := by
  rw [completionLaw_eq_responseProjection hS ν V hpoly hcharged,
    tendsto_nhds_unique (tendsto_meanMap_pathEndpoint hS ν hη hd hd' hint) hM]

end Budget

end Laplace.Multi
