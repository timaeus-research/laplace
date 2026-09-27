/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FacetCompletionLaw
import Laplace.Multi.DataRayReverse

/-!
# The endpoint of the data response in the Fisher completion

The response coordinates `θ_t` of the data path `ρ_t = ν.tilted (t h)` define a curve
`t ↦ [θ_t]` in the intrinsic Fisher completion. Under the facet hypotheses for the top-set
conditional mean `M = E[S | h = H] ∈ ri F`, **the curve has a limit as `t → ∞` iff the response
length from the featureless law is finite**; the limit is the unique completion point over `M`,
whose law is the face exponential-family law `P^A_{v_M}`.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Path

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The data response path in the Fisher completion. -/
noncomputable def dataPathCompletion (t : ℝ) : FisherCompletion hS ν :=
  ((⟨dataTheta hS ν hh t⟩ : FisherPoint hS ν) : FisherCompletion hS ν)

theorem meanExt_dataPathCompletion (t : ℝ) :
    meanExt hS ν (dataPathCompletion hS ν hh t) =
      meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (dataTheta hS ν hh t : J → ℝ) :=
  meanExt_coe hS ν _

/-- **Finite response length makes the data response path Cauchy at infinity.** -/
theorem cauchySeq_dataPathCompletion
    (hI : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(responseSpeedSq hS ν hh t))) < ⊤) :
    CauchySeq (dataPathCompletion hS ν hh) := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
      g = fun t ↦ fisherNorm S ν (dataTheta hS ν hh t : J → ℝ) (dataThetaVel hS ν hh t : J → ℝ) :=
    ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hg]
    exact continuous_fisherNorm_comp hS ν (continuous_coe_dataTheta hS ν hh)
      (continuous_coe_dataThetaVel hS ν hh)
  have hg0 : ∀ t, 0 ≤ g t := fun t ↦ by rw [hg]; exact fisherNorm_nonneg S ν _ _
  have hgint : IntegrableOn g (Ioi (0 : ℝ)) := by
    have h1 : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (g t)) < ⊤ := by
      refine lt_of_eq_of_lt (lintegral_congr fun t ↦ ?_) hI
      simp only [hg]
      rfl
    exact ⟨hgc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2 h1⟩
  -- the primitive is monotone and bounded by the half-line integral
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun t ↦ ∫ s in (0 : ℝ)..t, g s := ⟨_, rfl⟩
  have hF' : ∀ t, HasDerivAt F (g t) t := fun t ↦ by
    rw [hF]
    exact (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hFmono : Monotone F :=
    monotone_of_deriv_nonneg (fun t ↦ (hF' t).differentiableAt) fun t ↦ by
      rw [(hF' t).deriv]
      exact hg0 t
  have hF0 : F 0 = 0 := by rw [hF]; simp
  have hFle : ∀ t, F t ≤ ∫ s in Ioi (0 : ℝ), g s := fun t ↦ by
    rcases le_or_gt t 0 with ht | ht
    · calc F t ≤ F 0 := hFmono ht
        _ = 0 := hF0
        _ ≤ ∫ s in Ioi (0 : ℝ), g s := integral_nonneg fun s ↦ hg0 s
    · rw [hF]
      simp only
      rw [intervalIntegral.integral_of_le ht.le]
      exact setIntegral_mono_set hgint (ae_of_all _ hg0) (LE.le.eventuallyLE Ioc_subset_Ioi_self)
  refine cauchySeq_of_le_tendsto_0 (fun N : ℝ ↦ (∫ s in Ioi (0 : ℝ), g s) - F N)
    (fun n m N hn hm ↦ ?_) ?_
  · have key : ∀ n m : ℝ, N ≤ n → n ≤ m →
        dist (dataPathCompletion hS ν hh n) (dataPathCompletion hS ν hh m) ≤
          (∫ s in Ioi (0 : ℝ), g s) - F N := by
      intro n m hn hnm
      rw [dataPathCompletion, dataPathCompletion, UniformSpace.Completion.dist_eq,
        FisherPoint.dist_eq]
      calc fisherDist S ν (dataTheta hS ν hh n) (dataTheta hS ν hh m)
          ≤ ∫ s in n..m, g s := by
            rw [hg]
            exact fisherDist_le_integral hS ν (η := fun s ↦ (dataTheta hS ν hh s : J → ℝ))
              (fun s ↦ (dataTheta hS ν hh s).2) (hasDerivAt_coe_dataTheta hS ν hh)
              (continuous_coe_dataThetaVel hS ν hh) hnm
        _ = F m - F n := by
            rw [hF]
            simp only
            exact (intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable _ _)
              (hgc.intervalIntegrable _ _)).symm
        _ ≤ (∫ s in Ioi (0 : ℝ), g s) - F N := by
            have := hFmono hn
            linarith [hFle m]
    rcases le_total n m with h | h
    · exact key n m hn h
    · rw [dist_comm]
      exact key m n hm h
  · have h1 : Tendsto F atTop (𝓝 (∫ s in Ioi (0 : ℝ), g s)) := by
      rw [hF]
      exact intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hgint tendsto_id
    have h2 := (tendsto_const_nhds (x := ∫ s in Ioi (0 : ℝ), g s)).sub h1
    rwa [sub_self] at h2

end Path

section Endpoint

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h) {H : ℝ} (hH : ∀ x, h x ≤ H)
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hh hH hpoly hcharged

/-- **The endpoint theorem**: the data response path has a limit in the Fisher completion iff
its response length is finite; the limit lies over the top-set conditional mean. -/
theorem exists_tendsto_dataPathCompletion_iff (hp : 0 < ν.real {x | h x = H})
    {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    (hM : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) = β)
    (hF : minimalFacePoly V (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      intrinsicInterior ℝ
        (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) :
    (∃ x : FisherCompletion hS ν, Tendsto (dataPathCompletion hS ν hh) atTop (𝓝 x) ∧
        meanExt hS ν x = fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ↔
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(responseSpeedSq hS ν hh t))) < ⊤ := by
  have hmeans := tendsto_meanMap_dataTheta hS ν hh hH hp
  constructor
  · rintro ⟨x, -, hx⟩
    exact (exists_meanExt_eq_iff_responseLength hS ν V hpoly hcharged hh hH hp hV hM hMβ hF hMint
      hv₀V hv₀β hzV hz huW hu hT).1 ⟨x, hx⟩
  · intro hI
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (cauchySeq_dataPathCompletion hS ν hh hI)
    refine ⟨x, hx, ?_⟩
    have h1 := ((continuous_meanExt hS ν).tendsto x).comp hx
    have h2 : Tendsto (fun t ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (dataTheta hS ν hh t : J → ℝ)) atTop (𝓝 (meanExt hS ν x)) := by
      refine h1.congr fun t ↦ ?_
      simp only [Function.comp, meanExt_dataPathCompletion]
    exact tendsto_nhds_unique h2 hmeans

/-- **The endpoint law**: when the response length is finite, the limit of the data response
path is the unique completion point over `E[S | h = H]`, and its law is the face
exponential-family law. -/
theorem completionLaw_dataPathCompletion_limit (hp : 0 < ν.real {x | h x = H})
    {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    (hM : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) = β)
    (hF : minimalFacePoly V (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      intrinsicInterior ℝ
        (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
    (hM' : (fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ∈
      intrinsicInterior ℝ
        (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)
    {x : FisherCompletion hS ν} (hx : Tendsto (dataPathCompletion hS ν hh) atTop (𝓝 x)) :
    completionLaw hS ν x = familyMeasure (faceMeasure ν {x | dirLoss S u x = β})
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) := by
  have hmeans := tendsto_meanMap_dataTheta hS ν hh hH hp
  have h1 := ((continuous_meanExt hS ν).tendsto x).comp hx
  have h2 : Tendsto (fun t ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (dataTheta hS ν hh t : J → ℝ)) atTop (𝓝 (meanExt hS ν x)) := by
    refine h1.congr fun t ↦ ?_
    simp only [Function.comp, meanExt_dataPathCompletion]
  have hxM := tendsto_nhds_unique h2 hmeans
  exact completionLaw_eq_faceFamily hS ν V hpoly hcharged hV hM hMβ hF hMint hM' hv₀V hv₀β hzV hz
    huW hu hT hxM

end Endpoint

end Laplace.Multi
