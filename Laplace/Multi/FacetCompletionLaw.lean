/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FacetCompletionUnique
import Laplace.Multi.FaceRootDensityLimit
import Laplace.Multi.FisherCompletionMeasure

/-!
# The law of an accessible facet point is the face exponential-family law

Over an accessible facet mean `M ∈ ri F` the unique completion point `x_M` has extended square-root
density the face root density `1_A e^{−⟨v_M,S⟩/2}/√Z_F(v_M)` (the normal ray is Fisher–Cauchy, its
limit represents `M`, and its square-root densities converge to the face root density), and its
law is the member `P^A_{v_M}` of the exponential family of the face measure `ν(·|A)`:
**the boundary point of the completed response space over `M` is the maximum-entropy law on the
face with mean `M`.**
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Ray

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **A normal ray of finite Fisher length is Fisher–Cauchy at the integers.** -/
theorem cauchySeq_ray {u : J → ℝ} (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {v : J → ℝ}
    (hvW : v ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (hray : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) u r))) < ⊤) :
    CauchySeq fun n : ℕ ↦
      (⟨⟨v - (n : ℝ) • u, Submodule.sub_mem _ hvW (Submodule.smul_mem _ _ huW)⟩⟩ :
        FisherPoint hS ν) := by
  have hrayW : ∀ r : ℝ, v - r • u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun r ↦
    Submodule.sub_mem _ hvW (Submodule.smul_mem _ _ huW)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun r ↦ fisherNorm S ν (v - r • u) (-u) := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hg]
    exact continuous_fisherNorm_comp hS ν
      (continuous_const.sub (continuous_id.smul continuous_const)) continuous_const
  have hg0 : ∀ r, 0 ≤ g r := fun r ↦ by rw [hg]; exact fisherNorm_nonneg S ν _ _
  have hgint : IntegrableOn g (Ioi (0 : ℝ)) := by
    have h1 : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (g r)) < ⊤ := by
      have h2 := (lintegral_sqrt_raySpeedSq_lt_top_iff_tilt hS ν 0 v u).1 hray
      refine lt_of_eq_of_lt (lintegral_congr fun r ↦ ?_) h2
      simp only [hg]
      rw [fisherNorm_neg hS ν]
      rfl
    exact ⟨hgc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2 h1⟩
  have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ ↦ v - r • u) (-u) r := fun r ↦ by
    have h := ((hasDerivAt_id' (x := r)).smul_const u).const_sub v
    rw [one_smul] at h
    exact h
  refine cauchySeq_of_le_tendsto_0
    (fun N : ℕ ↦ (∫ r in Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..N, g r) (fun n m N hn hm ↦ ?_) ?_
  · have key : ∀ n m : ℕ, N ≤ n → n ≤ m →
        dist (⟨⟨v - (n : ℝ) • u, hrayW n⟩⟩ : FisherPoint hS ν) ⟨⟨v - (m : ℝ) • u, hrayW m⟩⟩ ≤
          (∫ r in Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..N, g r := by
      intro n m hn hnm
      rw [FisherPoint.dist_eq]
      calc fisherDist S ν ⟨v - (n : ℝ) • u, hrayW n⟩ ⟨v - (m : ℝ) • u, hrayW m⟩
          ≤ ∫ r in (n : ℝ)..m, g r := by
            rw [hg]
            exact fisherDist_le_integral hS ν hrayW hd continuous_const (by exact_mod_cast hnm)
        _ = (∫ r in (0 : ℝ)..m, g r) - ∫ r in (0 : ℝ)..n, g r :=
            (intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable _ _)
              (hgc.intervalIntegrable _ _)).symm
        _ ≤ (∫ r in Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..N, g r := by
            have h1 : ∫ r in (0 : ℝ)..m, g r ≤ ∫ r in Ioi (0 : ℝ), g r := by
              rw [intervalIntegral.integral_of_le (Nat.cast_nonneg m)]
              exact setIntegral_mono_set hgint (ae_of_all _ hg0)
                (LE.le.eventuallyLE Ioc_subset_Ioi_self)
            have h2 : ∫ r in (0 : ℝ)..N, g r ≤ ∫ r in (0 : ℝ)..n, g r :=
              intervalIntegral.integral_mono_interval le_rfl (Nat.cast_nonneg N)
                (by exact_mod_cast hn) (ae_of_all _ hg0) (hgc.intervalIntegrable _ _)
            linarith
    rcases le_total n m with h | h
    · exact key n m hn h
    · rw [dist_comm]
      exact key m n hm h
  · have h1 := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hgint
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have h2 := (tendsto_const_nhds (x := ∫ r in Ioi (0 : ℝ), g r)).sub h1
    rwa [sub_self] at h2

end Ray

section Law

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The extended square-root density of an accessible facet point is the face root density.** -/
theorem rootDensExt_eq_faceRootDens {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β)
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
    (hM' : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)
    {x : FisherCompletion hS ν} (hx : meanExt hS ν x = M) :
    rootDensExt hS ν x = (memLp_faceRootDens hS ν u β
      (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ)).toLp _ := by
  have hp' : 0 < ν.real {x | dirLoss S u x = β} :=
    faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hF' := measurableSet_faceFibre hS u β
  have hβ := ae_dirLoss_le_of_polytope hS ν V u β hpoly hV
  set vM : J → ℝ := (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) with hvM
  have hvMW : vM ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
    dirSpan_faceMeasure_le hS ν _ hF' hp' (faceThetaOf hS ν {x | dirLoss S u x = β} hM').2
  have hray := (exists_meanExt_eq_iff_ray hS ν V hpoly hcharged hV hM hMβ hF hMint hv₀V hv₀β
    hzV hz huW hu hT).1 ⟨x, hx⟩
  have hc := cauchySeq_ray hS ν huW hvMW hray
  have hc' : CauchySeq fun n : ℕ ↦ ((⟨⟨vM - (n : ℝ) • u,
      Submodule.sub_mem _ hvMW (Submodule.smul_mem _ _ huW)⟩⟩ : FisherPoint hS ν) :
        FisherCompletion hS ν) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc ε hε
    exact ⟨N, fun m hm n hn ↦ by rw [UniformSpace.Completion.dist_eq]; exact hN m hm n hn⟩
  obtain ⟨x', hx'⟩ := cauchySeq_tendsto_of_complete hc'
  have hmean : meanExt hS ν x' = M := by
    have h1 := tendsto_meanMap_of_tendsto_completion hS ν hx'
    have h2 : Tendsto (fun n : ℕ ↦ mean (vM - (n : ℝ) • u)) atTop (𝓝 M) := by
      have := (tendsto_meanMap_ray hS ν vM u β hβ hp').comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      rw [meanMap_faceThetaOf hS ν _ hM'] at this
      exact this
    exact tendsto_nhds_unique h1 h2
  have hxx' : x = x' := meanExt_eq_facet_unique hS ν V hpoly hcharged hV hM hMβ hF hMint hv₀V
    hv₀β hzV hz huW hu hT hx hmean
  rw [hxx']
  have h3 := ((continuous_rootDensExt hS ν).tendsto x').comp hx'
  have h4 : Tendsto (fun n : ℕ ↦ rootDensLp hS ν (vM - (n : ℝ) • u)) atTop
      (𝓝 (rootDensExt hS ν x')) := by
    refine h3.congr fun n ↦ ?_
    simp only [Function.comp, rootDensExt_coe]
  exact tendsto_nhds_unique h4 (tendsto_rootDensLp_ray hS ν u β hβ hp' vM)

/-- **The law of an accessible facet point is the face exponential-family law** `P^A_{v_M}`. -/
theorem completionLaw_eq_faceFamily {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β)
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
    (hM' : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)
    {x : FisherCompletion hS ν} (hx : meanExt hS ν x = M) :
    completionLaw hS ν x = familyMeasure (faceMeasure ν {x | dirLoss S u x = β})
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) := by
  have hp' : 0 < ν.real {x | dirLoss S u x = β} :=
    faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hF' := measurableSet_faceFibre hS u β
  have hA0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp').1.ne'
  have hAtop : ν {x | dirLoss S u x = β} ≠ ⊤ := measure_ne_top _ _
  set vM : J → ℝ := (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) with hvM
  have hZ := faceZ_pos hS ν u β hp' vM
  -- the left-hand side as a density with respect to `ν`
  have hL : completionLaw hS ν x = ν.withDensity fun y ↦
      ENNReal.ofReal ({x | dirLoss S u x = β}.indicator (famWeight S vM) y / faceZ S ν u β vM) := by
    rw [completionLaw, rootDensExt_eq_faceRootDens hS ν V hpoly hcharged hV hM hMβ hF hMint hM'
      hv₀V hv₀β hzV hz huW hu hT hx]
    refine withDensity_congr_ae ?_
    filter_upwards [(memLp_faceRootDens hS ν u β vM).coeFn_toLp] with y hy
    rw [hy, faceRootDens_mul_self hS ν u β hp' vM]
  -- the right-hand side as a density with respect to `ν`
  have hfamZ : famZ S (faceMeasure ν {x | dirLoss S u x = β}) vM =
      (ν.real {x | dirLoss S u x = β})⁻¹ * faceZ S ν u β vM := by
    rw [famZ, integral_faceMeasure]
    rfl
  have hRHS : (faceMeasure ν {x | dirLoss S u x = β}).withDensity (fun y ↦
      ENNReal.ofReal (famDens S (faceMeasure ν {x | dirLoss S u x = β}) vM y)) =
      (ν {x | dirLoss S u x = β})⁻¹ • ν.withDensity ({x | dirLoss S u x = β}.indicator fun y ↦
        ENNReal.ofReal (famDens S (faceMeasure ν {x | dirLoss S u x = β}) vM y)) := by
    rw [faceMeasure, withDensity_smul_measure, ← withDensity_indicator hF']
  rw [hL, familyMeasure_eq_withDensity_famDens (faceMeasure ν {x | dirLoss S u x = β}), hRHS,
    ← withDensity_smul' _ _ (ENNReal.inv_ne_top.2 hA0)]
  refine withDensity_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hy : y ∈ {x | dirLoss S u x = β}
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, famDens, hfamZ]
    have e : famWeight S vM y / ((ν.real {x | dirLoss S u x = β})⁻¹ * faceZ S ν u β vM) =
        ν.real {x | dirLoss S u x = β} * (famWeight S vM y / faceZ S ν u β vM) := by
      field_simp
    rw [e, ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
      ENNReal.ofReal_toReal hAtop, ← mul_assoc, ENNReal.inv_mul_cancel hA0 hAtop, one_mul]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_div, mul_zero,
      ENNReal.ofReal_zero]

end Law

end Laplace.Multi
