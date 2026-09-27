/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FacetCompletionAccess

/-!
# Uniqueness of the completion point over an accessible facet mean

**The fibre of the extended mean map over a point `M` of the relative interior of a facet is at
most a single point.** Two completion points over `M` are limits of parameter sequences
`θ_n = v_n − r_n u` and `θ'_n = v'_n − r'_n u` whose means converge to `M`; the facet asymptotics
give `v_n, v'_n → v_M` and `r_n, r'_n → ∞`. Then
`d_F(θ_n, θ'_n) ≤ K‖v_n − v_M‖ + (tail(r_n) + tail(r'_n)) + K‖v'_n − v_M‖ → 0`, where the middle
term is the Fisher length of the normal ray between depths `r_n` and `r'_n` (a tail of a finite
length), so the two sequences have the same limit in the completion.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Seq

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- Every completion point is the limit of a sequence of parameters. -/
theorem exists_seq_tendsto_completion (x : FisherCompletion hS ν) :
    ∃ u : ℕ → FisherPoint hS ν, Tendsto (fun n ↦ (u n : FisherCompletion hS ν)) atTop (𝓝 x) := by
  have hx' : x ∈ closure (Set.range ((↑) : FisherPoint hS ν → FisherCompletion hS ν)) := by
    rw [(UniformSpace.Completion.denseRange_coe).closure_range]
    exact Set.mem_univ x
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hx'
  choose u hu using hv
  exact ⟨u, hlim.congr fun n ↦ (hu n).symm⟩

/-- The means of an approximating sequence converge to the extended mean. -/
theorem tendsto_meanMap_of_tendsto_completion {u : ℕ → FisherPoint hS ν}
    {x : FisherCompletion hS ν}
    (hu : Tendsto (fun n ↦ (u n : FisherCompletion hS ν)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 ((u n).param : J → ℝ))
      atTop (𝓝 (meanExt hS ν x)) := by
  have h := ((continuous_meanExt hS ν).tendsto x).comp hu
  refine h.congr fun n ↦ ?_
  simp only [Function.comp, meanExt_coe]

end Seq

section Unique

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- **Uniqueness of the completion point over a facet mean.** -/
theorem meanExt_eq_facet_unique {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β)
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)
    {x x' : FisherCompletion hS ν} (hx : meanExt hS ν x = M) (hx' : meanExt hS ν x' = M) :
    x = x' := by
  -- the face
  have hp' : 0 < ν.real {x | dirLoss S u x = β} :=
    faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hF' := measurableSet_faceFibre hS u β
  have hA0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp').1.ne'
  have hPA := isProbabilityMeasure_faceMeasure ν hA0
  have hM' : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) := by
    rw [momentBody_faceMeasure_eq_of_exposed hS ν V u β hpoly hcharged hV hp']
    exact hMint
  have hfacet := facet_invisible_of_orth hS ν u β huW hu hT
  obtain ⟨vM, hvM⟩ : ∃ vM : J → ℝ,
      vM = (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) := ⟨_, rfl⟩
  have hvMW : vM ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := by
    rw [hvM]
    exact dirSpan_faceMeasure_le hS ν _ hF' hp' (faceThetaOf hS ν {x | dirLoss S u x = β} hM').2
  have hrayW : ∀ r : ℝ, vM - r • u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun r ↦
    Submodule.sub_mem _ hvMW (Submodule.smul_mem _ _ huW)
  -- the normal ray has finite length
  have hray := (exists_meanExt_eq_iff_ray hS ν V hpoly hcharged hV hM hMβ hF hMint hv₀V hv₀β
    hzV hz huW hu hT).1 ⟨x, hx⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun r ↦ fisherNorm S ν (vM - r • u) (-u) := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hg]
    exact continuous_fisherNorm_comp hS ν
      (continuous_const.sub (continuous_id.smul continuous_const)) continuous_const
  have hg0 : ∀ r, 0 ≤ g r := fun r ↦ by rw [hg]; exact fisherNorm_nonneg S ν _ _
  have hgint : IntegrableOn g (Ioi (0 : ℝ)) := by
    have h1 : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (g r)) < ⊤ := by
      have h2 := (lintegral_sqrt_raySpeedSq_lt_top_iff_tilt hS ν 0 vM u).1 hray
      refine lt_of_eq_of_lt (lintegral_congr fun r ↦ ?_) h2
      simp only [hg]
      rw [fisherNorm_neg hS ν]
      rfl
    exact ⟨hgc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2 h1⟩
  have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ ↦ vM - r • u) (-u) r := fun r ↦ by
    have h := ((hasDerivAt_id' (x := r)).smul_const u).const_sub vM
    rw [one_smul] at h
    exact h
  -- the tail of the ray length
  obtain ⟨tail, htail_def⟩ : ∃ tail : ℝ → ℝ,
      tail = fun a ↦ (∫ r in Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..a, g r := ⟨_, rfl⟩
  have htail0 : ∀ a, 0 ≤ a → 0 ≤ tail a := fun a ha ↦ by
    rw [htail_def, sub_nonneg, intervalIntegral.integral_of_le ha]
    exact setIntegral_mono_set hgint (ae_of_all _ hg0) (LE.le.eventuallyLE Ioc_subset_Ioi_self)
  have htail : Tendsto tail atTop (𝓝 0) := by
    have h1 := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hgint (tendsto_id (x := atTop))
    have h2 := (tendsto_const_nhds (x := ∫ r in Ioi (0 : ℝ), g r)).sub h1
    rw [sub_self] at h2
    rw [htail_def]
    exact h2
  have hraydist : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      fisherDist S ν ⟨vM - a • u, hrayW a⟩ ⟨vM - b • u, hrayW b⟩ ≤ tail a := fun a b ha hab ↦ by
    calc fisherDist S ν ⟨vM - a • u, hrayW a⟩ ⟨vM - b • u, hrayW b⟩
        ≤ ∫ r in a..b, g r := by
          rw [hg]
          exact fisherDist_le_integral hS ν hrayW hd continuous_const hab
      _ = (∫ r in (0 : ℝ)..b, g r) - ∫ r in (0 : ℝ)..a, g r :=
          (intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable _ _)
            (hgc.intervalIntegrable _ _)).symm
      _ ≤ tail a := by
          rw [htail_def]
          have h1 : ∫ r in (0 : ℝ)..b, g r ≤ ∫ r in Ioi (0 : ℝ), g r := by
            rw [intervalIntegral.integral_of_le (ha.trans hab)]
            exact setIntegral_mono_set hgint (ae_of_all _ hg0)
              (LE.le.eventuallyLE Ioc_subset_Ioi_self)
          linarith
  have hraydist' : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      fisherDist S ν ⟨vM - a • u, hrayW a⟩ ⟨vM - b • u, hrayW b⟩ ≤ tail a + tail b :=
    fun a b ha hb ↦ by
      rcases le_total a b with h | h
      · exact (hraydist a b ha h).trans (le_add_of_nonneg_right (htail0 b hb))
      · rw [fisherDist_comm hS ν]
        exact (hraydist b a hb h).trans (le_add_of_nonneg_left (htail0 a ha))
  -- approximating sequences and their facet components
  obtain ⟨K, hK0, hK⟩ := exists_fisherNorm_bound hS ν
  obtain ⟨w, hw⟩ := exists_seq_tendsto_completion hS ν x
  obtain ⟨w', hw'⟩ := exists_seq_tendsto_completion hS ν x'
  have hlim := tendsto_meanMap_of_tendsto_completion hS ν hw
  have hlim' := tendsto_meanMap_of_tendsto_completion hS ν hw'
  rw [hx] at hlim
  rw [hx'] at hlim'
  obtain ⟨hv, hr⟩ := tendsto_faceTheta_normalDepth_of_tendsto_meanMap hS ν V hpoly hcharged hV hM
    hMβ hF hM' hv₀V hv₀β hzV hz hfacet hu (η := fun n ↦ ((w n).param : J → ℝ))
    (fun n ↦ (w n).param.2) hlim
  obtain ⟨hv', hr'⟩ := tendsto_faceTheta_normalDepth_of_tendsto_meanMap hS ν V hpoly hcharged hV
    hM hMβ hF hM' hv₀V hv₀β hzV hz hfacet hu (η := fun n ↦ ((w' n).param : J → ℝ))
    (fun n ↦ (w' n).param.2) hlim'
  have hvn : Tendsto (fun n ↦ ‖(faceTheta hS ν {x | dirLoss S u x = β}
      ((w n).param : J → ℝ) : J → ℝ) - vM‖) atTop (𝓝 0) := by
    rw [hvM]
    exact tendsto_iff_norm_sub_tendsto_zero.1 ((continuous_subtype_val.tendsto _).comp hv)
  have hvn' : Tendsto (fun n ↦ ‖(faceTheta hS ν {x | dirLoss S u x = β}
      ((w' n).param : J → ℝ) : J → ℝ) - vM‖) atTop (𝓝 0) := by
    rw [hvM]
    exact tendsto_iff_norm_sub_tendsto_zero.1 ((continuous_subtype_val.tendsto _).comp hv')
  -- the tangential correction at fixed depth
  have htan : ∀ (θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) (r : ℝ),
      (θ : J → ℝ) = (faceTheta hS ν {x | dirLoss S u x = β} (θ : J → ℝ) : J → ℝ) - r • u →
      fisherDist S ν θ ⟨vM - r • u, hrayW r⟩ ≤
        K * ‖(faceTheta hS ν {x | dirLoss S u x = β} (θ : J → ℝ) : J → ℝ) - vM‖ := fun θ r hθ ↦ by
    refine (fisherDist_le_mul_norm hS ν hK θ ⟨vM - r • u, hrayW r⟩).trans ?_
    have e : ‖(⟨vM - r • u, hrayW r⟩ - θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S)‖ =
        ‖(faceTheta hS ν {x | dirLoss S u x = β} (θ : J → ℝ) : J → ℝ) - vM‖ := by
      rw [Submodule.coe_norm, Submodule.coe_sub]
      change ‖(vM - r • u) - (θ : J → ℝ)‖ = _
      conv_lhs => rw [hθ]
      rw [sub_sub_sub_cancel_right, norm_sub_rev]
    rw [e]
  -- the distance of the two sequences tends to zero
  have hdist : Tendsto (fun n ↦ dist (w n) (w' n)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n ↦
        K * ‖(faceTheta hS ν {x | dirLoss S u x = β} ((w n).param : J → ℝ) : J → ℝ) - vM‖ +
        (tail (normalDepth hS ν {x | dirLoss S u x = β} u ((w n).param : J → ℝ)) +
          tail (normalDepth hS ν {x | dirLoss S u x = β} u ((w' n).param : J → ℝ))) +
        K * ‖(faceTheta hS ν {x | dirLoss S u x = β} ((w' n).param : J → ℝ) : J → ℝ) - vM‖)
        atTop (𝓝 0) := by
      have := ((hvn.const_mul K).add ((htail.comp hr).add (htail.comp hr'))).add (hvn'.const_mul K)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (Eventually.of_forall fun n ↦ dist_nonneg) ?_
    filter_upwards [hr.eventually (eventually_ge_atTop (0 : ℝ)),
      hr'.eventually (eventually_ge_atTop (0 : ℝ))] with n hrn hrn'
    have hdec := eq_faceTheta_sub_smul hS ν _ u hF' hp' hfacet hu (w n).param.2
    have hdec' := eq_faceTheta_sub_smul hS ν _ u hF' hp' hfacet hu (w' n).param.2
    rw [FisherPoint.dist_eq]
    calc fisherDist S ν (w n).param (w' n).param
        ≤ fisherDist S ν (w n).param
            ⟨vM - normalDepth hS ν {x | dirLoss S u x = β} u ((w n).param : J → ℝ) • u, hrayW _⟩ +
          fisherDist S ν
            ⟨vM - normalDepth hS ν {x | dirLoss S u x = β} u ((w n).param : J → ℝ) • u, hrayW _⟩
            (w' n).param := fisherDist_triangle hS ν _ _ _
      _ ≤ fisherDist S ν (w n).param
            ⟨vM - normalDepth hS ν {x | dirLoss S u x = β} u ((w n).param : J → ℝ) • u, hrayW _⟩ +
          (fisherDist S ν
            ⟨vM - normalDepth hS ν {x | dirLoss S u x = β} u ((w n).param : J → ℝ) • u, hrayW _⟩
            ⟨vM - normalDepth hS ν {x | dirLoss S u x = β} u ((w' n).param : J → ℝ) • u, hrayW _⟩ +
          fisherDist S ν
            ⟨vM - normalDepth hS ν {x | dirLoss S u x = β} u ((w' n).param : J → ℝ) • u, hrayW _⟩
            (w' n).param) := add_le_add le_rfl (fisherDist_triangle hS ν _ _ _)
      _ ≤ K * ‖(faceTheta hS ν {x | dirLoss S u x = β} ((w n).param : J → ℝ) : J → ℝ) - vM‖ +
          ((tail (normalDepth hS ν {x | dirLoss S u x = β} u ((w n).param : J → ℝ)) +
            tail (normalDepth hS ν {x | dirLoss S u x = β} u ((w' n).param : J → ℝ))) +
          K * ‖(faceTheta hS ν {x | dirLoss S u x = β} ((w' n).param : J → ℝ) : J → ℝ) - vM‖) := by
          refine add_le_add (htan _ _ hdec) (add_le_add (hraydist' _ _ hrn hrn') ?_)
          rw [fisherDist_comm hS ν]
          exact htan _ _ hdec'
      _ = _ := by ring
  -- the two limits coincide
  have hw'x : Tendsto (fun n ↦ ((w' n : FisherPoint hS ν) : FisherCompletion hS ν)) atTop
      (𝓝 x) := by
    refine hw.congr_dist ?_
    simpa only [UniformSpace.Completion.dist_eq] using hdist
  exact tendsto_nhds_unique hw'x hw'

end Unique

end Laplace.Multi
