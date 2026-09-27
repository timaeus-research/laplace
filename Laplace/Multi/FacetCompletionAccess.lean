/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherCauchyRealisation
import Laplace.Multi.DataRayReverse

/-!
# Completion accessibility of a facet

**A point of the intrinsic Fisher completion lies over the relative interior of a facet of the
moment polytope if and only if the facet's normal ray has finite Fisher length** (equivalently,
`Σ_k √a_k < ∞` for the dyadic shell masses of the face layer).

Forward: a completion point over `M` is a Fisher–Cauchy sequence with means converging to `M`
(`exists_meanExt_eq_iff`); a subsequence has summable consecutive distances, near-optimal flat
paths between consecutive terms concatenate to one finite-length `C¹` path whose means converge
to `M` (`FisherCauchyRealisation`), and the facet accessibility theorem gives the ray. Converse:
the finite-length path supplied by the facet theorem, sampled at the integers, is Fisher–Cauchy
(its distance increments are bounded by the tails of the finite length integral) with means
converging to `M`.

Combined with the data-ray equivalence, for the top-set conditional mean of a data path this is
the finiteness of the response length from the featureless law.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Access

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **Completion accessibility of a facet**: the extended mean map hits `M ∈ ri F` iff the normal
ray of the facet `F` has finite Fisher length. -/
theorem exists_meanExt_eq_iff_ray {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β)
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hMint : M ∈ intrinsicInterior ℝ
      (convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ))))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β) (huW : u ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) (hu : dotJ u u ≠ 0)
    (hT : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, dotJ w u = 0 →
      w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S) :
    (∃ x : FisherCompletion hS ν, meanExt hS ν x = M) ↔
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) u r))) < ⊤ := by
  rw [exists_meanExt_eq_iff hS ν]
  constructor
  · rintro ⟨w, hw, hlim⟩
    obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
    obtain ⟨φ, hφ, hφd⟩ := exists_subseq_fisherDist_le hS ν hw
    choose p hp using fun n ↦ exists_fisherPath_length_lt (S := S) (ν := ν)
      (x := (w (φ n)).param) (y := (w (φ (n + 1))).param) (ε := (1 / 2 : ℝ) ^ n) (by positivity)
    have hlen : ∀ n, (p n).length ≤ 2 * (1 / 2 : ℝ) ^ n := fun n ↦ by linarith [hp n, hφd n]
    have hd0 : ∀ n, 0 ≤ 2 * (1 / 2 : ℝ) ^ n := fun n ↦ by positivity
    have hdsum : Summable fun n ↦ 2 * (1 / 2 : ℝ) ^ n := summable_geometric_two.mul_left 2
    have hdlim : Tendsto (fun n ↦ 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 2
      rwa [mul_zero] at this
    have hM' : Tendsto (fun n ↦ mean ((w (φ n)).param : J → ℝ)) atTop (𝓝 M) :=
      hlim.comp hφ.tendsto_atTop
    exact lintegral_sqrt_raySpeedSq_lt_top_of_path hS ν V hpoly hcharged hV hM hMβ hF hMint hv₀V
      hv₀β hzV hz huW hu hT (η := fun s ↦ (realise p s : J → ℝ)) (fun s ↦ (realise p s).2)
      (η' := fun s ↦ (realiseVel p s : J → ℝ)) (fun s _ ↦ hasDerivAt_coe_realise p s)
      (continuous_subtype_val.comp (continuous_realiseVel p)).continuousOn
      (tendsto_meanMap_realise hS ν p hB hB0 hlen hdlim hM')
      (lintegral_realise_lt_top hS ν p hlen hd0 hdsum)
  · intro hray
    obtain ⟨η, η', hη, hd, hd', hlim, hI⟩ := exists_path_of_lintegral_sqrt_raySpeedSq_lt_top hS ν
      V hpoly hcharged hV hMint hv₀V hv₀β huW hray
    have hηc : Continuous η := continuous_iff_continuousAt.2 fun t ↦ (hd t).continuousAt
    set g : ℝ → ℝ := fun s ↦ fisherNorm S ν (η s) (η' s) with hg
    have hgc : Continuous g := continuous_fisherNorm_comp hS ν hηc hd'
    have hg0 : ∀ s, 0 ≤ g s := fun s ↦ fisherNorm_nonneg S ν _ _
    have hgint : IntegrableOn g (Ioi (0 : ℝ)) :=
      ⟨hgc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2 hI⟩
    refine ⟨fun n ↦ ⟨⟨η n, hη n⟩⟩, ?_, ?_⟩
    · refine cauchySeq_of_le_tendsto_0
        (fun N : ℕ ↦ (∫ s in Ioi (0 : ℝ), g s) - ∫ s in (0 : ℝ)..N, g s)
        (fun n m N hn hm ↦ ?_) ?_
      · have key : ∀ n m : ℕ, N ≤ n → n ≤ m →
            dist (⟨⟨η n, hη n⟩⟩ : FisherPoint hS ν) ⟨⟨η m, hη m⟩⟩ ≤
              (∫ s in Ioi (0 : ℝ), g s) - ∫ s in (0 : ℝ)..N, g s := by
          intro n m hn hnm
          rw [FisherPoint.dist_eq]
          calc fisherDist S ν ⟨η n, hη n⟩ ⟨η m, hη m⟩ ≤ ∫ s in (n : ℝ)..m, g s :=
                fisherDist_le_integral hS ν hη hd hd' (by exact_mod_cast hnm)
            _ = (∫ s in (0 : ℝ)..m, g s) - ∫ s in (0 : ℝ)..n, g s :=
                (intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable _ _)
                  (hgc.intervalIntegrable _ _)).symm
            _ ≤ (∫ s in Ioi (0 : ℝ), g s) - ∫ s in (0 : ℝ)..N, g s := by
                have h1 : ∫ s in (0 : ℝ)..m, g s ≤ ∫ s in Ioi (0 : ℝ), g s := by
                  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg m)]
                  exact setIntegral_mono_set hgint (ae_of_all _ hg0)
                    (LE.le.eventuallyLE Ioc_subset_Ioi_self)
                have h2 : ∫ s in (0 : ℝ)..N, g s ≤ ∫ s in (0 : ℝ)..n, g s :=
                  intervalIntegral.integral_mono_interval le_rfl (Nat.cast_nonneg N)
                    (by exact_mod_cast hn) (ae_of_all _ hg0) (hgc.intervalIntegrable _ _)
                linarith
        rcases le_total n m with h | h
        · exact key n m hn h
        · rw [dist_comm]
          exact key m n hm h
      · have h1 := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hgint
          (tendsto_natCast_atTop_atTop (R := ℝ))
        have h2 := (tendsto_const_nhds (x := ∫ s in Ioi (0 : ℝ), g s)).sub h1
        rwa [sub_self] at h2
    · exact hlim.comp tendsto_natCast_atTop_atTop

/-- **The data path's response and the completion**: the top-set conditional mean
`E[S | h = H] ∈ ri F` is an extended mean of the intrinsic Fisher completion iff the response
path from the featureless law along the data path has finite Fisher length. -/
theorem exists_meanExt_eq_iff_responseLength {h : X → ℝ} (hh : Bdd h) {H : ℝ}
    (hH : ∀ x, h x ≤ H) (hp : 0 < ν.real {x | h x = H})
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
    (∃ x : FisherCompletion hS ν, meanExt hS ν x =
        fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}) ↔
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(responseSpeedSq hS ν hh t))) < ⊤ :=
  (exists_meanExt_eq_iff_ray hS ν V hpoly hcharged hV hM hMβ hF hMint hv₀V hv₀β hzV hz huW hu
    hT).trans (data_fisher_length_lt_top_iff_ray hS ν hh hH V hpoly hcharged hp hV hM hMβ hF
    hMint hv₀V hv₀β hzV hz huW hu hT).symm

end Access

end Laplace.Multi
