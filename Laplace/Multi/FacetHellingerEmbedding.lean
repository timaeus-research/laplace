/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FacetCompletionLaw

/-!
# Hellinger convergence to an accessible facet law is Fisher convergence

If the square-root densities of parameters `θ_n ∈ W` converge in `L²(ν)` to the face root density of
an accessible facet point `x_M`, then `[θ_n] → x_M` in the intrinsic Fisher completion. The means
converge (a bounded weight against squares is continuous on `L²`), the facet asymptotics give
`θ_n = v_n − r_n u` with `v_n → v_M`, `r_n → ∞`, and
`dist([θ_n], x_M) ≤ K‖v_n − v_M‖ + rayTail(r_n) → 0`. So near accessible facet points the Fisher
topology of the completion is the Hellinger topology of the laws: **the completion embeds
topologically into `L²(ν)` at every accessible facet point.**
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Embedding

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **Hellinger convergence to the facet law implies Fisher convergence to the facet point.** -/
theorem tendsto_completion_of_tendsto_rootDensLp {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
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
    {x : FisherCompletion hS ν} (hx : meanExt hS ν x = M)
    {θ : ℕ → J → ℝ} (hθ : ∀ n, θ n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (hL : Tendsto (fun n ↦ rootDensLp hS ν (θ n)) atTop (𝓝 ((memLp_faceRootDens hS ν u β
      (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ)).toLp _))) :
    Tendsto (fun n ↦ ((⟨⟨θ n, hθ n⟩⟩ : FisherPoint hS ν) : FisherCompletion hS ν)) atTop (𝓝 x) := by
  have hp' : 0 < ν.real {x | dirLoss S u x = β} :=
    faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hF' := measurableSet_faceFibre hS u β
  have hfacet := facet_invisible_of_orth hS ν u β huW hu hT
  set vM : J → ℝ := (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ) with hvM
  have hvMW : vM ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
    dirSpan_faceMeasure_le hS ν _ hF' hp' (faceThetaOf hS ν {x | dirLoss S u x = β} hM').2
  have hray := (exists_meanExt_eq_iff_ray hS ν V hpoly hcharged hV hM hMβ hF hMint hv₀V hv₀β
    hzV hz huW hu hT).1 ⟨x, hx⟩
  obtain ⟨K, hK0, hK⟩ := exists_fisherNorm_bound hS ν
  -- the means converge to `M`
  have hmean_i : ∀ i, Tendsto (fun n ↦ mean (θ n) i) atTop (𝓝 (M i)) := fun i ↦ by
    have hc := ((continuous_integral_mul_sq ν (hS i)).tendsto _).comp hL
    have e1 : ∀ n, ∫ y, S i y * (rootDensLp hS ν (θ n) y * rootDensLp hS ν (θ n) y) ∂ν =
        mean (θ n) i := fun n ↦ by
      have := meanExt_eq_integral_rootDensExt hS ν
        ((⟨⟨θ n, hθ n⟩⟩ : FisherPoint hS ν) : FisherCompletion hS ν) i
      rw [meanExt_coe, rootDensExt_coe] at this
      exact this.symm
    have e2 : ∫ y, S i y * (((memLp_faceRootDens hS ν u β vM).toLp _) y *
        ((memLp_faceRootDens hS ν u β vM).toLp _) y) ∂ν = M i := by
      rw [← rootDensExt_eq_faceRootDens hS ν V hpoly hcharged hV hM hMβ hF hMint hM' hv₀V hv₀β
        hzV hz huW hu hT hx, ← meanExt_eq_integral_rootDensExt hS ν x i, hx]
    rw [Function.comp_def] at hc
    simp only [e1, e2] at hc
    exact hc
  have hmean : Tendsto (fun n ↦ mean (θ n)) atTop (𝓝 M) := tendsto_pi_nhds.2 hmean_i
  -- the facet asymptotics
  obtain ⟨hv, hr⟩ := tendsto_faceTheta_normalDepth_of_tendsto_meanMap hS ν V hpoly hcharged hV hM
    hMβ hF hM' hv₀V hv₀β hzV hz hfacet hu hθ hmean
  have hvn : Tendsto (fun n ↦ ‖(faceTheta hS ν {x | dirLoss S u x = β} (θ n) : J → ℝ) - vM‖)
      atTop (𝓝 0) := by
    rw [hvM]
    exact tendsto_iff_norm_sub_tendsto_zero.1 ((continuous_subtype_val.tendsto _).comp hv)
  -- the distance estimate
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : Tendsto (fun n ↦ K * ‖(faceTheta hS ν {x | dirLoss S u x = β} (θ n) : J → ℝ) - vM‖ +
      rayTail S ν u vM (normalDepth hS ν {x | dirLoss S u x = β} u (θ n))) atTop (𝓝 0) := by
    have := (hvn.const_mul K).add ((tendsto_rayTail hS ν u vM hray).comp hr)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun n ↦ dist_nonneg) ?_
  filter_upwards [hr.eventually (eventually_ge_atTop (0 : ℝ))] with n hrn
  have hdec := eq_faceTheta_sub_smul hS ν _ u hF' hp' hfacet hu (hθ n)
  have hrayW : vM - normalDepth hS ν {x | dirLoss S u x = β} u (θ n) • u ∈
      dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
    Submodule.sub_mem _ hvMW (Submodule.smul_mem _ _ huW)
  calc dist (((⟨⟨θ n, hθ n⟩⟩ : FisherPoint hS ν) : FisherCompletion hS ν)) x
      ≤ dist (((⟨⟨θ n, hθ n⟩⟩ : FisherPoint hS ν) : FisherCompletion hS ν))
          (((⟨⟨vM - normalDepth hS ν {x | dirLoss S u x = β} u (θ n) • u, hrayW⟩⟩ :
            FisherPoint hS ν) : FisherCompletion hS ν)) +
        dist (((⟨⟨vM - normalDepth hS ν {x | dirLoss S u x = β} u (θ n) • u, hrayW⟩⟩ :
            FisherPoint hS ν) : FisherCompletion hS ν)) x := dist_triangle _ _ _
    _ ≤ K * ‖(faceTheta hS ν {x | dirLoss S u x = β} (θ n) : J → ℝ) - vM‖ +
          rayTail S ν u vM (normalDepth hS ν {x | dirLoss S u x = β} u (θ n)) := by
        refine add_le_add ?_ (dist_ray_completion_le hS ν V hpoly hcharged hV hM hMβ hF hMint hM'
          hv₀V hv₀β hzV hz huW hu hT hx hrn)
        rw [UniformSpace.Completion.dist_eq, FisherPoint.dist_eq]
        refine (fisherDist_le_mul_norm hS ν hK _ _).trans ?_
        have e : ‖(⟨vM - normalDepth hS ν {x | dirLoss S u x = β} u (θ n) • u, hrayW⟩ -
            ⟨θ n, hθ n⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S)‖ =
            ‖(faceTheta hS ν {x | dirLoss S u x = β} (θ n) : J → ℝ) - vM‖ := by
          rw [Submodule.coe_norm, Submodule.coe_sub]
          change ‖(vM - normalDepth hS ν {x | dirLoss S u x = β} u (θ n) • u) - θ n‖ = _
          generalize hw : (faceTheta hS ν {x | dirLoss S u x = β} (θ n) : J → ℝ) = w at hdec ⊢
          generalize hr : normalDepth hS ν {x | dirLoss S u x = β} u (θ n) = r at hdec ⊢
          rw [hdec, sub_sub_sub_cancel_right, norm_sub_rev]
        rw [e]

end Embedding

end Laplace.Multi
