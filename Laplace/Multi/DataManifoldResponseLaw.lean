/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseCompactification
import Laplace.Multi.DataResponseEndpoint
import Laplace.Multi.MeanMapEmbedding

/-!
# The response law along the whole data manifold

Along the data path `ρ_t ∝ e^{th} ν`, `t ∈ [0, ∞)`, the response law is the variational response
at the data mean, `Π(E_{ρ_t} S)`. On a charged polytope this curve of laws

* starts at the featureless law: `Π(E_{ρ_0} S) = ν`;
* is the completion law of the Fisher response at every time: `Q_{[θ_t]} = Π(E_{ρ_t} S)`;
* is continuous in `t` in `L¹(ν)`;
* converges, as `t → ∞`, in `L¹(ν)` to `Π(M_∞)` with `M_∞ = E[S | h = H]` the conditional mean
  on the top set of the data direction (`tendsto_projL1_dataMean`),

with **no accessibility hypothesis**: the variational response extends continuously from the
featureless law all the way to the data limit through the response compactification, whether or
not the Fisher response path has finite length. Where it does (`DataResponseEndpoint`), the
Fisher endpoint carries the same law, so the two pictures of "mapping responses across the data
manifold" coincide exactly on the accessible part.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section DataManifold

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

variable (S h) in
/-- The data mean `E_{ρ_t} S` along the data path. -/
noncomputable def dataMean (t : ℝ) : J → ℝ := fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ t * h x)

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hh in
theorem dataMean_apply (t : ℝ) (i : J) :
    dataMean S ν h t i = ∫ x, S i x ∂ν.tilted (fun x ↦ t * h x) := rfl

/-- The response of the data law has the data mean: `m(θ_t) = E_{ρ_t} S`. -/
theorem meanMap_dataTheta_eq_dataMean (t : ℝ) :
    mean (dataTheta hS ν hh t : J → ℝ) = dataMean S ν h t := by
  have h1 := congrArg Subtype.val (chartV_dataTheta hS ν hh t)
  rw [chartV_apply] at h1
  have h2 : (pathV hS ν hh t : J → ℝ) = dataMean S ν h t - mean 0 := rfl
  rw [h2] at h1
  exact sub_left_inj.1 h1

/-- The completion law of the Fisher response is the variational response at the data mean. -/
theorem completionLaw_dataPathCompletion_eq (t : ℝ) :
    completionLaw hS ν (dataPathCompletion hS ν hh t) =
      responseProjection hS ν (dataMean S ν h t) := by
  rw [dataPathCompletion, completionLaw_coe, familyMeasure_eq_responseProjection_meanMap hS ν,
    meanMap_dataTheta_eq_dataMean hS ν hh]

set_option linter.unusedFintypeInType false in
/-- The data mean is continuous in `t`. -/
theorem continuous_dataMean : Continuous (dataMean S ν h) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hc : Continuous fun t ↦ mean (dataTheta hS ν hh t : J → ℝ) :=
    (continuous_meanMap measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
      (one_integral_pos ν) measurable_const h0 hS one_pos).comp (continuous_coe_dataTheta hS ν hh)
  exact hc.congr fun t ↦ meanMap_dataTheta_eq_dataMean hS ν hh t

variable {H : ℝ} (hH : ∀ x, h x ≤ H) (hp : 0 < ν.real {x | h x = H})
include hH hp

variable (S h H) in
/-- The limiting mean `M_∞ = E[S | h = H]`. -/
noncomputable def topMean : J → ℝ := fun i ↦ (∫ x in {x | h x = H}, S i x ∂ν) / ν.real {x | h x = H}

omit [Nonempty X] [Fintype J] [Nonempty J] in
/-- **The data mean converges to the conditional mean on the top set.** -/
theorem tendsto_dataMean : Tendsto (dataMean S ν h) atTop (𝓝 (topMean S ν h H)) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_integral_dataPath_atTop ν hh hH hp (hS i)

variable (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hpoly hcharged

omit [Nonempty J] [Nonempty V] hH hp hcharged in
set_option linter.unusedFintypeInType false in
/-- The data means lie in the polytope. -/
theorem dataMean_mem_polytope (t : ℝ) : dataMean S ν h t ∈ convexHull ℝ (V : Set (J → ℝ)) := by
  have := isProbabilityMeasure_dataPath' ν hh t
  rw [← hpoly]
  exact mean_mem_momentBody_of_ac hS ν _ (tilted_absolutelyContinuous ν _)

omit [Nonempty J] hH [Nonempty V] hcharged in
set_option linter.unusedFintypeInType false in
/-- The limiting mean lies in the polytope. -/
theorem topMean_mem_polytope : topMean S ν h H ∈ convexHull ℝ (V : Set (J → ℝ)) := by
  have hF0 : ν {x | h x = H} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  have hac : faceMeasure ν {x | h x = H} ≪ ν := by
    rw [faceMeasure_eq_withDensity ν (measurableSet_eq_fun hh.1 measurable_const)]
    exact withDensity_absolutelyContinuous _ _
  have hmem := mean_mem_momentBody_of_ac hS ν _ hac
  rw [hpoly] at hmem
  convert hmem using 1
  funext i
  simp only [topMean, integral_faceMeasure, div_eq_inv_mul]

/-- **The response law along the data manifold converges in `L¹(ν)` to the variational response
at the data limit**, with no accessibility hypothesis. -/
theorem tendsto_projL1_dataMean :
    Tendsto (fun t ↦ projL1 hS ν (dataMean S ν h t)) atTop
      (𝓝 (projL1 hS ν (topMean S ν h H))) := by
  refine tendsto_iff_seq_tendsto.2 fun u hu ↦ ?_
  exact tendsto_projL1_of_tendsto hS ν V hcharged (topMean_mem_polytope hS ν hh hp V hpoly)
    (fun n ↦ dataMean_mem_polytope hS ν hh V hpoly (u n))
    ((tendsto_dataMean hS ν hh hH hp).comp hu)

omit hH hp in
/-- **The response law along the data manifold is continuous in time** (in `L¹(ν)`). -/
theorem continuous_projL1_dataMean : Continuous fun t ↦ projL1 hS ν (dataMean S ν h t) := by
  refine continuous_iff_seqContinuous.2 fun u t hu ↦ ?_
  exact tendsto_projL1_of_tendsto hS ν V hcharged (dataMean_mem_polytope hS ν hh V hpoly t)
    (fun n ↦ dataMean_mem_polytope hS ν hh V hpoly (u n)) ((continuous_dataMean hS ν hh).tendsto t
      |>.comp hu)

omit [Nonempty V] hH hp hpoly hcharged in
/-- **The response law starts at the featureless law**: `Π(E_{ρ_0} S) = ν`. -/
theorem responseProjection_dataMean_zero : responseProjection hS ν (dataMean S ν h 0) = ν := by
  rw [← meanMap_dataTheta_eq_dataMean hS ν hh, ← familyMeasure_eq_responseProjection_meanMap hS ν,
    dataTheta_zero, Submodule.coe_zero]
  exact familyMeasure_zero_eq hS ν

end DataManifold

end Laplace.Multi
