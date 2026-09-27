/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CoefficientTiltDifferentiation
import Laplace.Multi.ResponsePathLengthBudget
import Laplace.Multi.ResponsePullbackForm
import Laplace.Multi.CovarianceFrechet
import Laplace.Multi.ResponseSusceptibility
import Laplace.Multi.ChartContinuity

/-!
# The response path of a journey through the data manifold, and its length budget

For bounded contrasts `h_j` and `C¹` coefficients `a(t)`, the data path `ρ_t ∝ e^{g_t} ν`,
`g_t = ⟨a(t), h⟩`, has response path `t ↦ Φ(g_t) = θ(E_{ρ_t} S)` (`coeffResponse`), which is `C¹`
with velocity the response velocity of the pull-back form,

`d/dt Φ(g_t) = DΦ_{g_t}[ġ_t] = responseVel`   (`hasDerivAt_coeffResponse`),

by the coefficient calculus of `CoefficientTiltDifferentiation` and the strict derivative of the
inverse mean chart; its Fisher speed is `√(G^{resp}_{g_t}(ġ_t))` (`fisherNorm_coeffResponse`), and
the velocity is continuous (`continuous_responseVel_tilt`). Hence the **length budget for
journeys through data** (`tendsto_coeffResponse_endpoint`): if `∫_0^∞ √(G^{resp}_{g_t}(ġ_t)) dt < ∞`
then `Φ(g_t)` converges in `Ŵ` to an endpoint with the tail bound
`d̂(Φ(g_t), x_∞) ≤ ∫_t^∞ √(G^{resp})`, and the data means `E_{ρ_t} S` converge to its extended mean.
Any motion of the truth with integrable pulled-back response speed ends at a definite structural
point of the stratified response atlas.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Path

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ j, Bdd (h j)) {a a' : ℝ → ι → ℝ}
  (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
include hS hh ha ha'

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

variable (S h a) in
/-- The data means along the coefficient path, `E_{ρ_t} S`. -/
noncomputable def coeffMean (t : ℝ) : J → ℝ := fun i ↦ ∫ x, S i x ∂ν.tilted (dirLoss h (a t))

omit [Fintype J] [Nonempty J] in
theorem hasDerivAt_coeffMean (t₀ : ℝ) :
    HasDerivAt (coeffMean S ν h a) (forcing S ν (dirLoss h (a t₀)) (dirLoss h (a' t₀))) t₀ :=
  hasDerivAt_pi.2 fun i ↦ hasDerivAt_integral_tilted_dirLoss ν hh ha ha' (hS i) t₀

omit [Nonempty J] ha ha' in
set_option linter.unusedFintypeInType false in
theorem coeffMean_mem_intrinsicInterior (t : ℝ) :
    coeffMean S ν h a t ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
  mean_tilted_mem_intrinsicInterior hS ν (bdd_dirLoss hh (a t))

variable (h a) in
/-- **The response path** `t ↦ Φ(g_t)`. -/
noncomputable def coeffResponse (t : ℝ) : 𝕍 := responseOf hS ν (dirLoss h (a t))

/-- **The response path is `C¹` with velocity the response velocity**:
`d/dt Φ(g_t) = DΦ_{g_t}[ġ_t]`. -/
theorem hasDerivAt_coeffResponse (t₀ : ℝ) :
    HasDerivAt (coeffResponse hS ν h a)
      (responseVel hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a' t₀))) t₀ := by
  have hrel := coeffMean_mem_intrinsicInterior hS ν hh (a := a) t₀
  have hstrict := hasStrictFDerivAt_responseTheta_add hS ν hrel
  have hmemz : ∀ t, coeffMean S ν h a t - coeffMean S ν h a t₀ ∈ 𝕍 := fun t ↦
    sub_mem_dirSpan_of_mem_momentBody' hS ν (intrinsicInterior_subset hrel)
      (intrinsicInterior_subset (coeffMean_mem_intrinsicInterior hS ν hh (a := a) t))
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ → 𝕍,
      z = fun t ↦ ⟨coeffMean S ν h a t - coeffMean S ν h a t₀, hmemz t⟩ := ⟨_, rfl⟩
  have hz : HasDerivAt z ⟨forcing S ν (dirLoss h (a t₀)) (dirLoss h (a' t₀)),
      forcing_mem_dirSpan hS ν (bdd_dirLoss hh (a t₀)) (bdd_dirLoss hh (a' t₀))⟩ t₀ := by
    rw [hzdef]
    exact hasDerivAt_subtype_of_hasDerivAt _ ((hasDerivAt_coeffMean hS ν hh ha ha' t₀).sub_const _)
  have hz0 : z t₀ = 0 := by
    rw [hzdef]
    exact Subtype.ext (sub_self _)
  have hF : HasFDerivAt (fun w : 𝕍 ↦ θr (coeffMean S ν h a t₀ + w))
      ((CDE (θr (coeffMean S ν h a t₀))).symm : 𝕍 →L[ℝ] 𝕍) (z t₀) := by
    rw [hz0]
    exact hstrict.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt t₀ hz
  refine (hcomp.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · change θr (coeffMean S ν h a t) = θr (coeffMean S ν h a t₀ + (z t : J → ℝ))
    rw [hzdef]
    change θr (coeffMean S ν h a t) =
      θr (coeffMean S ν h a t₀ + (coeffMean S ν h a t - coeffMean S ν h a t₀))
    rw [add_sub_cancel]
  · rfl

theorem continuous_coeffResponse : Continuous (coeffResponse hS ν h a) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_coeffResponse hS ν hh ha ha' t).continuousAt

/-- **The response velocity is continuous along the path.** -/
theorem continuous_responseVel_tilt :
    Continuous fun t ↦
      (responseVel hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t)) : J → ℝ) := by
  have hL : Continuous fun t ↦ ((CDE (coeffResponse hS ν h a t)).symm : 𝕍 →L[ℝ] 𝕍) :=
    (continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).comp (continuous_coeffResponse hS ν hh ha ha')
  have hv : Continuous fun t ↦ (⟨forcing S ν (dirLoss h (a t)) (dirLoss h (a' t)),
      forcing_mem_dirSpan hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t))⟩ : 𝕍) :=
    Continuous.subtype_mk (continuous_pi fun i ↦
      continuous_lawCov_tilted_dirLoss ν hh ha ha' (hS i)) _
  exact continuous_subtype_val.comp (hL.clm_apply hv)

omit ha ha' in
/-- The Fisher speed of the response path is the pulled-back response speed. -/
theorem fisherNorm_coeffResponse (t : ℝ) :
    fisherNorm S ν (coeffResponse hS ν h a t : J → ℝ)
      (responseVel hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t)) : J → ℝ) =
      √(pullbackForm hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t))) := rfl

/-- **The length budget for journeys through the data manifold**: integrable pulled-back
response speed gives a completion endpoint, the tail bound, and convergence of the data means. -/
theorem tendsto_coeffResponse_endpoint
    (hint : IntegrableOn (fun t ↦
      √(pullbackForm hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t)))) (Ioi 0)) :
    ∃ x : FisherCompletion hS ν,
      Tendsto (fun t ↦ ((⟨coeffResponse hS ν h a t⟩ : FisherPoint hS ν) :
        FisherCompletion hS ν)) atTop (𝓝 x) ∧
      (∀ t, 0 ≤ t → dist (((⟨coeffResponse hS ν h a t⟩ : FisherPoint hS ν) :
        FisherCompletion hS ν)) x ≤
          ∫ s in Ioi t, √(pullbackForm hS ν (bdd_dirLoss hh (a s)) (bdd_dirLoss hh (a' s)))) ∧
      Tendsto (coeffMean S ν h a) atTop (𝓝 (meanExt hS ν x)) := by
  have hη : ∀ s, (coeffResponse hS ν h a s : J → ℝ) ∈ 𝕍 := fun s ↦
    (coeffResponse hS ν h a s).2
  have hd : ∀ s, HasDerivAt (fun t ↦ (coeffResponse hS ν h a t : J → ℝ))
      (responseVel hS ν (bdd_dirLoss hh (a s)) (bdd_dirLoss hh (a' s)) : J → ℝ) s := fun s ↦
    (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_coeffResponse hS ν hh ha ha' s)
  have hd' := continuous_responseVel_tilt hS ν hh ha ha'
  refine ⟨pathEndpoint hS ν hη hd hd' hint, tendsto_pathEndpoint hS ν hη hd hd' hint,
    fun t ht ↦ dist_pathEndpoint_le_tail hS ν hη hd hd' hint ht, ?_⟩
  refine (tendsto_meanMap_pathEndpoint hS ν hη hd hd' hint).congr fun t ↦ ?_
  exact meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (coeffMean_mem_intrinsicInterior hS ν hh (a := a) t)

end Path

end Laplace.Multi
