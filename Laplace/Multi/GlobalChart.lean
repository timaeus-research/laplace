/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponsePathDifferential
import Laplace.Multi.MeanMapEmbedding
import Laplace.Multi.EntropyCompletion
import Laplace.Multi.EmpiricalProjection

/-!
# The global response chart

The gauge-fixed mean map `θ ↦ m(θ) = E_{P_θ} S` on the direction subspace `𝕍` of the moment body is
a homeomorphism onto the relative interior of the moment body (`relintChart`), strictly
differentiable with derivative the restricted covariance operator `Dm(θ) = −Σ_θ|_𝕍`
(`hasStrictFDerivAt_relintChart_coe`, `dotJ_chartDeriv`), whose inverse is strictly differentiable
with derivative `−Σ_M⁻¹` (`hasStrictFDerivAt_chartVInv`). The inverse chart is the natural
coordinate of the reconstruction (`relintChart_symm_apply`,
`responseProjection_eq_familyMeasure_relintChart_symm`), and reconstruction is a section of the
response map with, in every interior fibre
`{ρ : E_ρ S = M}`, the unique entropy minimiser (`exists_unique_entropy_minimiser`). The packaged
statement is `global_response_chart`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Chart

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The translation of an interior response into the direction subspace. -/
noncomputable def relintToV (M : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  ⟨(M : J → ℝ) - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0,
    sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (intrinsicInterior_subset M.2)⟩

theorem continuous_relintToV : Continuous (relintToV hS ν) :=
  Continuous.subtype_mk (continuous_subtype_val.sub continuous_const) _

theorem relintToV_eq_toV (M : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    relintToV hS ν M = toV ν (fun _ ↦ (1 : ℝ)) S M :=
  Subtype.ext (by rw [toV_apply (relintToV hS ν M).2]; rfl)

/-- The inverse of the intrinsic chart is the inverse chart at the translated response. -/
theorem intrinsicChart_symm_eq_chartVInv
    (M : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (intrinsicChart measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS).symm M =
      chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        (relintToV hS ν M) := by
  have h : chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
      ((intrinsicChart measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS).symm M) = relintToV hS ν M := by
    refine Subtype.ext ?_
    rw [chartV_apply, meanMap_intrinsicChart_symm]
    rfl
  rw [← h, chartVInv_chartV]

/-- **The global response chart**: the gauge-fixed mean map is a homeomorphism of the direction
subspace onto the relative interior of the moment body. -/
noncomputable def relintChart :
    dirSpan ν (fun _ ↦ (1 : ℝ)) S ≃ₜ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) where
  toEquiv := intrinsicChart measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS
  continuous_toFun := by
    have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
    exact Continuous.subtype_mk ((continuous_meanMap measurable_const (integrable_const 1)
      (fun _ ↦ zero_le_one) (one_integral_pos ν) measurable_const h0 hS one_pos).comp
        continuous_subtype_val) _
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun M ↦ ?_
    have e : ((intrinsicChart measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS).symm : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) →
          dirSpan ν (fun _ ↦ (1 : ℝ)) S) =
        chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS ∘
          relintToV hS ν := funext fun M ↦ intrinsicChart_symm_eq_chartVInv hS ν M
    change ContinuousAt ((intrinsicChart measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).symm) M
    rw [e]
    refine ContinuousAt.comp ?_ (continuous_relintToV hS ν).continuousAt
    have hc : chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS ((intrinsicChart measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS).symm M) = relintToV hS ν M := by
      refine Subtype.ext ?_
      rw [chartV_apply, meanMap_intrinsicChart_symm]
      rfl
    rw [← hc]
    exact (hasStrictFDerivAt_chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS _).continuousAt

theorem relintChart_apply (θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    (relintChart hS ν θ : J → ℝ) = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := rfl

/-- The inverse chart is the natural coordinate of the reconstruction. -/
theorem relintChart_symm_apply (M : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (relintChart hS ν).symm M = responseTheta measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS M := by
  change (intrinsicChart measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS).symm M = _
  rw [intrinsicChart_symm_eq_chartVInv, relintToV_eq_toV]
  rfl

/-- The reconstruction of an interior response is the family member at the inverse chart. -/
theorem responseProjection_eq_familyMeasure_relintChart_symm
    (M : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    responseProjection hS ν M = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      ((relintChart hS ν).symm M) := by
  rw [relintChart_symm_apply]
  exact responseProjection_eq_familyMeasure_responseTheta hS ν M.2

/-- **The chart is strictly differentiable with derivative the restricted covariance operator.** -/
theorem hasStrictFDerivAt_relintChart_coe (θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    HasStrictFDerivAt (fun θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S ↦ (relintChart hS ν θ : J → ℝ))
      ((dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.comp (chartDeriv measurable_const
        (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS θ)) θ := by
  have h := ((dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasStrictFDerivAt.comp θ
    (hasStrictFDerivAt_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ)).add_const (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun θ ↦ ?_)
  simp only [relintChart_apply, Submodule.subtypeL_apply, chartV_apply]
  abel

/-- The pairing of the chart derivative with a direction is minus a covariance of the family. -/
theorem dotJ_relintChart_deriv (θ v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) (e : J → ℝ) :
    dotJ e (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS θ v) =
      -lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) (dirLoss S e)
        (dirLoss S v) := by
  rw [dotJ_chartDeriv, priorCov_eq_lawCov_familyMeasure hS ν]

/-- **The global response-chart theorem**: a homeomorphism `𝕍 ≃ₜ ri K` whose forward map is the
mean map (strictly differentiable, derivative the restricted covariance operator), whose inverse is
the natural coordinate of the reconstruction, and whose fibres carry a unique entropy minimiser,
the reconstruction. -/
theorem global_response_chart :
    ∃ e : dirSpan ν (fun _ ↦ (1 : ℝ)) S ≃ₜ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S),
      (∀ θ, (e θ : J → ℝ) = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) ∧
      (∀ θ, HasStrictFDerivAt (fun θ ↦ (e θ : J → ℝ))
        ((dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.comp (chartDeriv measurable_const
          (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS θ)) θ) ∧
      (∀ M : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S),
        responseProjection hS ν M = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          (e.symm M)) ∧
      (∀ M : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S),
        (fun i ↦ ∫ x, S i x ∂responseProjection hS ν M) = M ∧
        ∀ ρ : Measure X, IsProbabilityMeasure ρ → (fun i ↦ ∫ x, S i x ∂ρ) = (M : J → ℝ) →
          klDiv ρ ν = genRate ν S M → ρ = responseProjection hS ν M) := by
  refine ⟨relintChart hS ν, relintChart_apply hS ν, hasStrictFDerivAt_relintChart_coe hS ν,
    responseProjection_eq_familyMeasure_relintChart_symm hS ν, fun M ↦ ?_⟩
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν M.2
  obtain ⟨hP, hmean, hkl, -⟩ := responseProjection_spec hS ν hfin
  refine ⟨hmean, fun ρ hρ hρM hρkl ↦ ?_⟩
  obtain ⟨ρ₀, -, huniq⟩ := exists_unique_entropy_minimiser hS ν hfin
  rw [huniq ρ ⟨hρ, hρM, hρkl⟩, huniq (responseProjection hS ν M) ⟨hP, hmean, hkl⟩]

end Chart

end Laplace.Multi
