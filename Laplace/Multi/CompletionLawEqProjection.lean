/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BoundedTiltCompletionAction
import Laplace.Multi.FacetCompletionUnique
import Laplace.Multi.PolyhedralCompletion
import Laplace.Multi.EntropyGapTotalVariation
import Laplace.Multi.VertexGapForward
import Laplace.Multi.ResponsePathDifferential
import Laplace.Multi.FaceGauge
import Laplace.Multi.RelativeMomentBody

/-!
# Every completion law is the variational response at its extended mean

On a charged polytope the variational response `M ↦ Π(M)` (the information projection of `ν`
onto the laws with mean `M`) is defined on the whole closed moment polytope and is `L¹`-continuous
there (`PolyhedralCompletion`). At interior parameters `P_θ = Π(m(θ))`. For a point `x` of the
Fisher completion, approximating `x` by parameters `θ_n` and passing to the limit on both sides —
`Q_x = lim P_{θ_n}` for bounded test functions by continuity of the completion laws, and
`Π(m(θ_n)) → Π(meanExt x)` in `L¹` — gives

`Q_x = Π(meanExt x)`   (`completionLaw_eq_responseProjection`).

So **the completed Fisher response is the restriction of the variational response to the
accessible extended means**: every completion law has information `𝓘(meanExt x)` and is the
unique Kullback–Leibler minimiser among the laws with its mean, whatever construction produced
the point.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Identify

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The family member is the variational response at its own mean**: `P_θ = Π(m(θ))`. -/
theorem familyMeasure_eq_responseProjection_meanMap (θ : J → ℝ) :
    Pfam θ = responseProjection hS ν (mean θ) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hrel : mean θ ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    rw [← range_meanMap_eq_intrinsicInterior_momentBody measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS]
    exact ⟨θ, rfl⟩
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hrel]
  have hmean := meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel
  have hinv := (meanMap_eq_iff_invisible measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) measurable_const h0 hS one_pos _ _).1 hmean
  have := familyMeasure_add_of_invisible hS ν (responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS (mean θ)) hinv
  rwa [add_sub_cancel] at this

variable (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hpoly hcharged

omit [Nonempty V] hcharged in
/-- Extended means lie in the polytope. -/
theorem meanExt_mem_polytope (x : FisherCompletion hS ν) :
    meanExt hS ν x ∈ convexHull ℝ (V : Set (J → ℝ)) := by
  obtain ⟨θ, hθ⟩ := exists_seq_tendsto_completion hS ν x
  have hm := tendsto_meanMap_of_tendsto_completion hS ν hθ
  exact (V.finite_toSet.isClosed_convexHull (𝕜 := ℝ)).mem_of_tendsto hm
    (Eventually.of_forall fun n ↦ meanMap_mem_polytope hS ν V hpoly _)

omit hpoly in
/-- Bounded integrals against the projection are continuous along convergent means. -/
theorem tendsto_integral_mul_projDens {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    {m : ℕ → J → ℝ} (hm : ∀ n, m n ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hlim : Tendsto m atTop (𝓝 M)) {f : X → ℝ} (hf : Bdd f) :
    Tendsto (fun n ↦ ∫ y, f y * projDens hS ν (m n) y ∂ν) atTop
      (𝓝 (∫ y, f y * projDens hS ν M y ∂ν)) := by
  obtain ⟨B, hB⟩ := hf.2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  have hL1 := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_projL1_of_tendsto hS ν V hcharged hM hm
    hlim)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (by simpa using hL1.const_mul B)
  have hi : ∀ N, Integrable (fun y ↦ f y * projDens hS ν N y) ν := fun N ↦
    (integrable_projDens hS ν N).bdd_mul hf.1.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hB y)
  rw [← integral_sub (hi _) (hi _), norm_projL1_sub]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono ((hi _).sub (hi _)).norm
    ((((integrable_projDens hS ν _).sub (integrable_projDens hS ν _)).abs).const_mul B) fun y ↦ ?_
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (hB y) (abs_nonneg _)

/-- **Every completion law is the variational response at its extended mean**:
`Q_x = Π(meanExt x)`. -/
theorem completionLaw_eq_responseProjection (x : FisherCompletion hS ν) :
    completionLaw hS ν x = responseProjection hS ν (meanExt hS ν x) := by
  obtain ⟨θ, hθ⟩ := exists_seq_tendsto_completion hS ν x
  have hm := tendsto_meanMap_of_tendsto_completion hS ν hθ
  have hmem : ∀ n, mean ((θ n).param : J → ℝ) ∈ convexHull ℝ (V : Set (J → ℝ)) := fun n ↦
    meanMap_mem_polytope hS ν V hpoly _
  have hMx := meanExt_mem_polytope hS ν V hpoly x
  have hfin : ∀ M ∈ convexHull ℝ (V : Set (J → ℝ)), genRate ν S M ≠ ⊤ := fun M hM ↦
    genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have key : ∀ f : X → ℝ, Bdd f → ∫ y, f y ∂completionLaw hS ν x =
      ∫ y, f y ∂responseProjection hS ν (meanExt hS ν x) := by
    intro f hf
    have h1 : Tendsto (fun n ↦ ∫ y, f y ∂completionLaw hS ν (θ n : FisherCompletion hS ν)) atTop
        (𝓝 (∫ y, f y ∂completionLaw hS ν x)) :=
      ((continuous_integral_completionLaw hS ν hf).tendsto x).comp hθ
    have e1 : ∀ n, ∫ y, f y ∂completionLaw hS ν (θ n : FisherCompletion hS ν) =
        ∫ y, f y * projDens hS ν (mean ((θ n).param : J → ℝ)) y ∂ν := fun n ↦ by
      rw [completionLaw_coe, familyMeasure_eq_responseProjection_meanMap hS ν,
        integral_responseProjection_eq_rnDeriv hS ν (hfin _ (hmem n)) f]
      exact integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)
    have e2 : ∫ y, f y ∂responseProjection hS ν (meanExt hS ν x) =
        ∫ y, f y * projDens hS ν (meanExt hS ν x) y ∂ν := by
      rw [integral_responseProjection_eq_rnDeriv hS ν (hfin _ hMx) f]
      exact integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)
    have h2 := tendsto_integral_mul_projDens hS ν V hcharged hMx hmem hm hf
    rw [e2]
    exact tendsto_nhds_unique (h1.congr fun n ↦ e1 n) h2
  have hP := (responseProjection_spec hS ν (hfin _ hMx)).1
  ext A hA
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _),
    ← measureReal_def, ← measureReal_def, ← integral_indicator_one hA, ← integral_indicator_one hA]
  exact key _ ⟨measurable_one.indicator hA, 1, fun y ↦ by by_cases hy : y ∈ A <;> simp [hy]⟩

/-- **The information of a completion law is the rate at its extended mean.** -/
theorem klDiv_completionLaw_eq_genRate (x : FisherCompletion hS ν) :
    klDiv (completionLaw hS ν x) ν = genRate ν S (meanExt hS ν x) := by
  rw [completionLaw_eq_responseProjection hS ν V hpoly hcharged x]
  exact (responseProjection_spec hS ν (genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged
    (meanExt_mem_polytope hS ν V hpoly x))).2.2.1

/-- **Every completion law is the information projection at its extended mean**: it has the
least information among the laws with the same mean. -/
theorem klDiv_completionLaw_le (x : FisherCompletion hS ν) (Q : Measure X) [IsProbabilityMeasure Q]
    (hQ : (fun i ↦ ∫ y, S i y ∂Q) = meanExt hS ν x) :
    klDiv (completionLaw hS ν x) ν ≤ klDiv Q ν := by
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged
    (meanExt_mem_polytope hS ν V hpoly x)
  rw [klDiv_completionLaw_eq_genRate hS ν V hpoly hcharged x,
    (responseProjection_spec hS ν hfin).2.2.2 Q inferInstance hQ]
  exact le_add_self

end Identify

end Laplace.Multi
