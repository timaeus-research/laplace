/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CompletionLawEqProjection

/-!
# The response compactification

On a charged polytope the variational response `M ↦ Π(M)`, read through its density in `L¹(ν)`,
is continuous on the closed moment polytope (`tendsto_projL1_of_tendsto`), injective (the mean of
`Π(M)` is `M`), and the polytope is compact; so **the closed moment polytope embeds as a compact
subset of `L¹(ν)` through the variational response** (`isClosedEmbedding_projL1Poly`), a
homeomorphism onto its image. This is the response compactification of the exponential family:
the family `{P_θ}` sits inside it as the image of the relative interior, and every law reached by
the Fisher completion is one of its points (`completionLaw_eq_responseProjection`). Continuity of
the inverse says that laws close in `L¹` have close means — no wall is crossed without moving the
structural coordinate.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Compactification

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- The variational response on the closed polytope, as a map into `L¹(ν)`. -/
noncomputable def projL1Poly : convexHull ℝ (V : Set (J → ℝ)) → (X →₁[ν] ℝ) :=
  fun M ↦ projL1 hS ν M

omit hpoly in
/-- **Continuity of the variational response on the closed polytope.** -/
theorem continuous_projL1Poly : Continuous (projL1Poly hS ν V) := by
  refine continuous_iff_seqContinuous.2 fun m M hm ↦ ?_
  exact tendsto_projL1_of_tendsto hS ν V hcharged M.2 (fun n ↦ (m n).2) (tendsto_subtype_rng.1 hm)

omit [Nonempty V] hpoly in
/-- The mean recovers the point of the polytope from the response density. -/
theorem coe_eq_integral_projDens_mul {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    (i : J) : M i = ∫ y, projDens hS ν M y * S i y ∂ν := by
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have := congrFun (responseProjection_spec hS ν hfin).2.1 i
  rw [← this, integral_responseProjection_eq_rnDeriv hS ν hfin]
  rfl

omit [Nonempty V] hpoly in
/-- **Injectivity of the variational response**: different means give different laws. -/
theorem injective_projL1Poly : Function.Injective (projL1Poly hS ν V) := by
  intro M M' h
  have hae : projDens hS ν M =ᵐ[ν] projDens hS ν M' := by
    unfold projL1Poly projL1 at h
    exact (Integrable.toL1_eq_toL1_iff _ _ (integrable_projDens hS ν M)
      (integrable_projDens hS ν M')).1 h
  apply Subtype.ext
  funext i
  rw [coe_eq_integral_projDens_mul hS ν V hcharged M.2 i,
    coe_eq_integral_projDens_mul hS ν V hcharged M'.2 i]
  exact integral_congr_ae (hae.mono fun y hy ↦ by simp only [hy])

omit hpoly in
/-- **The response compactification**: the closed moment polytope embeds as a compact subset of
`L¹(ν)` through the variational response. -/
theorem isClosedEmbedding_projL1Poly : Topology.IsClosedEmbedding (projL1Poly hS ν V) := by
  have : CompactSpace (convexHull ℝ (V : Set (J → ℝ))) :=
    isCompact_iff_compactSpace.1 (V.finite_toSet.isCompact_convexHull (𝕜 := ℝ))
  exact (continuous_projL1Poly hS ν V hcharged).isClosedEmbedding
    (injective_projL1Poly hS ν V hcharged)

omit hpoly in
/-- The image of the closed polytope under the variational response is compact in `L¹(ν)`. -/
theorem isCompact_range_projL1Poly : IsCompact (Set.range (projL1Poly hS ν V)) := by
  have : CompactSpace (convexHull ℝ (V : Set (J → ℝ))) :=
    isCompact_iff_compactSpace.1 (V.finite_toSet.isCompact_convexHull (𝕜 := ℝ))
  exact isCompact_range (continuous_projL1Poly hS ν V hcharged)

omit hpoly in
/-- **Continuity of the inverse**: laws of the variational family that are close in `L¹(ν)` have
close means. -/
theorem tendsto_of_tendsto_projL1Poly {m : ℕ → convexHull ℝ (V : Set (J → ℝ))}
    {M : convexHull ℝ (V : Set (J → ℝ))}
    (h : Tendsto (fun n ↦ projL1Poly hS ν V (m n)) atTop (𝓝 (projL1Poly hS ν V M))) :
    Tendsto m atTop (𝓝 M) :=
  (isClosedEmbedding_projL1Poly hS ν V hcharged).isEmbedding.tendsto_nhds_iff.2 h

end Compactification

end Laplace.Multi
