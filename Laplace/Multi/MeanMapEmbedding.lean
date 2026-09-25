/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MeanMapChart

/-!
# The mean map is a global open embedding of the affine data manifold

Combining global injectivity (`meanMap_injective`) with the local chart theorem
(`map_nhds_meanMap`): for an affine data family with non-degenerate contrasts the mean map
`m : ℝ^k → ℝ^k` is continuous, injective and open, hence an **open embedding**
(`isOpenEmbedding_meanMap`) with open image (`isOpen_range_meanMap`), a homeomorphism onto its
image (`meanMapHomeomorph`), and its global inverse `Function.invFun m` is strictly
differentiable at every point of the image with derivative `(Dm(a))⁻¹`
(`hasStrictFDerivAt_invFun_meanMap`). The response coordinates `y = m(a)` are thus a **global
chart** of the affine data manifold: the data distribution is recovered from the vector of
posterior expectations of the contrasts by a strictly differentiable map, everywhere on the (open)
response space (Astra, round 25, item 1).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι] [Nonempty X]

section Global

variable {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)

include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- The mean map is continuous. -/
theorem continuous_meanMap : Continuous (meanMap μ π L₀ R t) :=
  continuous_iff_continuousAt.mpr fun a ↦
    (hasStrictFDerivAt_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht a).continuousAt

include hnd

/-- The mean map is an open map. -/
theorem isOpenMap_meanMap : IsOpenMap (meanMap μ π L₀ R t) :=
  isOpenMap_iff_nhds_le.mpr fun a ↦
    (map_nhds_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a).ge

/-- **The mean map is an open embedding.** -/
theorem isOpenEmbedding_meanMap : IsOpenEmbedding (meanMap μ π L₀ R t) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht)
    (meanMap_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd)
    (isOpenMap_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd)

/-- The response space of the affine family is open. -/
theorem isOpen_range_meanMap : IsOpen (Set.range (meanMap μ π L₀ R t)) :=
  (isOpenMap_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd).isOpen_range

/-- The affine data manifold is homeomorphic to its response space. -/
noncomputable def meanMapHomeomorph : (ι → ℝ) ≃ₜ Set.range (meanMap μ π L₀ R t) :=
  (isOpenEmbedding_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd).isEmbedding.toHomeomorph

/-- The global inverse of the mean map inverts it on the data manifold. -/
theorem invFun_meanMap (a : ι → ℝ) :
    Function.invFun (meanMap μ π L₀ R t) (meanMap μ π L₀ R t a) = a :=
  Function.leftInverse_invFun (meanMap_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd) a

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd in
/-- The mean map inverts its global inverse on the response space. -/
theorem meanMap_invFun {y : ι → ℝ} (hy : y ∈ Set.range (meanMap μ π L₀ R t)) :
    meanMap μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) y) = y :=
  Function.invFun_eq hy

/-- **The global inverse chart is strictly differentiable at every response**, with derivative
`(Dm(a))⁻¹`. -/
theorem hasStrictFDerivAt_invFun_meanMap (a : ι → ℝ) :
    HasStrictFDerivAt (Function.invFun (meanMap μ π L₀ R t))
      ((meanMapDerivEquiv (meanMapDeriv_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a)).symm :
        (ι → ℝ) →L[ℝ] (ι → ℝ)) (meanMap μ π L₀ R t a) :=
  (hasStrictFDerivAt_meanMap_equiv hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a).to_local_left_inverse
    (Filter.Eventually.of_forall fun b ↦ invFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd b)

/-- The global inverse chart is continuous on the response space. -/
theorem continuousOn_invFun_meanMap :
    ContinuousOn (Function.invFun (meanMap μ π L₀ R t)) (Set.range (meanMap μ π L₀ R t)) := by
  rintro _ ⟨a, rfl⟩
  exact (hasStrictFDerivAt_invFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
    a).continuousAt.continuousWithinAt

/-- The local inverse of `MeanMapChart` agrees with the global inverse near every response. -/
theorem meanMapInverse_eventuallyEq_invFun (a₀ : ι → ℝ) :
    ∀ᶠ y in 𝓝 (meanMap μ π L₀ R t a₀),
      meanMapInverse hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ y =
        Function.invFun (meanMap μ π L₀ R t) y := by
  filter_upwards [meanMap_meanMapInverse hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀] with y hy
  conv_rhs => rw [← hy]
  rw [invFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]

end Global

end Laplace.Multi
