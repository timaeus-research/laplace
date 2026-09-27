/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDataSmooth
import Laplace.Multi.ResponseSecondOrderLifts
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The response map is a submersion on horizontally augmented slices

A finite data slice `z ↦ Φ(g + ∑ zᵢkᵢ)` need not be a submersion (its directions may all be
invisible). Adjoining the horizontal lift repairs this: on the **augmented slice** `Ψ(z, u) = Φ(g +
∑ zᵢkᵢ + hor_g(u))`, `u ∈ W`, the derivative at the base is `DΨ(0,0)[ξ, w] = DΦ_g[⟨ξ,k⟩] + w`
(`fderiv_augSlice_zero`), which is onto `W`, and the map `Ξ(z,u) = (z, Ψ(z,u))` has an invertible
strict derivative with explicit inverse `(ξ, η) ↦ (ξ, η − DΦ_g[⟨ξ,k⟩])` (`augDerivEquiv`,
`hasStrictFDerivAt_augChart`).

The inverse function theorem then gives the **local product structure** of the augmented slice:
there is a `C^∞` map `σ` near `(0, Φ(g))` with `Ψ(z, σ(z, θ)) = θ`
(`eventually_augSlice_fibreSection`) and `σ(z, Ψ(z,u)) = u` (`eventually_fibreSection_augSlice`),
`σ(0, Φ(g)) = 0`. Locally the response fibres in the augmented slice are the graphs `u = σ(z, θ)`,
and the slice is the product of a fibre with the response coordinate. This is the submersion
theorem for the response map on every horizontally augmented finite-dimensional piece of the data
manifold.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Augmented

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {ι : Type*} [Fintype ι] {g : X → ℝ} (hg : Bdd g) {k : ι → X → ℝ} (hk : ∀ i, Bdd (k i))
include hS hg hk

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The dimension of the direction space. -/
local notation "n" => Module.finrank ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S)

variable (S) in
/-- A basis of the direction space. -/
noncomputable def wBasis : Module.Basis (Fin n) ℝ 𝕍 := Module.finBasis ℝ 𝕍

variable (k) in
/-- The augmented directions: the slice directions together with the horizontal lifts of a basis
of the direction space. -/
noncomputable def augDir : ι ⊕ Fin n → X → ℝ :=
  Sum.elim k fun j ↦ horizontalLift hS ν hg (wBasis S ν j)

set_option linter.unusedFintypeInType false in
omit [Fintype ι] in
theorem bdd_augDir : ∀ a, Bdd (augDir hS ν hg k a) := by
  rintro (i | j)
  · exact hk i
  · exact bdd_horizontalLift hS ν hg _

variable (ι S) in
/-- The augmented coefficient map `(z, u) ↦ (z, coordinates of u)`, as a continuous linear map. -/
noncomputable def augCoeffL : ((ι → ℝ) × 𝕍) →L[ℝ] (ι ⊕ Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearEquiv.sumArrowLequivProdArrow ι (Fin n) ℝ ℝ).symm.toLinearMap ∘ₗ
      LinearMap.prodMap LinearMap.id ((wBasis S ν).equivFun : 𝕍 →ₗ[ℝ] (Fin n → ℝ)))

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk in
theorem augCoeffL_apply (p : (ι → ℝ) × 𝕍) :
    augCoeffL S ν ι p = Sum.elim p.1 ((wBasis S ν).equivFun p.2) := by
  funext a
  rcases a with i | j
  · rfl
  · rfl

variable (k) in
/-- **The augmented slice** `Ψ(z, u) = Φ(g + ∑ zᵢ kᵢ + hor_g(u))`. -/
noncomputable def augSlice (p : (ι → ℝ) × 𝕍) : 𝕍 :=
  responseOf hS ν (sliceFun g (augDir hS ν hg k) (augCoeffL S ν ι p))

/-- The augmented slice is `C^∞`. -/
theorem contDiff_augSlice : ContDiff ℝ ∞ (augSlice hS ν hg k) :=
  (contDiff_responseOf_slice hS ν hg (bdd_augDir hS ν hg hk)).comp (augCoeffL S ν ι).contDiff

omit hk in
theorem sliceFun_zero' : sliceFun g (augDir hS ν hg k) 0 = g := by
  funext x
  simp [sliceFun]

omit hk in
theorem augSlice_zero : augSlice hS ν hg k ((0 : ι → ℝ), (0 : 𝕍)) = responseOf hS ν g := by
  unfold augSlice
  rw [Prod.mk_zero_zero, map_zero, sliceFun_zero' hS ν hg]

/-- The velocity map `ξ ↦ DΦ_g[⟨ξ, k⟩]` of the slice directions, as a continuous linear map. -/
noncomputable def sliceVelL : (ι → ℝ) →L[ℝ] 𝕍 :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (responseVel hS ν hg (hk i))

theorem sliceVelL_apply (ξ : ι → ℝ) :
    sliceVelL hS ν hg hk ξ = responseVel hS ν hg (bdd_dirLoss hk ξ) := by
  rw [responseVel_dirLoss hS ν hg hk ξ]
  simp [sliceVelL]

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk in
theorem eq_sum_single_aug [DecidableEq ι] (v : ι ⊕ Fin n → ℝ) :
    v = ∑ a, v a • (Pi.single a 1 : ι ⊕ Fin n → ℝ) := by
  funext b
  simp [Finset.sum_apply, Pi.single_apply]

/-- **The derivative of the augmented slice at the base**: `DΨ(0,0)[ξ, w] = DΦ_g[⟨ξ,k⟩] + w`. -/
theorem fderiv_augSlice_zero (ξ : ι → ℝ) (w : 𝕍) :
    fderiv ℝ (augSlice hS ν hg k) ((0 : ι → ℝ), (0 : 𝕍)) (ξ, w) = sliceVelL hS ν hg hk ξ + w := by
  classical
  have hF := ((contDiff_responseOf_slice hS ν hg (bdd_augDir hS ν hg hk)).differentiable
    (by simp)).differentiableAt (x := augCoeffL S ν ι ((0 : ι → ℝ), (0 : 𝕍))) |>.hasFDerivAt
  have hcomp := hF.comp ((0 : ι → ℝ), (0 : 𝕍)) (augCoeffL S ν ι).hasFDerivAt
  have hΨ : HasFDerivAt (augSlice hS ν hg k) _ ((0 : ι → ℝ), (0 : 𝕍)) := hcomp
  rw [hΨ.fderiv, ContinuousLinearMap.comp_apply, Prod.mk_zero_zero, map_zero, augCoeffL_apply]
  rw [eq_sum_single_aug ν (Sum.elim ξ ((wBasis S ν).equivFun w)), map_sum]
  simp only [map_smul, fderiv_slice_single hS ν hg (bdd_augDir hS ν hg hk) 0]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 1
  · rw [sliceVelL_apply, responseVel_dirLoss hS ν hg hk ξ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    exact responseVel_congr hS ν _ _ hg (hk i) (sliceFun_zero' hS ν hg (k := k)) rfl
  · conv_rhs => rw [← (wBasis S ν).sum_equivFun w]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    exact (responseVel_congr hS ν _ _ hg (bdd_horizontalLift hS ν hg _)
      (sliceFun_zero' hS ν hg (k := k)) rfl).trans (responseVel_horizontalLift hS ν hg _)

variable (k) in
/-- The chart `Ξ(z, u) = (z, Ψ(z, u))`. -/
noncomputable def augChart (p : (ι → ℝ) × 𝕍) : (ι → ℝ) × 𝕍 := (p.1, augSlice hS ν hg k p)

theorem contDiff_augChart : ContDiff ℝ ∞ (augChart hS ν hg k) :=
  contDiff_fst.prodMk (contDiff_augSlice hS ν hg hk)

/-- The derivative of the chart at the base, `(ξ, w) ↦ (ξ, DΦ_g[⟨ξ,k⟩] + w)`. -/
noncomputable def augDerivL : ((ι → ℝ) × 𝕍) →L[ℝ] ((ι → ℝ) × 𝕍) :=
  (ContinuousLinearMap.fst ℝ (ι → ℝ) 𝕍).prod
    ((sliceVelL hS ν hg hk).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) 𝕍) +
      ContinuousLinearMap.snd ℝ (ι → ℝ) 𝕍)

/-- Its inverse `(ξ, η) ↦ (ξ, η − DΦ_g[⟨ξ,k⟩])`. -/
noncomputable def augDerivInvL : ((ι → ℝ) × 𝕍) →L[ℝ] ((ι → ℝ) × 𝕍) :=
  (ContinuousLinearMap.fst ℝ (ι → ℝ) 𝕍).prod
    (ContinuousLinearMap.snd ℝ (ι → ℝ) 𝕍 -
      (sliceVelL hS ν hg hk).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) 𝕍))

theorem augDerivL_apply (p : (ι → ℝ) × 𝕍) :
    augDerivL hS ν hg hk p = (p.1, sliceVelL hS ν hg hk p.1 + p.2) := rfl

theorem augDerivInvL_apply (p : (ι → ℝ) × 𝕍) :
    augDerivInvL hS ν hg hk p = (p.1, p.2 - sliceVelL hS ν hg hk p.1) := rfl

/-- **The derivative of the chart is invertible.** -/
noncomputable def augDerivEquiv : ((ι → ℝ) × 𝕍) ≃L[ℝ] ((ι → ℝ) × 𝕍) :=
  ContinuousLinearEquiv.equivOfInverse (augDerivL hS ν hg hk) (augDerivInvL hS ν hg hk)
    (fun p ↦ by
      rw [augDerivL_apply, augDerivInvL_apply]
      simp)
    (fun p ↦ by
      rw [augDerivInvL_apply, augDerivL_apply]
      simp)

theorem coe_augDerivEquiv :
    (augDerivEquiv hS ν hg hk : ((ι → ℝ) × 𝕍) →L[ℝ] ((ι → ℝ) × 𝕍)) = augDerivL hS ν hg hk := rfl

/-- **The chart has an invertible strict derivative at the base.** -/
theorem hasStrictFDerivAt_augChart :
    HasStrictFDerivAt (augChart hS ν hg k)
      (augDerivEquiv hS ν hg hk : ((ι → ℝ) × 𝕍) →L[ℝ] ((ι → ℝ) × 𝕍)) ((0 : ι → ℝ), (0 : 𝕍)) := by
  have h := hasStrictFDerivAt_fst.prodMk
    ((contDiff_augSlice hS ν hg hk).contDiffAt.hasStrictFDerivAt (x := ((0 : ι → ℝ), (0 : 𝕍)))
      (by simp))
  rw [coe_augDerivEquiv]
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p ↦ ?_
  rw [augDerivL_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    fderiv_augSlice_zero hS ν hg hk]

/-- **The fibre section**: the `u`-component of the local inverse of the chart, so that
`Ψ(z, σ(z, θ)) = θ` near `(0, Φ(g))`. -/
noncomputable def fibreSection : (ι → ℝ) × 𝕍 → 𝕍 := fun q ↦
  ((hasStrictFDerivAt_augChart hS ν hg hk).localInverse (augChart hS ν hg k) _ _ q).2

omit hk in
theorem augChart_zero :
    augChart hS ν hg k ((0 : ι → ℝ), (0 : 𝕍)) = ((0 : ι → ℝ), responseOf hS ν g) := by
  rw [augChart, augSlice_zero hS ν hg]

/-- **Local right inverse**: `Ψ(z, σ(z, θ)) = θ` for `(z, θ)` near `(0, Φ(g))`. -/
theorem eventually_augSlice_fibreSection :
    ∀ᶠ q : (ι → ℝ) × 𝕍 in 𝓝 ((0 : ι → ℝ), responseOf hS ν g),
      augSlice hS ν hg k (q.1, fibreSection hS ν hg hk q) = q.2 := by
  have h := (hasStrictFDerivAt_augChart hS ν hg hk).eventually_right_inverse
  rw [augChart_zero] at h
  filter_upwards [h] with q hq
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  simp only [augChart] at h1 h2
  rw [← h2]
  unfold fibreSection
  rw [← h1]

/-- **Local left inverse**: `σ(z, Ψ(z, u)) = u` for `(z, u)` near `(0, 0)`. -/
theorem eventually_fibreSection_augSlice :
    ∀ᶠ p : (ι → ℝ) × 𝕍 in 𝓝 ((0 : ι → ℝ), (0 : 𝕍)),
      fibreSection hS ν hg hk (p.1, augSlice hS ν hg k p) = p.2 := by
  filter_upwards [(hasStrictFDerivAt_augChart hS ν hg hk).eventually_left_inverse] with p hp
  unfold fibreSection
  change ((hasStrictFDerivAt_augChart hS ν hg hk).localInverse (augChart hS ν hg k) _ _
    (augChart hS ν hg k p)).2 = p.2
  rw [hp]

theorem fibreSection_base : fibreSection hS ν hg hk ((0 : ι → ℝ), responseOf hS ν g) = 0 := by
  have h := (hasStrictFDerivAt_augChart hS ν hg hk).localInverse_apply_image
  rw [augChart_zero] at h
  unfold fibreSection
  rw [h]

/-- **The fibre section is `C^∞`** at the base. -/
theorem contDiffAt_fibreSection :
    ContDiffAt ℝ ∞ (fibreSection hS ν hg hk) ((0 : ι → ℝ), responseOf hS ν g) := by
  have h := (contDiff_augChart hS ν hg hk).contDiffAt.to_localInverse
    (hasStrictFDerivAt_augChart hS ν hg hk).hasFDerivAt (by simp)
  rw [augChart_zero] at h
  exact contDiffAt_snd.comp _ h

/-- **The fibre section has a strict derivative** `(ξ, η) ↦ η − DΦ_g[⟨ξ,k⟩]` at the base. -/
theorem hasStrictFDerivAt_fibreSection :
    HasStrictFDerivAt (fibreSection hS ν hg hk)
      ((ContinuousLinearMap.snd ℝ (ι → ℝ) 𝕍).comp
        (augDerivInvL hS ν hg hk)) ((0 : ι → ℝ), responseOf hS ν g) := by
  have h := (hasStrictFDerivAt_augChart hS ν hg hk).to_localInverse
  rw [augChart_zero] at h
  have h2 := hasStrictFDerivAt_snd.comp ((0 : ι → ℝ), responseOf hS ν g) h
  exact h2

end Augmented

end Laplace.Multi
