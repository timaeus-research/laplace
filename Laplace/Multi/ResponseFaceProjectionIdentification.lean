/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFacewiseRegression

/-!
# The tangential projection is the Euclidean orthogonal projection

The tangential projection `faceProj` of `ResponseFacewiseRegression` was defined as the
`Σ_q`-Riesz projection onto the face direction space. On the support geometry of a probability
vector it coincides with the Euclidean orthogonal projection: if `z ∈ V` and `u − z` is
`dotJ`-orthogonal to `V`, then `⟨u − z, S⟩` is constant on the support of `q`, so `Σ_q(u − z, ·)`
vanishes on `V` and `z` satisfies the defining equations of `faceProj`
(`faceProj_eq_of_dotJ_eq_zero`); at a boundary mean the hypothesis is the definition of the face
direction space (`faceProj_faceSpan_eq_of_dotJ_eq_zero`). The identification is special to the
covariance support geometry: it fails for an arbitrary positive definite restriction of a
bilinear form to an arbitrary subspace.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Identification

variable {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
  {J : Type*} [Fintype J] {S : J → X → ℝ} {q : X → ℝ} (hq : q ∈ stdSimplex ℝ X)
include hq

/-- A function constant on the support of `q` has zero covariance with every function. -/
theorem lawCov_vecMeasure_eq_zero_of_const_on_support {f : X → ℝ} {c : ℝ}
    (hf : ∀ x, 0 < q x → f x = c) (g : X → ℝ) : lawCov (vecMeasure q) f g = 0 := by
  unfold lawCov
  rw [integral_vecMeasure hq.1, integral_vecMeasure hq.1, integral_vecMeasure hq.1]
  have e1 : ∀ x, q x * (f x * g x) = c * (q x * g x) := fun x ↦ by
    by_cases hx : 0 < q x
    · rw [hf x hx]
      ring
    · have : q x = 0 := le_antisymm (not_lt.1 hx) (hq.1 x)
      rw [this]
      ring
  have e2 : ∀ x, q x * f x = c * q x := fun x ↦ by
    by_cases hx : 0 < q x
    · rw [hf x hx]
      ring
    · have : q x = 0 := le_antisymm (not_lt.1 hx) (hq.1 x)
      rw [this]
      ring
  simp_rw [e1, e2]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hq.2]
  ring

variable {V : Submodule ℝ (J → ℝ)}

/-- **The tangential projection is the Euclidean orthogonal projection** whenever the feature
differences on the support of `q` lie in `V`: if `z ∈ V` and `⟨u − z, w⟩ = 0` for all `w ∈ V`,
then `faceProj u = z`. -/
theorem faceProj_eq_of_dotJ_eq_zero (hpd : PosDefOn S hq V)
    (hspan : ∀ x y, 0 < q x → 0 < q y → statPoint S x - statPoint S y ∈ V) {u : J → ℝ} {z : V}
    (hz : ∀ w ∈ V, dotJ (u - (z : J → ℝ)) w = 0) : faceProj hq hpd u = z := by
  -- `Σ_q(u − z, w) = 0` on `V`
  have hcov : ∀ w ∈ V, covForm S hq (u - (z : J → ℝ)) w = 0 := by
    intro w hw
    rw [covForm_apply]
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, 0 < q x₀ := by
      by_contra hne
      push Not at hne
      have : ∑ x, q x = 0 := Finset.sum_eq_zero fun x _ ↦ le_antisymm (hne x) (hq.1 x)
      rw [hq.2] at this
      exact one_ne_zero this
    refine lawCov_vecMeasure_eq_zero_of_const_on_support hq
      (c := dirLoss S (u - (z : J → ℝ)) x₀) (fun x hx ↦ ?_) _
    rw [dirLoss_eq_dotJ_statPoint, dirLoss_eq_dotJ_statPoint, ← sub_eq_zero,
      ← (isLinearMap_dotJ (u - (z : J → ℝ))).map_sub]
    exact hz _ (hspan _ _ hx hx₀)
  -- uniqueness of the Riesz projection
  have hd : ∀ w : V, covForm S hq ((faceProj hq hpd u : J → ℝ) - z) w = 0 := fun w ↦ by
    rw [map_sub, LinearMap.sub_apply, covForm_faceProj]
    have := hcov w w.2
    rw [map_sub, LinearMap.sub_apply] at this
    linarith
  by_contra hne
  have hne' : (faceProj hq hpd u : J → ℝ) - z ≠ 0 := by
    intro h
    exact hne (Subtype.ext (sub_eq_zero.1 h))
  have hmem : (faceProj hq hpd u : J → ℝ) - z ∈ V := V.sub_mem (faceProj hq hpd u).2 z.2
  have := hpd _ hmem hne'
  rw [hd ⟨_, hmem⟩] at this
  exact lt_irrefl _ this

end Identification

section Boundary

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- **At a boundary mean the tangential projection is the Euclidean orthogonal projection onto
the face direction space.** -/
theorem faceProj_faceSpan_eq_of_dotJ_eq_zero {M : J → ℝ} (hM : M ∈ hull) {u : J → ℝ}
    {z : faceSpan S hS ν M} (hz : ∀ w ∈ faceSpan S hS ν M, dotJ (u - (z : J → ℝ)) w = 0) :
    faceProj (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM) (posDefOn_faceSpan hS ν hν hM) u =
      z :=
  faceProj_eq_of_dotJ_eq_zero _ _ (fun x y hx hy ↦ by
    rw [← vsub_eq_sub]
    exact vsub_mem_vectorSpan ℝ (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)) hz

end Boundary

end Laplace.Multi
