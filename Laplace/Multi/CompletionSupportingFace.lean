/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherCompletionMeasure
import Laplace.Multi.DataRayBlocks

/-!
# Completion laws concentrate on the supporting faces of their mean

If `⟨u,S⟩ ≤ β` `ν`-a.e. and the extended mean of a completion point `x` lies on the supporting
hyperplane `⟨u,·⟩ = β`, then the law of `x` is concentrated on the face event `{⟨u,S⟩ = β}`: the
nonnegative slack `β − ⟨u,S⟩` has zero integral against `Ψ̄(x)²`, hence vanishes a.e. for the law.
In particular every boundary extended mean lies on a face charged by `ν`.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The law of a completion point has mean `meanExt` against linear statistics. -/
theorem integral_dirLoss_completionLaw (x : FisherCompletion hS ν) (u : J → ℝ) :
    ∫ y, dirLoss S u y ∂completionLaw hS ν x = dotJ u (meanExt hS ν x) := by
  rw [integral_dirLoss_eq_dotJ u _ hS]
  congr 1
  funext i
  exact integral_completionLaw_eq_meanExt hS ν x i

/-- **A completion law is concentrated on every exposed face containing its mean.** -/
theorem completionLaw_face_eq_one (x : FisherCompletion hS ν) {u : J → ℝ} {β : ℝ}
    (hβ : ∀ᵐ y ∂ν, dirLoss S u y ≤ β) (hM : dotJ u (meanExt hS ν x) = β) :
    completionLaw hS ν x {y | dirLoss S u y = β} = 1 := by
  have hac : completionLaw hS ν x ≪ ν := completionLaw_absolutelyContinuous hS ν x
  have hβQ : ∀ᵐ y ∂completionLaw hS ν x, dirLoss S u y ≤ β := hac.ae_le hβ
  have hint : Integrable (fun y ↦ β - dirLoss S u y) (completionLaw hS ν x) :=
    integrable_of_bdd_prob _ ((Bdd.const β).sub (bdd_dirLoss hS u))
  have h0 : ∫ y, (β - dirLoss S u y) ∂completionLaw hS ν x = 0 := by
    rw [integral_sub (integrable_const _) (integrable_of_bdd_prob _ (bdd_dirLoss hS u)),
      integral_const, probReal_univ, one_smul, integral_dirLoss_completionLaw hS ν x u, hM,
      sub_self]
  have hae : (fun y ↦ β - dirLoss S u y) =ᵐ[completionLaw hS ν x] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (hβQ.mono fun y hy ↦ by
      rw [Pi.zero_apply]
      exact sub_nonneg.2 hy) hint).1 h0
  have hae' : ∀ᵐ y ∂completionLaw hS ν x, dirLoss S u y = β := hae.mono fun y hy ↦ by
    simp only [Pi.zero_apply] at hy
    exact (sub_eq_zero.1 hy).symm
  rw [← prob_compl_eq_zero_iff (measurableSet_faceFibre hS u β)]
  rw [ae_iff] at hae'
  exact hae'

/-- **Boundary extended means lie on faces charged by `ν`.** -/
theorem faceFibre_pos_of_meanExt (x : FisherCompletion hS ν) {u : J → ℝ} {β : ℝ}
    (hβ : ∀ᵐ y ∂ν, dirLoss S u y ≤ β) (hM : dotJ u (meanExt hS ν x) = β) :
    0 < ν {y | dirLoss S u y = β} := by
  refine pos_iff_ne_zero.2 fun h ↦ ?_
  have h1 := completionLaw_absolutelyContinuous hS ν x h
  rw [completionLaw_face_eq_one hS ν x hβ hM] at h1
  exact one_ne_zero h1

end Face

end Laplace.Multi
