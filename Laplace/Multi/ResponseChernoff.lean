/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.NormalForm
import Laplace.Multi.LegendreClosure

/-!
# The visible information is the sampling cost of the response

Sampling `n` points from the featureless law `ν`, the probability that the empirical response
`R̄_n` lies on the far side of the response `M` along its own natural parameter `θ(M)` is at most
`e^{−n 𝓘(M)}` (`response_chernoff`): the visible information `𝓘(M) = KL(Q_M ‖ ν)` is the exponential
cost of producing the response `M` from the featureless law. This is the halfspace Chernoff bound
(`halfspace_chernoff`) evaluated at the multiplier direction `−θ(M)`, where the Chernoff exponent
`⟨θ(M), M⟩ − Λ_ν(−θ(M))` coincides with the rate (`toReal_genRate_eq_neg_dotJ_sub_featCgf`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The rate as a Chernoff exponent at its own natural parameter**:
`𝓘(M) = −⟨θ(M), M⟩ − Λ_ν(−θ(M))`. -/
theorem toReal_genRate_eq_neg_dotJ_sub_featCgf {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (genRate ν S M).toReal = -dotJ (θr M : J → ℝ) M - featCgf ν S (-(θr M : J → ℝ)) := by
  have hmean : meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θr M) = M :=
    meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel
  have h := genRate_meanMap_neg hS ν (-(θr M : J → ℝ))
  rw [neg_neg, hmean, dotJ_neg_left] at h
  have h0 := nonneg_klDiv_familyMeasure_featureless hS ν (θr M)
  rw [hmean] at h0
  rw [h, ENNReal.toReal_ofReal h0]

/-- **The visible information is the sampling cost of the response**: for `n` i.i.d. samples from
the featureless law, `P(⟨θ(M), R̄_n⟩ ≤ ⟨θ(M), M⟩) ≤ e^{−n 𝓘(M)}`. -/
theorem response_chernoff {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {n : ℕ} (hn : 0 < n) :
    (Measure.pi fun _ : Fin n ↦ ν).real
        {x | dotJ (θr M : J → ℝ) (empMean S n x) ≤ dotJ (θr M : J → ℝ) M} ≤
      Real.exp (-(n * (genRate ν S M).toReal)) := by
  have h := halfspace_chernoff ν hS (-(θr M : J → ℝ)) (-dotJ (θr M : J → ℝ) M) hn
    (lam := 1) zero_le_one
  have e : {x : Fin n → X | -dotJ (θr M : J → ℝ) M ≤ ∑ i, (-(θr M : J → ℝ)) i * empMean S n x i} =
      {x | dotJ (θr M : J → ℝ) (empMean S n x) ≤ dotJ (θr M : J → ℝ) M} := by
    ext x
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]
    rfl
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  rw [toReal_genRate_eq_neg_dotJ_sub_featCgf hS ν hrel, one_smul, one_mul]

end Laplace.Multi
