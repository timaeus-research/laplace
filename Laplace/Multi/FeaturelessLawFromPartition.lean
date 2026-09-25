/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TauberianVariance
import Laplace.Multi.ThermoLengthFromBase

/-!
# The RLCT is the featureless-length coefficient

Combining the Tauberian variance theorem with the Cesàro lemma of `ThermoLengthFromBase`: if the
partition function satisfies Watanabe's asymptotic `Z(u) ~ C u^{-λ} (log u)^k`, then the
thermodynamic length of the featureless line from any base temperature `u₀ > 0` satisfies

  `(∫_{u₀}^t √Var_u(L) du) / log t → √λ`   (`featureless_law_of_partition_asymptotic`).

No derivative control of `Z` and no Laplace-expansion hypotheses are needed: the free-energy
asymptotic alone determines the leading geometry of the map from the featureless distribution to the
data distribution.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **The featureless law from the partition-function asymptotic.** -/
theorem featureless_law_of_partition_asymptotic {π L : X → ℝ} (hπm : Measurable π)
    (hπ : ∀ x, 0 ≤ π x) (hL : Measurable L) (hL0 : ∀ x, 0 ≤ L x)
    (hint : ∀ u > 0, ∀ k ≤ 2, Integrable (fun x ↦ L x ^ k * Real.exp (-(u * L x)) * π x) μ)
    (hZ : ∀ u > 0, 0 < priorZ μ π L u) {lam C : ℝ} (k : ℕ) (hlam : 0 < lam) (hC : 0 < C)
    (hasym : Tendsto (fun u ↦ priorZ μ π L u / (u ^ (-lam) * Real.log u ^ k)) atTop (𝓝 C))
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    Tendsto (fun t ↦ (∫ u in u₀..t, Real.sqrt (priorCov μ π L L L u)) / Real.log t) atTop
      (𝓝 (Real.sqrt lam)) := by
  have h0 : Integrable (fun x ↦ Real.exp (-(u₀ * L x)) * π x) μ :=
    (hint u₀ hu₀ 0 (by norm_num)).congr (Filter.Eventually.of_forall fun x ↦ by simp)
  have h1 : Integrable (fun x ↦ L x * (Real.exp (-(u₀ * L x)) * π x)) μ :=
    (hint u₀ hu₀ 1 (by norm_num)).congr (Filter.Eventually.of_forall fun x ↦ by simp [mul_assoc])
  have h2 : Integrable (fun x ↦ L x * L x * (Real.exp (-(u₀ * L x)) * π x)) μ :=
    (hint u₀ hu₀ 2 (by norm_num)).congr (Filter.Eventually.of_forall fun x ↦ by ring)
  have hcont := continuousOn_priorCov_self_Ici hL hL0 hπm hπ
    (fun u hu ↦ (hZ u (lt_of_lt_of_le hu₀ hu)).ne') h0 h1 h2
  exact thermoLength_from_div_log_tendsto hcont
    (tendsto_sq_mul_priorCov_of_partition_asymptotic hπm hπ hL hL0 hint hZ k hlam hC hasym)

end Laplace.Multi
