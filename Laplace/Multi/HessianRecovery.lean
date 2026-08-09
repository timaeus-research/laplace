/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.HessianMoments

/-!
# Pairwise Hessian recovery

Stage H6, closing the multivariate H-recovery milestone: two losses
(each carrying the domain package) whose posterior covariance data
agree to `o(q²)` have the same Hessian at the minimum. Uniqueness of
limits identifies the inverse Hessians entrywise, and
positive-definiteness makes inversion injective. This is the
multivariate analogue of the one-dimensional `base_recovery`.
-/

open Real Matrix Filter Topology

namespace Laplace.Multi

namespace LocalLaplaceDomain

variable {d : ℕ}

/-- The posterior covariance form of a domain package at scale `q`. -/
noncomputable def covariance {L : EuclidD d → ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ} (A : LocalLaplaceDomain L H)
    (i j : Fin d) (q : ℝ) : ℝ :=
  A.posteriorIntegral (fun w ↦ w i * w j) q /
      A.posteriorIntegral (fun _ ↦ 1) q -
    A.posteriorIntegral (fun w ↦ w i) q /
        A.posteriorIntegral (fun _ ↦ 1) q *
      (A.posteriorIntegral (fun w ↦ w j) q /
        A.posteriorIntegral (fun _ ↦ 1) q)

/-- The H5 limit in covariance language. -/
theorem tendsto_covariance {L : EuclidD d → ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ} (A : LocalLaplaceDomain L H)
    (i j : Fin d) :
    Tendsto (fun q : ℝ ↦ A.covariance i j q / q ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (H⁻¹ i j)) :=
  A.tendsto_normalized_covariance i j

/-- **Entrywise recovery**: covariance data agreeing to `o(q²)`
identify the inverse Hessian entries. -/
theorem hessian_inv_entry_recovery {L₁ L₂ : EuclidD d → ℝ}
    {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A₁ : LocalLaplaceDomain L₁ H₁) (A₂ : LocalLaplaceDomain L₂ H₂)
    (i j : Fin d)
    (hdata : (fun q : ℝ ↦ A₁.covariance i j q - A₂.covariance i j q)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ 2) :
    H₁⁻¹ i j = H₂⁻¹ i j := by
  have h1 := A₁.tendsto_covariance i j
  have h2 := A₂.tendsto_covariance i j
  have hdiff : Tendsto
      (fun q : ℝ ↦ A₁.covariance i j q / q ^ 2 -
        A₂.covariance i j q / q ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (H₁⁻¹ i j - H₂⁻¹ i j)) := h1.sub h2
  have hzero : Tendsto
      (fun q : ℝ ↦ A₁.covariance i j q / q ^ 2 -
        A₂.covariance i j q / q ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hdata.tendsto_div_nhds_zero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [sub_div]
  have := tendsto_nhds_unique hdiff hzero
  linarith [this]

/-- **Pairwise Hessian recovery** (germbij multivariate H6): two
losses whose covariance data agree to `o(q²)` at every coordinate
pair have the same Hessian. -/
theorem hessian_recovery {L₁ L₂ : EuclidD d → ℝ}
    {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A₁ : LocalLaplaceDomain L₁ H₁) (A₂ : LocalLaplaceDomain L₂ H₂)
    (hdata : ∀ i j : Fin d,
      (fun q : ℝ ↦ A₁.covariance i j q - A₂.covariance i j q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ 2) :
    H₁ = H₂ := by
  have hinv : H₁⁻¹ = H₂⁻¹ := by
    ext i j
    exact hessian_inv_entry_recovery A₁ A₂ i j (hdata i j)
  have h1 : IsUnit H₁.det :=
    isUnit_iff_ne_zero.mpr A₁.hH_posDef.det_pos.ne'
  have h2 : IsUnit H₂.det :=
    isUnit_iff_ne_zero.mpr A₂.hH_posDef.det_pos.ne'
  calc H₁ = H₁⁻¹⁻¹ := (Matrix.nonsing_inv_nonsing_inv H₁ h1).symm
    _ = H₂⁻¹⁻¹ := by rw [hinv]
    _ = H₂ := Matrix.nonsing_inv_nonsing_inv H₂ h2

end LocalLaplaceDomain

end Laplace.Multi
