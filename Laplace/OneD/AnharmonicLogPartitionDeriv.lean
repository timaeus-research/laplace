/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicMomentNormalisation

/-!
# Cumulant generating function: first derivative of `log Z`

The partition-derivative arc produced the perturbed partition
`Z = weightedPartition … 0` and its `h`-derivatives. The cumulant generating
function is `K(h) = log Z(h)`; its derivatives at `h = 0` are the connected
cumulants of the perturbation observable `u(x) = -(t x)`. This file lands the
first rung:
\[
  K'(0) = \frac{Z'(0)}{Z(0)} = \langle -(t x) \rangle_0,
\]
the unperturbed Gibbs mean of `u`, by `HasDerivAt.log` on the partition's
first derivative (with `Z(0) > 0`). It is the foundation for the higher
connected cumulants $\kappa_2,\kappa_3,\kappa_4$.
-/

open MeasureTheory

namespace Laplace.OneD

/-- `Z(0) = weightedPartition … 0 0` is the unperturbed partition integral. -/
theorem weightedPartition_zero_zero_eq
    {lam alpha gamma t : ℝ} :
    weightedPartition lam alpha gamma t 0 0
      = ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
  unfold weightedPartition
  congr 1
  funext x
  rw [pow_zero, one_mul]
  congr 1
  ring

/-- The unperturbed partition `Z(0)` is strictly positive. -/
theorem weightedPartition_zero_zero_pos
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    0 < weightedPartition lam alpha gamma t 0 0 := by
  rw [weightedPartition_zero_zero_eq]
  exact anharmonic_partition_pos hlam hgamma hdisc ht

/-- **First derivative of the cumulant generating function** `K = log Z` at
`h = 0`: `K'(0) = Z'(0)/Z(0)`, where `Z'(0) = weightedPartition … 1 0`. -/
theorem logPartition_hasDerivAt
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    HasDerivAt (fun h : ℝ => Real.log (weightedPartition lam alpha gamma t 0 h))
      (weightedPartition lam alpha gamma t 1 0
        / weightedPartition lam alpha gamma t 0 0) 0 := by
  have hZ := weightedPartition_hasDerivAt 0 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hne : weightedPartition lam alpha gamma t 0 0 ≠ 0 :=
    (weightedPartition_zero_zero_pos hlam hgamma hdisc ht).ne'
  exact hZ.log hne

/-- **`K'(0)` is the unperturbed Gibbs mean** of the perturbation observable
`-(t x)`: `∂_h log Z |_{h=0} = ⟨ -(t x) ⟩_0`. -/
theorem logPartition_deriv_eq_gibbsExp_mean
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    deriv (fun h : ℝ => Real.log (weightedPartition lam alpha gamma t 0 h)) 0
      = Threepoint.gibbsExp (volume : Measure ℝ)
          (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
          (fun x : ℝ => -(t * x)) := by
  rw [(logPartition_hasDerivAt hlam hgamma hdisc ht).deriv]
  -- `Z'(0)/Z(0) = iteratedDeriv 1 (wP 0) 0 / Z(0) = gibbsExp … (fun x => (-(t·x))^1)`.
  have hid : weightedPartition lam alpha gamma t 1 0
      = iteratedDeriv 1 (weightedPartition lam alpha gamma t 0) 0 :=
    (iteratedDeriv_weightedPartition_zero hlam hgamma hdisc ht 1 (by norm_num)).symm
  rw [hid, iteratedDeriv_partition_div_eq_gibbsExp 1 hlam hgamma hdisc ht]
  -- `(fun x => (-(t·x))^1) = (fun x => -(t·x))`.
  congr 1
  funext x
  rw [pow_one]

end Laplace.OneD
