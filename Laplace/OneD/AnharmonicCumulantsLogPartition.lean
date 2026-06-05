/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicFourthCumulant

/-!
# Cumulants as derivatives of the log-partition (cumulant generating function)

The connected cumulants `κ_n` of `u = -(t x)` were proved as derivatives of the
perturbed mean `M(h) = G_1(h)/G_0(h)` (`κ_n = ∂_h^{n-1} M|_0`). This file ties
them to the genuine cumulant generating function `K(h) = log Z(h)` with
`Z = G_0`: since `deriv K = M` near `0`,
\[
  \mathrm{iteratedDeriv}\,(n+1)\,K\,0 = \mathrm{iteratedDeriv}\,n\,M\,0,
\]
so `κ_2, κ_3, κ_4` are the second, third and fourth derivatives of `log Z` at
`0` — the standard definition of the connected cumulants. This closes the arc's
narrative loop with `logPartition_hasDerivAt` (the CGF's first derivative).
-/

open Topology

namespace Laplace.OneD

/-- General-`h` first derivative of the cumulant generating function
`K = log Z`: `K'(h₀) = G_1(h₀)/G_0(h₀) = ⟨u⟩_{h₀}` for `|h₀| < 1`. -/
theorem logPartition_hasDerivAt_general
    {lam alpha gamma t : ℝ} {h₀ : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) (hh₀ : |h₀| < 1) :
    HasDerivAt (fun h : ℝ => Real.log (weightedPartition lam alpha gamma t 0 h))
      (weightedPartition lam alpha gamma t 1 h₀
        / weightedPartition lam alpha gamma t 0 h₀) h₀ := by
  have hZ := weightedPartition_hasDerivAt 0 hlam hgamma hdisc ht (h₀ := h₀) hh₀
  have hne : weightedPartition lam alpha gamma t 0 h₀ ≠ 0 :=
    (weightedPartition_zero_pos hlam hgamma hdisc ht hh₀).ne'
  exact hZ.log hne

/-- `deriv (log Z) = M` (the mean) on a neighbourhood of `0`. -/
theorem deriv_logPartition_eventuallyEq
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    deriv (fun h : ℝ => Real.log (weightedPartition lam alpha gamma t 0 h))
      =ᶠ[𝓝 0]
      (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
        / weightedPartition lam alpha gamma t 0 h) := by
  have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_self]; exact one_pos)
  filter_upwards [hball] with h₀ hmem
  have hh : |h₀| < 1 := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem; exact hmem
  exact (logPartition_hasDerivAt_general hlam hgamma hdisc ht hh).deriv

/-- **Cumulant ladder via the generating function.** For every `n`, the
`(n+1)`-th derivative of `log Z` at `0` equals the `n`-th derivative of the
mean `M = G_1/G_0` at `0`. -/
theorem iteratedDeriv_logPartition_succ
    {lam alpha gamma t : ℝ} (n : ℕ)
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv (n + 1)
        (fun h : ℝ => Real.log (weightedPartition lam alpha gamma t 0 h)) 0
      = iteratedDeriv n
        (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
          / weightedPartition lam alpha gamma t 0 h) 0 := by
  rw [iteratedDeriv_succ']
  exact Filter.EventuallyEq.iteratedDeriv_eq n
    (deriv_logPartition_eventuallyEq hlam hgamma hdisc ht)

/-- **Second cumulant as `∂² log Z`.** `κ₂ = iteratedDeriv 2 (log Z) 0`. -/
theorem logPartition_secondDeriv_eq_kappa2
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv 2
        (fun h : ℝ => Real.log (weightedPartition lam alpha gamma t 0 h)) 0
      = (weightedPartition lam alpha gamma t 2 0
            * weightedPartition lam alpha gamma t 0 0
          - weightedPartition lam alpha gamma t 1 0
            * weightedPartition lam alpha gamma t 1 0)
        / weightedPartition lam alpha gamma t 0 0 ^ 2 := by
  rw [iteratedDeriv_logPartition_succ 1 hlam hgamma hdisc ht, iteratedDeriv_one]
  exact (anharmonic_mean_hasDerivAt hlam hgamma hdisc ht).deriv

/-- **Third cumulant as `∂³ log Z`.** `κ₃ = iteratedDeriv 3 (log Z) 0`. -/
theorem logPartition_thirdDeriv_eq_kappa3
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv 3
        (fun h : ℝ => Real.log (weightedPartition lam alpha gamma t 0 h)) 0
      = (weightedPartition lam alpha gamma t 3 0
            * weightedPartition lam alpha gamma t 0 0 ^ 2
          - 3 * weightedPartition lam alpha gamma t 1 0
            * weightedPartition lam alpha gamma t 2 0
            * weightedPartition lam alpha gamma t 0 0
          + 2 * weightedPartition lam alpha gamma t 1 0 ^ 3)
        / weightedPartition lam alpha gamma t 0 0 ^ 3 := by
  rw [iteratedDeriv_logPartition_succ 2 hlam hgamma hdisc ht]
  exact anharmonic_third_cumulant hlam hgamma hdisc ht

/-- **Fourth cumulant as `∂⁴ log Z`** (the flow-equation identity expressed
through the cumulant generating function). `κ₄ = iteratedDeriv 4 (log Z) 0`. -/
theorem logPartition_fourthDeriv_eq_kappa4
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv 4
        (fun h : ℝ => Real.log (weightedPartition lam alpha gamma t 0 h)) 0
      = (weightedPartition lam alpha gamma t 4 0
            * weightedPartition lam alpha gamma t 0 0 ^ 3
          - 4 * weightedPartition lam alpha gamma t 3 0
            * weightedPartition lam alpha gamma t 1 0
            * weightedPartition lam alpha gamma t 0 0 ^ 2
          - 3 * weightedPartition lam alpha gamma t 2 0 ^ 2
            * weightedPartition lam alpha gamma t 0 0 ^ 2
          + 12 * weightedPartition lam alpha gamma t 2 0
            * weightedPartition lam alpha gamma t 1 0 ^ 2
            * weightedPartition lam alpha gamma t 0 0
          - 6 * weightedPartition lam alpha gamma t 1 0 ^ 4)
        / weightedPartition lam alpha gamma t 0 0 ^ 4 := by
  rw [iteratedDeriv_logPartition_succ 3 hlam hgamma hdisc ht]
  exact anharmonic_fourth_cumulant hlam hgamma hdisc ht

end Laplace.OneD
