/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicSusceptibilityGeneralH

/-!
# Third connected cumulant of the anharmonic Gibbs measure

The third connected cumulant of the perturbation observable `u = -(t x)` is the
second derivative of the perturbed mean `M(h) = ⟨u⟩_h = G_1(h)/G_0(h)` at
`h = 0`:
\[
  \kappa_3 = \frac{\partial^2}{\partial h^2}\Big|_{0}\langle u\rangle_h
    = \frac{G_3(0)G_0(0)^2 - 3G_1(0)G_2(0)G_0(0) + 2G_1(0)^3}{G_0(0)^3}
    = \langle u^3\rangle_0 - 3\langle u^2\rangle_0\langle u\rangle_0
      + 2\langle u\rangle_0^3 .
\]
The mean's first derivative is the susceptibility
`S(h) = (G_2(h)G_0(h)-G_1(h)^2)/G_0(h)^2` (general-`h` susceptibility tide), so
`deriv M = S` near `0`; differentiating `S` once more — a compound quotient
rule on the partition derivatives — gives `κ_3`.
-/

open MeasureTheory Topology

namespace Laplace.OneD

/-- **Third connected cumulant** of `u = -(t x)`: the second `h`-derivative of
the perturbed mean `G_1(h)/G_0(h)` at `0`. -/
theorem anharmonic_third_cumulant
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv 2
        (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
          / weightedPartition lam alpha gamma t 0 h) 0
      = (weightedPartition lam alpha gamma t 3 0
            * weightedPartition lam alpha gamma t 0 0 ^ 2
          - 3 * weightedPartition lam alpha gamma t 1 0
            * weightedPartition lam alpha gamma t 2 0
            * weightedPartition lam alpha gamma t 0 0
          + 2 * weightedPartition lam alpha gamma t 1 0 ^ 3)
        / weightedPartition lam alpha gamma t 0 0 ^ 3 := by
  have hne : weightedPartition lam alpha gamma t 0 0 ≠ 0 :=
    (weightedPartition_zero_zero_pos hlam hgamma hdisc ht).ne'
  -- Pointwise partition derivatives at 0.
  have hG0 := weightedPartition_hasDerivAt 0 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hG1 := weightedPartition_hasDerivAt 1 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hG2 := weightedPartition_hasDerivAt 2 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  -- Susceptibility `S = (G_2·G_0 − G_1²)/G_0²`; differentiate at 0.
  have hnum :
      HasDerivAt
        (fun h : ℝ => weightedPartition lam alpha gamma t 2 h
            * weightedPartition lam alpha gamma t 0 h
          - weightedPartition lam alpha gamma t 1 h
            * weightedPartition lam alpha gamma t 1 h) _ 0 :=
    (hG2.mul hG0).sub (hG1.mul hG1)
  have hden :
      HasDerivAt (fun h : ℝ => weightedPartition lam alpha gamma t 0 h ^ 2) _ 0 :=
    hG0.pow 2
  have hden_ne : weightedPartition lam alpha gamma t 0 0 ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hS :
      HasDerivAt
        (fun h : ℝ => (weightedPartition lam alpha gamma t 2 h
              * weightedPartition lam alpha gamma t 0 h
            - weightedPartition lam alpha gamma t 1 h
              * weightedPartition lam alpha gamma t 1 h)
          / weightedPartition lam alpha gamma t 0 h ^ 2)
        ((weightedPartition lam alpha gamma t 3 0
              * weightedPartition lam alpha gamma t 0 0 ^ 2
            - 3 * weightedPartition lam alpha gamma t 1 0
              * weightedPartition lam alpha gamma t 2 0
              * weightedPartition lam alpha gamma t 0 0
            + 2 * weightedPartition lam alpha gamma t 1 0 ^ 3)
          / weightedPartition lam alpha gamma t 0 0 ^ 3) 0 := by
    convert hnum.div hden hden_ne using 1
    field_simp
    ring
  -- `deriv M = S` on `ball 0 1`, hence eventually at 0.
  have hev :
      deriv (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
          / weightedPartition lam alpha gamma t 0 h)
        =ᶠ[𝓝 0]
        (fun h : ℝ => (weightedPartition lam alpha gamma t 2 h
              * weightedPartition lam alpha gamma t 0 h
            - weightedPartition lam alpha gamma t 1 h
              * weightedPartition lam alpha gamma t 1 h)
          / weightedPartition lam alpha gamma t 0 h ^ 2) := by
    have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_self]; exact one_pos)
    filter_upwards [hball] with h₀ hmem
    have hh : |h₀| < 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
      exact hmem
    exact (anharmonic_mean_hasDerivAt_general hlam hgamma hdisc ht hh).deriv
  -- Chain: iteratedDeriv 2 M 0 = deriv (deriv M) 0 = deriv S 0 = κ₃.
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, hS.deriv]

end Laplace.OneD
